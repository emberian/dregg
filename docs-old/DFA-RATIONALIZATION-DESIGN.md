# DFA-RATIONALIZATION-DESIGN — what to do with the open DFA loop

**Date:** 2026-05-24. **Status:** design only. Read-only on code; one new
`.md`. **Scope:** decide the future shape of dregg's DFA / pattern-routing
machinery, given that three implementations currently exist
(`wire::dfa_router`, `rbg::routing`, `apps/governed-namespace::routes`),
none of them subsume the others, and the wire-level one is mostly
vestigial.

**Cross-cuts:** `STORAGE-REFLECTIVITY-RBG-DFA-AUDIT.md` (the audit that
named the gap), `SLOT-CAVEATS-DESIGN.md` (the caveat-evaluation seam
this composes with), `APPS-AS-USERSPACE-AUDIT.md` (the userspace gaps
this attempts to close), `DESIGN-captp-integration.md` (CapTP routing).

---

## §0. TL;DR

There are **three** DFA-ish things in the tree, **two** of them are
inadequate, **one** is workspace-excluded and full of stub types, and
the wire-level one is in the right crate but underpowered. The
sustainable answer is **Option B-with-borrowings**: keep
`wire::dfa_router` as the canonical home, lift the regex compiler and
the AIR-trace shape from `rbg::routing` into it, leave the
`DirectoryCell` / `ScopedIntentPool` / `MetaDirectory` cluster as a
*separate* lift into a `dregg-directory` crate, and stop pretending
`apps/governed-namespace::routes` is a DFA. The wire-level router is
the right shape; the bottleneck is its compiler vocabulary and that
nobody reaches for it.

Concretely, this design recommends:

1. **Promote** the `rbg::routing` compiler shape (`Pattern → Nfa →
   Dfa`, intersection, AIR-trace) into `wire::dfa_router` over ~1-2
   weeks. The `GovernedRouter` / `compile_routes` public surface
   stays; the engine gets richer.
2. **Delete** `apps/governed-namespace::routes` (it is a
   `BTreeMap<&str, RouteEntry>` with longest-prefix lookup wearing
   DFA's clothes) and re-host it on the unified
   `wire::dfa_router`. Closes a duplicate-implementation foot-gun.
3. **Lift** `rbg::directory::{DirectoryCell, ScopedIntentPool,
   MetaDirectory}` into a new `dregg-directory` crate. This is a
   separate, larger workstream — it answers the apps-audit Tier-2
   `CommittedMap<K,V>` and the intent-scoping gap. Out of scope for
   this design beyond a roadmap link.
4. **Wire** the unified router into three real call sites that today
   bypass it: (a) `intent::gossip` topic filtering, (b) the
   `app-framework` HTTP path-classification layer
   (`governed-namespace`, `discord-bot`'s slash-command dispatch,
   `subscription`'s endpoints), (c) CapTP gateway dispatch as a
   *coarse* pre-filter in front of the swiss-table fast path.
5. **Cleanly orthogonalize** with slot caveats: DFA classification
   *selects* the route; the route's caveat *gates* the action. Two
   stages, two evaluators, both AIR-bindable.

The strong claim under this design: **DFA dispatch is a userspace
primitive that should be exposed as a starbridge-app authoring
verb**, not an implementation detail of the wire layer. The wire
crate is where the *engine* lives; the *vocabulary* (`Route`,
`Predicate`, `RouteCaveat`) is what authors touch.

---

## §1. Inventory and current state

### 1.1 `wire/src/dfa_router.rs` — the canonical implementation

**LOC:** 699 (with tests). **Public surface:**

- `RouteTarget` enum: `Cell(CellId) | Handler(String) |
  Federation(GroupId) | Drop`. Four destinations.
- `RouteTable { commitment: [u8;32], transitions: Vec<u8>,
  num_states: usize, accept_map: HashMap<u8, RouteTarget> }`. Flat
  transition table, `BLAKE3` commitment, accept map keyed by state.
- `Router::new(table)` + `classify(&[u8]) -> Option<&RouteTarget>`
  / `classify_path(&[u8])`. Runs the DFA over message bytes.
- `compile_routes(&[(&str, RouteTarget)]) -> RouteTable`. The
  *only* compiler: URL-style patterns with literal segments and an
  optional trailing `/*` wildcard. No alternation, no character
  classes, no offset patterns, no intersection.
- `GovernedRouter` (CAS-style atomic table swap with a
  `GovernanceProof { expected_old_commitment, proof_data }`). The
  `proof_data` field is a placeholder — the actual cryptographic
  check is documented as "in production: verify proof.proof_data
  against threshold sig / ZK proof".
- `dispatch_message` / `dispatch_path` helpers returning a
  `DispatchDecision`.

**Internal compiler shape:** a `DfaBuilder` that walks a trie of
path bytes and flattens it to a transition table. State indexes are
`u8`, hard-capped at **255 live states** (the build `assert!`s
this). This makes the engine **unsuitable for any non-trivial
classification grammar** — 50 routes nearly saturate the limit
(the stress test in `tests` uses exactly 50). Comparison-wise,
**`rbg::routing` uses `u32` state IDs** and has no analogous cap.

**Real consumers (grep results):**

| Consumer | Status |
|---|---|
| `teasting/tests/dfa_routing.rs` | tests |
| `teasting/tests/fault_byzantine.rs:344-395` | tests |
| `teasting/src/{mesh_sim,router_sim}.rs` | test harness |
| `preflight/src/checks/routing.rs` | preflight check |
| `wire/src/server.rs` | **not wired in** — server uses postcard `Message` enum dispatch |
| `intent/src/gossip.rs` | **not wired in** — flat broadcast |
| `captp/src/{session,handoff}.rs` | **not wired in** — swiss-table lookup |
| `apps/governed-namespace/src/*.rs` | **does NOT use it** — uses its own `routes::RoutingTable` (a BTreeMap-backed longest-prefix matcher) |

The audit's claim that
`apps/governed-namespace/src/main.rs:1139-1177` is "the one real
production-shaped consumer" of `wire::dfa_router` is **wrong on the
detail and right on the spirit.** Inspecting the file: the test
exercises the app's *own* `routes.rs` module, which independently
implements a `BTreeMap<String, RouteEntry>` with longest-prefix
lookup. The app does not import `dregg_wire::dfa_router`. There is
**no production consumer** of `wire::dfa_router` today.

### 1.2 `apps/governed-namespace/src/routes.rs` — the duplicate

**LOC:** 287. **Public surface:** `RoutingTable {
routes: BTreeMap<String, RouteEntry>, version: u64 }` with
`classify(&str) -> Classification`, `commitment() -> [u8;32]`
(JSON-serialized `BTreeMap` BLAKE3-hashed), `replace_all` for
atomic updates.

**What it is:** a 25-line longest-prefix matcher with a JSON
commitment, *not* a DFA. The module docstring is candid:

> A full NFA→DFA compilation (as in rbg/routing.rs) handles regex
> patterns, character classes, and alternation. For this demo we
> use prefix-match semantics: longest-prefix wins, compiled into a
> sorted trie that acts as a DFA over path segments.

The author chose to write 25 lines of `for (prefix, entry) in
&self.routes { if path.starts_with(prefix) ... }` rather than
import `wire::dfa_router`'s `compile_routes`. The reason isn't
documented but is inferrable: the app's `RouteClass` (`Public |
MembersOnly | AdminOnly | Multisig { threshold } | Custom(String)`)
doesn't fit `wire::dfa_router::RouteTarget`. The semantics differ:
`RouteClass` describes an **access policy** to apply, while
`RouteTarget` describes a **destination** to forward to. They're
*both* "what to do with a classified path," but at different layers
of the stack.

This split — destination-vs-policy — is real, and the unified
design must honor it (see §3).

### 1.3 `rbg/src/routing.rs` — the workspace-excluded implementation

**LOC:** 1346 (with tests). **Public surface:**

- `Dfa { num_states: u32, transitions: Vec<u32>, start, accepting
  }`. `u32` states (no cap), accept *set* (not accept map), explicit
  start state.
- `Pattern` enum: `Word | Range | Bit | AnyByte | Seq | All | Any
  | Offset | Repeat | BytesAt`. **Real regex combinators.**
- Compiler: `Pattern → Nfa → Dfa` via subset construction. NFA has
  byte transitions and epsilon transitions; determinization is
  textbook ε-closure.
- `Pattern::All` is **DFA intersection by product construction** —
  real DFA algebra, not a trie.
- `Classifier`, `PacketSource`, `SourceHandle`, `RouteDecision`,
  `FilterTree { add_filter, revoke, compile_combined }`. The
  capability-secure source-splitting model from Robigalia: a
  source is a capability, splitting it produces two new capability
  references; revocation = remove a filter from the tree, recompile,
  swap.
- `AirTraceRow { step, state, byte, next_state }`,
  `generate_air_trace`, `verify_air_trace`. The DFA execution trace
  shape that maps directly to AIR constraint rows for STARK
  encoding.
- `TopicFilter::{exact_topic, topic_namespace}` for gossip.

**What it doesn't have:** governance binding (no `GovernedRouter`
analog), no `RouteTarget`-style accept map (just an `accepting:
BTreeSet<StateId>`).

**Why it's excluded:** documented in `Cargo.toml:10-12` — edition
2021 vs the workspace's 2024, stub types (`CellId`, `GroupId`
re-declared locally), no in-tree consumers. The README marks it
"experimental, kept excluded until either integrated or removed."

### 1.4 Cross-reference: `rbg/src/directory.rs`

The other half of the `rbg` crate is the `DirectoryCell` /
`ScopedIntentPool` / `MetaDirectory` cluster (1707 LOC). It is
*not* a DFA — it's a versioned capability-gated key-value cell
with hierarchical lookup, scoped gossip topics, and topic
subscription management. **It uses simple `starts_with` matching
internally**, with a comment that says: "Internal pattern matching
(simplified — production would use DFA compilation)." So even the
RBG directory side concedes that a real DFA engine is the right
substrate for the scoped intent pool's pattern matcher.

This connects the two threads: the DFA engine is the natural
*compiler* for the directory's `MatchPattern` (predicates like
"entries with tag X and name prefix Y"), and the directory is the
natural *namespace* in which routes are scoped.

### 1.5 The DFA-in-circuit story

The AIR-side already exists, independently of any of the three
implementations:

- `circuit/src/dsl/circuit.rs:1711-1941` — a DFA-lookup constraint
  the DSL can emit.
- `tests/src/dfa_circuit.rs` — proves correct DFA execution in
  STARK.

The `rbg::routing::generate_air_trace` function emits the exact
trace shape that circuit already verifies. The seam exists; it
just isn't wired into the production router. **Promotion is free
on the AIR side** — the constraint already accepts this row shape.

### 1.6 `intent/src/matcher.rs` and `intent::MatchSpec`

`MatchSpec` (`intent/src/lib.rs:344-360`) is the intent system's
predicate language: `actions`, `resource`, `app_id`, `service`,
`user_id`, `features`, `oauth_provider`, plus a recursive
`compound: Option<Vec<MatchSpec>>` for conjunction. Today the
matcher (`intent/src/matcher.rs`) evaluates these by straight Rust
field comparison — no compilation step, no commitment, no AIR
encoding.

**MatchSpec is a DFA candidate but not a DFA today.** Several
audit notes (the audit's Q4.4 in particular, and the rbg README's
"Could enhance wire protocol routing" mapping) propose compiling
`MatchSpec → wire::dfa_router::RouteTable`. Sketch in §6.

---

## §2. The case for DFA as a userspace primitive

The wire-level DFA router currently has zero production consumers
but five *plausible* ones. Walking each:

### 2.1 Service mesh (route requests to caps by path/tags)

**Shape:** an app exposes capabilities at URL-shaped paths
(`/v1/transfer`, `/admin/freeze`, `/oracle/price/*`); incoming
HTTP / wire messages are classified to a `RouteTarget::Cell` or
`RouteTarget::Handler`.

**DFA fit:** **strong.** This is the textbook case for the wire
DFA — `apps/governed-namespace`'s shape is exactly this, except it
chose to reinvent prefix matching. The vocabulary that's missing
isn't pattern expressivity (URL paths are tame) but the
**destination type**: cells, handlers, federations are too narrow
when an app wants to map a path to "an access policy" (governed
namespace) or "a slash command" (discord-bot) or "an inbox cell
plus a caveat to enforce" (subscription).

**Verdict:** the current API is *almost* a good fit. It needs:

1. A more open `RouteTarget` (or a generic `RouteTarget<T>`) so the
   destination type is app-defined.
2. A `Classification` return type that carries the *remainder* of
   the matched path (which `apps/governed-namespace::routes` calls
   `remainder` and which `wire::dfa_router` discards).

### 2.2 Governance: atomic table swap of "approved capability set"

**Shape:** a constitution binds a route-table commitment; an
amendment is "compute new table, threshold-sign the proof, CAS the
commitment, atomically install the new table."

**DFA fit:** **strong.** `GovernedRouter::update_routes` is exactly
this primitive, modulo the placeholder `proof_data: Vec<u8>`. The
shape is right, the implementation is half. Need: a real
threshold-signature verification in `update_routes` keyed off the
federation's constitution. Federation-aware route updates are
sketched in `FEDERATION-UNIFICATION-DESIGN.md` and would naturally
ride on this.

**Verdict:** **keep as-is, finish the cryptography.** This is the
strongest use-case and the one that justifies the
`commitment: [u8;32]` field.

### 2.3 Intent matching: predicate-shaped dispatch to handlers

**Shape:** the intent pool receives a `MatchSpec`; the cclerk has
held capabilities; the matcher finds a satisfying token.

**DFA fit:** **strong, but with caveats.** A `MatchSpec` *can*
compile to a DFA over a serialized token representation (treat the
token's `(action, resource, app_id, ...)` as a bytestring, build
a pattern). Two questions:

1. **Is compilation worth it?** Today's matcher iterates
   capabilities and compares fields. For cipherclerks with 10s of
   tokens, compilation is overkill. For service-mesh cipherclerks with
   1000s of tokens (a hub that brokers caps), DFA dispatch with a
   single `O(n)` byte scan dominates.
2. **What about the proof side?** The current matcher emits a
   STARK proof of "I have a token satisfying spec S" via an
   *intent-specific* circuit. Compiling to DFA would let the proof
   be "I have a token whose serialization matches DFA D" — a
   single uniform circuit (`tests/src/dfa_circuit.rs` already
   exists). Trade-off: smaller, more uniform circuits vs. higher
   compile-time complexity per intent.

**Verdict:** **userspace-optional.** Offer a
`MatchSpec::compile_to_dfa() -> RouteTable<MatchSpec::Action>`
that an intent broker *may* invoke. Default matcher stays
Datalog-style.

### 2.4 CapTP message routing (which session, which handler)

**Shape:** a CapTP message carries a swiss number; the gateway
looks up the session and dispatches.

**DFA fit:** **weak as primary path, useful as filter.** Swiss
numbers are 32-byte opaque hashes; a DFA over swiss numbers is
just a hash table with extra steps. **But** as a *coarse pre-filter*
(reject obviously-malformed framing before swiss lookup), the DFA
is the right shape. And for *export-side* routing — "this
endpoint exports caps at swiss numbers in range R; route external
traffic accordingly" — a DFA over framing bytes is the natural
classifier.

**Verdict:** **keep CapTP's swiss-table as the fast path.** Use
the DFA as an optional pre-filter at the wire ingress (drop
malformed, route by family before swiss lookup). See §7.

### 2.5 Bridge / observation routing (federation A's observers vs B's)

**Shape:** a bridge node has multiple federation observers, each
subscribed to different chains; incoming events must route to the
right observer pipeline.

**DFA fit:** **strong.** Federation IDs are small, the routing
table is constitutionally bound (which federations does this bridge
relay for?), and the `RouteTarget::Federation(GroupId)` variant
already exists. The bridge audit
(`AUDIT-morpheus-federation-blocklace.md`) names topic-filtered
gossip as the missing piece.

**Verdict:** **first-class win.** This is the case where the
existing `wire::dfa_router` API needs no semantic change, just
production wiring.

### 2.6 Discord-bot slash-command dispatch

**Shape:** Discord sends a slash-command interaction with a
`command_data.name` ("/transfer", "/cipherclerk/balance"); the bot
routes to a handler.

**DFA fit:** **strong, low-stakes.** The slash-command set is
small and constitutionally stable (you don't add slash commands
mid-flight without a deploy); a `compile_routes(&[("/transfer/*",
Handler("transfer")), ...])` is exactly what the
`discord-bot/src/commands/mod.rs` dispatcher should be doing.
Today it's a hand-written `match` on command name. Migrating gives
nothing dramatic — but it *unifies the dispatcher with the rest
of the app surface*, which matters for the broader "starbridge-apps
share one mesh" story.

**Verdict:** good demo, low payoff in isolation. Use it as the
*first* test consumer of the unified router because the failure
mode is benign.

### 2.7 The full table

| Use case | Current state | DFA primary fit? | Surface gap |
|---|---|---|---|
| Service mesh path dispatch | each app rolls its own | yes | `RouteTarget` too narrow; no `remainder` |
| Governance atomic-swap | `GovernedRouter` exists, unused | yes | crypto stub in `update_routes` |
| Intent matching | Datalog-style today | yes (optional) | no `MatchSpec → DFA` compiler |
| CapTP routing | swiss-table | no (use as filter) | needs pre-filter integration |
| Bridge / federation routing | unimplemented | yes | needs wiring into bridge crate |
| Discord slash-commands | hand-written match | yes (low payoff) | trivial integration |
| Gossip topic filtering | flat broadcast | yes | needs `intent::gossip` integration |

**Summary:** the API is the right *shape* for ~6 of 7 candidate
use-cases. The compiler vocabulary is the limit, not the
architecture.

---

## §3. The three options

### Option A — lift `rbg::routing` into `wire/` (or its own crate)

**Pros:**
- The capability is already built. Real NFA→DFA, real combinators,
  intersection, AIR-trace, capability-secure source splitting.
- ~1346 LOC of working tests-pass code.
- Closes the "kept excluded until either integrated or removed"
  TODO in `Cargo.toml`.
- Unlocks gossip-topic filtering, intent-matching-as-DFA, in-circuit
  routing proofs at very little extra work.

**Cons:**
- Edition 2021 vs workspace 2024. Mechanical fix but real.
- `rbg::routing::Dfa { num_states: u32, transitions: Vec<u32>,
  start, accepting: BTreeSet<StateId> }` is **structurally
  incompatible** with `wire::dfa_router::RouteTable { transitions:
  Vec<u8>, num_states: usize, accept_map: HashMap<u8,
  RouteTarget> }` — `u8` vs `u32` states, accept-set vs
  accept-map. Reconciling means rewriting the in-circuit
  constraint to take `u32` and replacing the `u8` cap with the
  more permissive `u32`.
- `PacketSource` and `FilterTree` are *more* than `wire` wants;
  they belong with the directory cluster, not with the bare
  router.
- "Promote in place" leaves two crates importing two slightly
  different `RouteTarget`-shaped things until the migration
  completes.

**Effort:** ~1-2 weeks for the engine swap + downstream fixes.

### Option B — improve `wire::dfa_router` to match RBG's capability

**Pros:**
- Stays in canonical `wire/`. No edition mixing. No crate moves.
- Forces the design conversation about the *public surface* (what
  is a `RouteTarget` really?) up front.
- The pieces of `rbg::routing` we need are well-isolated: the
  combinator surface, NFA, determinization, intersection,
  AIR-trace. We can port those modules *by lifting their code*
  while throwing away `PacketSource` / `FilterTree`.
- Lets us keep the `u8`-or-`u32` decision open: `u32` for
  expressivity, with a typed accept-map.

**Cons:**
- Re-implementation work (even though the source is right there in
  `rbg/`). Subset construction in particular is tedious.
- "Abandons RBG learnings" *only if* we don't port the AIR-trace
  shape — which we should. If we port the regex combinators + the
  AIR-trace shape, we're really doing Option A with cosmetic
  surgery.

**Effort:** ~1-2 weeks. Roughly the same as A.

### Option C — design a clean unified replacement

**Pros:**
- Best long-term shape. We can be principled about the public
  vocabulary (`Route<Dest>`, `Predicate`, `RouteCaveat`,
  `Classifier`).
- Forces us to confront the destination-vs-policy split (§1.2,
  `governed-namespace`).
- One implementation in one place.

**Cons:**
- Most upfront work.
- Designs of this shape (clean from-scratch unifications) **almost
  always recreate the existing two implementations plus a third
  set of issues** unless we have a very specific user-shaped
  reason for the rebuild.
- The existing audit material is *already* the cleanup analysis. A
  C-style rebuild that doesn't follow this audit's findings
  would mean ignoring 600+ lines of recent designer work.

**Effort:** ~4-6 weeks. High risk of bike-shedding.

### Recommendation: **Option B, biased toward A.**

Net structure:

1. **Lift `rbg::routing`'s `Pattern → Nfa → Dfa` compiler into
   `wire::dfa_router`** as a new internal module (call it
   `compiler`). Keep the existing trie-only `compile_routes` for
   backwards compatibility — it becomes a thin shim over the new
   compiler. The new compiler accepts `Pattern` and produces a
   `RouteTable` with `u32` states and `BTreeMap<u32, RouteTarget>`
   accept map.

2. **Generalize `RouteTarget`** to either (a) a typed
   `RouteTarget<T>` where the current four variants are the
   default `T`, or (b) add a `RouteTarget::Userspace { kind:
   String, payload: Vec<u8> }` open variant for apps to encode
   their own destinations. **Recommend (b)** — typed generics
   propagate through the whole `Router`/`GovernedRouter`/
   `dispatch_*` family and are painful in the wire crate's
   downstream consumers.

3. **Keep `GovernedRouter`** — it's the right shape. Wire the
   actual constitutional signature verification (it's a stub
   today).

4. **Port the AIR-trace shape**
   (`rbg::routing::generate_air_trace`) as
   `wire::dfa_router::generate_air_trace`. This is ~30 lines and
   directly feeds `tests/src/dfa_circuit.rs`.

5. **Defer `PacketSource` / `FilterTree`.** These belong with the
   directory lift (§5/§8), not with the bare router. If we ever
   want capability-secure source splitting, it gets its own
   `wire::source_capability` module that depends on the
   classifier-as-capability shape that the directory cluster
   provides.

6. **Decompose `apps/governed-namespace::routes`** into:
   `wire::dfa_router::RouteTarget::Userspace { kind:
   "namespace_class", payload: bincode(RouteClass) }`. Then the
   app's `Classification` becomes a `RouteTarget::Userspace`
   decode + the matched-prefix remainder (which the router
   should newly expose).

7. **Delete `rbg::routing`** once the lift is complete (or keep
   the `rbg` crate around as a design-museum exhibit per the
   designer's "let's not lose that open loop" framing — but
   without `routing.rs`).

This is Option B in name (no crate moves, no big rename), Option A
in effect (the working code comes from `rbg`).

---

## §4. Userspace surface — how a starbridge-app authors a DFA route

The proposed authoring shape, after the lift:

### 4.1 Sketch for a starbridge-app

```rust
use dregg_wire::dfa_router::{compile_routes, Pattern, RouteTarget, GovernedRouter};

// A starbridge-app declares its routing table at startup.
// Each route is a (Pattern, RouteTarget) pair.
let table = compile_routes(&[
    // Literal path: only "/health" matches.
    (Pattern::literal("/health"),
     RouteTarget::Handler("health_check".into())),

    // Wildcard suffix: "/cells/<cell_id>/*" routes to the cell.
    (Pattern::path_to_cell("/cells/", stablecoin_cell_id),
     RouteTarget::Cell(stablecoin_cell_id)),

    // Predicate-shaped intent dispatch: messages starting with
    // 0x01 (auth) followed by 4+ bytes route to the auth handler.
    (Pattern::seq(vec![
        Pattern::byte(0x01),
        Pattern::repeat(Pattern::any_byte(), 4),
        Pattern::wildcard(),  // tail
     ]),
     RouteTarget::Handler("auth".into())),

    // Userspace destination: governed-namespace shape.
    (Pattern::path_prefix("/treasury/"),
     RouteTarget::Userspace {
         kind: "namespace_class".into(),
         payload: bincode::serialize(&RouteClass::Multisig { threshold: 3 }).unwrap(),
     }),

    // Drop pattern: anything starting with "/blocked/" is silently discarded.
    (Pattern::path_prefix("/blocked/"),
     RouteTarget::Drop),
]);

// Wrap in a GovernedRouter — table swaps require constitutional approval.
let router = GovernedRouter::new(table);
```

### 4.2 Classification API

```rust
// Classify a path. Returns the matched target, the matched prefix,
// and the remainder (what's after the matched prefix). The remainder
// is the missing piece in today's wire::dfa_router and the reason
// apps/governed-namespace had to roll its own.
let result: Option<Classification<'_>> = router.classify_path(b"/treasury/budget.csv");
//   Classification {
//     target: &RouteTarget::Userspace { kind: "namespace_class", payload: ... },
//     matched_prefix: "/treasury/",
//     remainder: "budget.csv",
//   }
```

### 4.3 Governance amendment

```rust
// Compile the proposed new table.
let new_table = compile_routes(&[/* ... amended routes ... */]);

// Threshold-sign the (old_commitment, new_commitment) pair.
let proof = GovernanceProof {
    expected_old_commitment: router.commitment().clone(),
    proof_data: threshold_sig.to_bytes(),  // real signature now, not a stub
};

// CAS the table. If anyone else amended in the meantime, the CAS
// fails and we re-compute.
router.update_routes(new_table, &proof)?;
```

### 4.4 Governed-namespace as a starbridge-app, after the lift

The whole app collapses into:

```rust
// At startup, build the route table from configured RouteClasses.
let routes = config.route_classes.into_iter().map(|(prefix, class)| {
    (Pattern::path_prefix(&prefix),
     RouteTarget::Userspace {
         kind: "namespace_class".into(),
         payload: bincode::serialize(&class).unwrap(),
     })
}).collect::<Vec<_>>();
let router = GovernedRouter::new(compile_routes(&routes));

// On each request, classify and decode.
let classification = router.classify_path(request.path.as_bytes())
    .ok_or(StatusCode::NOT_FOUND)?;
let route_class: RouteClass = match classification.target {
    RouteTarget::Userspace { kind, payload } if kind == "namespace_class" => {
        bincode::deserialize(payload)?
    }
    _ => return Err(StatusCode::BAD_GATEWAY),
};

// Apply the access policy.
match route_class {
    RouteClass::Public => Ok(()),  // anyone can read
    RouteClass::MembersOnly => check_member_auth(&request)?,
    RouteClass::AdminOnly => check_admin_token(&request)?,
    RouteClass::Multisig { threshold } => check_multisig(&request, threshold)?,
    RouteClass::Custom(name) => run_custom_policy(&name, &request)?,
}
```

The app's `routes.rs` (287 lines today) becomes ~40 lines, the
DFA logic moves to the canonical crate, and route amendments go
through `GovernedRouter::update_routes` (free atomic-swap + CAS
semantics + commitment binding) instead of `RoutingTable::
replace_all` (a `clear() + insert()` loop with a manual `version
+= 1` and a JSON-based commitment that's not actually used to bind
votes).

### 4.5 Authoring sugar (proposed `app-framework` extension)

```rust
// In app-framework, add a helper:
pub trait DfaRoutedApp {
    fn routes(&self) -> Vec<RouteSpec<Self::Destination>>;
    type Destination: serde::Serialize + serde::de::DeserializeOwned;

    fn dispatch(&self, path: &str) -> Result<(Self::Destination, &str), AppError>;
}

// Apps implement DfaRoutedApp; the framework compiles routes,
// installs a GovernedRouter, exposes the governance endpoints.
```

This is the *userspace* shape — `dregg-app-framework` would be the
natural home for an `axum`-layer middleware that pre-classifies
requests through the GovernedRouter and attaches the result as a
request extension.

---

## §5. Composition with slot caveats (per `SLOT-CAVEATS-DESIGN.md`)

The slot-caveats design lifts `storage::programmable::
QueueConstraint` variants into `cell::program::StateConstraint`.
Caveats *gate transitions on a cell*: "this field may only
increase," "this slot is write-once," "the sender must be in the
authorized set."

DFA routes *select destinations from paths*: "this path goes to
cell X," "this path goes to handler Y."

### 5.1 They are orthogonal — and that's good

A route classification answers **where** a message goes. A caveat
answers **whether** the message may execute. Together:

```
incoming request
    │
    ▼
DFA classify ────► RouteTarget::Cell(stablecoin)
                    │
                    ▼
                  cell program's StateConstraints evaluated
                  on (old_state, new_state, sender, ...)
                    │
                    ▼
                  accept / reject
```

The two stages are at *different layers*: routing is wire-level
(no cell state needed), caveats are turn-level (require old_state,
new_state, validation context). Conflating them produces neither.

### 5.2 But routes can carry caveats

The `RouteTarget::Userspace { kind, payload }` variant lets an
app encode "the route is to cell X, but the caveat 'admin only'
must hold." Concretely:

```rust
RouteTarget::Userspace {
    kind: "gated_cell".into(),
    payload: bincode::serialize(&GatedCell {
        cell: stablecoin_cell_id,
        required_caveats: vec![
            Caveat::SenderInSet { set_root: admin_root },
            Caveat::CommitWindow { start: H, end: H+1000 },
        ],
    }).unwrap(),
}
```

The router classifies; the dispatcher decodes the userspace
target; the app's middleware evaluates the caveats; the turn
executes (with the cell-program's own caveats checked again at
turn time, defense in depth).

### 5.3 Should DFA dispatch *be* a caveat-evaluation pattern?

**No.** Caveats are predicates over (old_state, new_state,
context). DFA dispatch is a pattern match over a bytestring. The
input domains are different: caveats reason about cell state
deltas; DFAs reason about message classification. They share the
"both can be encoded as AIR constraints" property but at different
constraint shapes:

- DFA constraint: lookup into a transition table per byte
  (`rbg::routing::generate_air_trace` shape).
- Caveat constraint: typed field comparisons against `old_state` /
  `new_state` (the AIR variants `StateConstraint::FieldGte` etc.,
  per `SLOT-CAVEATS-DESIGN.md` §6).

Trying to unify them produces a worst-of-both-worlds VM. **Keep
them separate; compose them at the dispatcher.**

### 5.4 The composition layer

The natural composition spot is the *dispatcher*, not the router
or the executor:

```
wire ingress
    │
    ▼
GovernedRouter::classify_path  ←─── route table commitment in constitution
    │
    ▼
Dispatcher (app-framework)
    │
    ├─► extracts caveats from RouteTarget::Userspace
    │
    ├─► binds them to incoming Turn
    │
    ▼
TurnExecutor
    │
    ├─► validates cell program's StateConstraints
    │
    ├─► validates Turn-level caveats (the ones the dispatcher added)
    │
    ▼
emit Receipt
```

**Two evaluators, two domains, one Receipt.** This shape composes
without conflating.

---

## §6. Composition with the intent system

The intent crate has `MatchSpec` (predicate language),
`matcher.rs` (local Datalog-ish evaluation), `gossip.rs` (flat
broadcast pool), and `solver.rs` (matching engine for intent
fulfillment).

### 6.1 Does DFA subsume intent dispatch? No.

`MatchSpec` is **structural**, not bytestring-shaped:

```rust
pub struct MatchSpec {
    pub action: ActionPattern,        // recursive predicate
    pub resource: Option<String>,
    pub app_id: Option<String>,
    pub service: Option<String>,
    pub user_id: Option<String>,
    pub features: Vec<String>,
    pub oauth_provider: Option<String>,
    pub constraints: Vec<Constraint>,  // budget, expiry, etc.
    pub compound: Option<Vec<MatchSpec>>,  // recursive AND
}
```

These have **typed fields with semantics** (a budget constraint
isn't comparable to a byte position). A DFA could match against a
*serialized* `MatchSpec`, but the cost is paid in either (a)
serialization complexity (canonicalizing all field orderings) or
(b) loss of expressivity (the DFA can't reason about "budget >=
1000" without unrolling it into a per-byte byte-range pattern,
which makes table size explode).

**Verdict:** intent matching is **structurally distinct** from DFA
routing. The matcher should stay as it is.

### 6.2 But intent *gossip topics* are DFA-shaped.

`intent/src/gossip.rs` today is flat broadcast: every intent goes
to every connected peer. The scoping story (per
`STORAGE-REFLECTIVITY-RBG-DFA-AUDIT.md` §4.4) needs **topic
filtering**: only deliver intents on topic T to peers subscribed
to T.

This IS the DFA's natural shape: a `TopicFilter` (rbg's existing
`rbg::routing::TopicFilter`) compiled from a topic pattern, run
against incoming messages, atomically swapped when topics change.

**Verdict:** wire the unified `wire::dfa_router` into
`intent::gossip` as the topic-classification layer. The intent
matcher itself remains structural; *which peers see which
intents* becomes DFA-mediated.

### 6.3 The seam

```
sender                               receiver
  │                                     │
  ▼                                     ▼
Intent { spec, topic_id }           subscribe_topic(t) ──► TopicFilter
  │                                     │                      │
  ▼                                     ▼                      │
gossip.broadcast(topic_id, intent)    on_message:               │
  │                                     classify(msg) ─────────┘
  └────────────────────────────────────►│
                                        ▼
                                      if accepted: matcher.evaluate(spec, held_caps)
```

The DFA layer answers "should I see this intent?" The matcher
answers "do my caps satisfy this intent?" Different questions,
same pipeline.

### 6.4 `rbg::directory::ScopedIntentPool` is the data structure for this

The `rbg::directory::ScopedIntentPool` already binds intents to a
gossip topic derived from a `DirectoryCell`. The DFA topic filter
+ the scoped pool's membership check (the directory's ACL) +
the matcher's local predicate check = the three layers of intent
visibility:

1. **DFA gossip filter:** wire-level, byte-pattern, fast.
2. **Directory ACL:** cell-state, membership-set check.
3. **Matcher predicate:** structural, held-cap-comparison.

The DFA work is the wire-level prerequisite for the directory
lift; the directory lift is the next-level dregg-directory crate
(out of scope here but cross-referenced).

---

## §7. Composition with CapTP

### 7.1 CapTP today: swiss-table routing

`captp/src/handoff.rs` and `captp/src/session.rs` use a
`SwissTable` (HashMap-keyed by swiss number) for the primary
dispatch: "this incoming message references swiss S; look up
session E; deliver." The wire layer's `captp_routing.rs`
constructs the appropriate `Effect` (`ExportSturdyRef`,
`EnlivenRef`, `DropRef`, `ValidateHandoff`) and queues a `Turn`.

Swiss numbers are 32-byte opaque hashes. A DFA over swiss numbers
is just hash-table lookup with extra steps. **The fast path
should stay as it is.**

### 7.2 Where DFA helps CapTP

Three places:

1. **Ingress malformed-message rejection.** Before the swiss-table
   lookup, the message must be parsed (currently postcard). A DFA
   over the leading bytes can pre-filter framing errors,
   wrong-protocol-version messages, and known-blocked patterns
   atomically (drop without expensive parse), with the same
   `RouteTarget::Drop` mechanism that exists today.

2. **Federation-level forwarding.** When a CapTP message arrives
   addressed to a federation other than this one
   (`Effect::CapTpForward`-style — the architecture supports it),
   the wire layer must decide which peer federation to forward to.
   `RouteTarget::Federation(GroupId)` is exactly this. Today this
   isn't wired in because federation forwarding is itself
   undefined; when it's defined, the DFA is the right substrate.

3. **Receipt fan-out classification.** When a `Receipt` is
   emitted, gossip layers fan it out to interested peers. The
   fan-out filter is naturally a DFA over the receipt's topic
   bytes (the `swissprefix` or `cell_id` family).

**Verdict:** **swiss-table is the keystone fast path; DFA wraps
it as a pre-filter at ingress and a post-filter at fan-out.** The
two compose without conflict. CapTP message dispatch (the
"deliver to session E") stays out of the DFA; CapTP message
*acceptance* (drop / forward / pass-through) goes through it.

### 7.3 In-circuit composition

The DFA-in-AIR encoding (`tests/src/dfa_circuit.rs`) and the
CapTP-Effect AIR encoding (`turn::action::Effect` variants for
`ExportSturdyRef` / `EnlivenRef` / `DropRef`) are independent
constraint sets that can coexist in the same proof. A
receipt-bearing proof can include "and the message classified to
route target T per route table commitment C" as an *additional*
constraint. Useful for: "the relay routed this message correctly
per the governance-approved table."

---

## §8. Migration plan

### 8.1 Option B-with-borrowings: concrete steps

**Phase 1 — engine lift (~3-5 days):**

1. Create `wire/src/dfa_router/compiler.rs`. Copy
   `rbg::routing::{Dfa, Nfa, NfaState, Pattern, pattern_to_nfa,
   dfa_intersection}` into it. Convert from edition 2021 to 2024
   (mostly: re-check `for byte in 0u16..=255u16` loops — they
   already work in 2024). Convert `BTreeSet<StateId>` accept set
   to a `BTreeMap<StateId, RouteTarget>` accept map. Switch
   `StateId` from `u32` to `u32` (no change, since
   `wire::dfa_router` was `u8` — this is the breaking change for
   `wire`'s internals).

2. Update `wire::dfa_router::RouteTable` to use `u32` states:
   ```rust
   pub struct RouteTable {
       pub commitment: [u8; 32],
       pub transitions: Vec<u32>,  // was: Vec<u8>
       pub num_states: u32,         // was: usize
       pub accept_map: BTreeMap<u32, RouteTarget>,  // was: HashMap<u8, ...>
   }
   ```
   This breaks the existing `Router::run_dfa` (the `state as
   usize * 256 + byte as usize` cast still works; the `state ==
   0` dead-state check still works). Net: ~30 lines edited.

3. Re-export `Pattern` from `wire::dfa_router::compiler` so apps
   can write patterns directly. Keep the existing
   `compile_routes(&[(&str, RouteTarget)])` as a thin shim that
   converts URL strings to `Pattern::path_prefix` + the new
   compiler.

4. Add `RouteTarget::Userspace { kind: String, payload: Vec<u8>
   }` variant. Update `DispatchDecision` correspondingly.

5. Add `Classification { target: &RouteTarget, matched_prefix:
   &[u8], remainder: &[u8] }` and the `classify_path_full` method
   that returns it.

6. Port `generate_air_trace` and `verify_air_trace`.

**Phase 2 — finish governance (~2 days):**

7. Replace `GovernanceProof::proof_data: Vec<u8>` with a real
   threshold-sig type. Hook into `federation::Constitution`'s
   approved-quorum verification (see
   `FEDERATION-UNIFICATION-DESIGN.md` for the shape). Add
   `GovernanceProof::verify(&constitution)` that the
   `update_routes` call uses.

**Phase 3 — first consumer (~2-3 days):**

8. Rewrite `apps/governed-namespace::routes::RoutingTable` as a
   thin wrapper around `wire::dfa_router::GovernedRouter`. Replace
   `RouteEntry::class: RouteClass` with `RouteTarget::Userspace {
   kind: "namespace_class", payload: bincode(RouteClass) }`.

9. Wire `discord-bot::commands` to use a `GovernedRouter` for
   slash-command dispatch (low-stakes proving-ground).

**Phase 4 — production wiring (~1-2 weeks):**

10. Add `intent::gossip::TopicFilter` (the `rbg::routing::
    TopicFilter` shape, now in `wire`) and hook it into the
    intent broadcast layer. Per-topic subscription replaces flat
    broadcast.

11. Add the wire ingress pre-filter: server.rs gets a
    `GovernedRouter` that classifies incoming framed messages
    before postcard parsing. Malformed → `RouteTarget::Drop`.

12. Bridge crate: integrate per-federation routing for
    observation bridges.

**Phase 5 — directory lift (out of scope, future work):**

13. Lift `rbg::directory::{DirectoryCell, ScopedIntentPool,
    MetaDirectory}` into a new `dregg-directory` crate. This is a
    separate ~3-4 week workstream. It depends on Phase 1's
    compiler being in place (the scoped pool uses the
    classifier internally), but is otherwise independent.

14. Delete `rbg/src/routing.rs` (once its contents are in
    `wire::dfa_router::compiler`). Decide whether to delete the
    rest of `rbg/` or keep it as an exhibit per the designer's
    framing.

### 8.2 LOC estimate

| Phase | Files touched | New LOC | Edited LOC | Deleted LOC |
|---|---|---:|---:|---:|
| 1 | `wire/src/dfa_router{.rs,/compiler.rs}` | ~900 (from rbg) | ~150 | 0 |
| 2 | `wire/src/dfa_router.rs`, `federation/src/constitution.rs` | ~80 | ~30 | 0 |
| 3 | `apps/governed-namespace/src/*.rs`, `discord-bot/src/commands/*.rs` | ~100 | ~150 | ~250 |
| 4 | `intent/src/gossip.rs`, `wire/src/server.rs`, `bridge/src/*.rs` | ~300 | ~100 | 0 |
| 5 (deferred) | new `dregg-directory/` | ~2500 (from rbg) | 0 | rbg's 4500 |

Total for Phases 1-4: **~1400 new LOC, ~430 edited, ~250 deleted**.
~2-4 weeks of focused work.

### 8.3 Risk mitigations

- **Risk:** `u8` → `u32` state ID change breaks downstream
  consumers (preflight, teasting). **Mitigation:** the public
  surface (`classify`, `classify_path`, `dispatch_*`) is
  unchanged; only the internal `RouteTable` field types shift.
  Downstream code that inspected `transitions: Vec<u8>` directly
  is in tests only.

- **Risk:** the `RouteTarget::Userspace` open variant lets apps
  encode arbitrary destinations, breaking the audit-friendliness
  of the constitution-bound table. **Mitigation:** require the
  `kind: String` to be a registered identifier (a "userspace
  destination kind registry" — sibling to the existing
  `FactoryRegistry`). Apps register their destination kinds at
  deployment time; routes referencing unregistered kinds fail
  validation.

- **Risk:** AIR-trace shape mismatch between `rbg::routing` and
  `circuit::dsl::circuit:1711-1941`. **Mitigation:** the trace
  shape is straightforward (`step, state, byte, next_state`); the
  existing circuit definition expects exactly this. Cross-check
  is mechanical.

- **Risk:** the directory lift (Phase 5) discovers that the
  scoped pool's pattern matching wants the DFA *compiled
  per-pool*, not per-route-table. **Mitigation:** the
  `wire::dfa_router::compiler` module is reusable; the directory
  crate imports it just like an app would. The compiler is
  decoupled from `GovernedRouter`.

---

## §9. Open questions for the designer

1. **`RouteTarget::Userspace` shape:** open `{ kind: String,
   payload: Vec<u8> }`, or typed `RouteTarget<T>` generic, or a
   registry of named variants (`UserspaceKind::NamespaceClass(_)`
   / `UserspaceKind::SlashCommand(_)` / ...). The open-variant
   choice is simplest; the typed generic is purest; the registry
   is auditable. Recommendation: open variant + kind registry
   (see §8.3 risk #2). Designer call.

2. **State-ID width:** `u16` (65k states, fits typical apps) vs
   `u32` (4G states, future-proof). `rbg::routing` uses `u32`;
   the AIR encoding can accommodate either. `u16` would halve
   the transition table size, which matters because
   `BLAKE3(transitions)` is the commitment (and `Merkle(transitions
   .chunks)` is a likely future evolution if tables grow large).
   Recommendation: `u32` for design symmetry with `rbg::routing`,
   accept the size cost. Designer call.

3. **Should `compile_routes` accept Patterns or stay
   string-based?** Backwards-compat says keep
   `compile_routes(&[(&str, RouteTarget)])` and add a new
   `compile_patterns(&[(Pattern, RouteTarget)])`. The string-based
   form is uglier but ergonomic for apps that just want URL
   prefixes (the 80% case).

4. **In-circuit routing proofs — when?** The AIR primitives
   exist (`tests/src/dfa_circuit.rs`). The wire-level DFA does
   not emit proofs today. Is there a near-term use case (bridge
   audit logs? receipt-bound routing decisions?) or is this
   speculation? If we build the trace-gen path but never wire it
   to a Prover, that's wasted work.

5. **Should `intent::gossip` topic-filter changes go through
   `GovernedRouter`?** Topics are app-level concepts; routes
   are typically federation-bound. The composition is "the
   federation's constitution names which topics are valid for
   each app, the app's DFA topic-filter is bound to that
   namespace." But the granularity might be wrong — if a topic
   filter swaps every block (new subscription), that's
   constitutionally heavyweight. Recommendation: separate the
   *topic filter table* (per-peer, atomically swappable, NOT
   constitutionally bound) from the *route table*
   (federation-bound, governance-gated). The DFA engine is
   shared; the swap protocols differ.

6. **`RouteTarget::Federation(GroupId)` semantics:** today the
   variant exists but federation forwarding doesn't. Should this
   variant be removed until federation forwarding is real (YAGNI),
   or left as a forward-compatible placeholder? Recommendation:
   leave. The cost is one enum variant; the benefit is that the
   commitment hash for current route tables doesn't change when
   forwarding ships.

7. **Should `apps/governed-namespace::routes` be deleted
   immediately or deprecated for a release?** Net change ~250
   lines deleted, ~50 added. The app has tests against its own
   API; switching to `wire::dfa_router` is mechanical but
   requires fixing those tests. Recommendation: delete in the
   same PR as the engine lift, fix tests inline.

8. **What about `RouteTarget::Drop` semantics in adversarial
   settings?** A malicious operator could swap the route table to
   `Drop` everything. The constitutional binding is supposed to
   prevent this, but the threshold-signature verification in
   `update_routes` is a stub today. Recommendation: Phase 2's
   real signature verification is non-negotiable before any
   wire-level production wiring.

9. **`rbg::directory` lift — separate crate or merge into
   `cell/`?** A `dregg-directory` crate keeps `cell/` focused on
   the cell model and lets directory cells be opt-in. Merging
   into `cell/` means every cell-program-aware consumer sees the
   directory types. Recommendation: separate crate
   (`dregg-directory`) depending on `cell`. The directory is a
   higher-level construct.

10. **What's the lifecycle of a `RouteTable` once it's compiled
    but before it's installed in a `GovernedRouter`?** Can a
    starbridge-app dry-run-compile a proposed amendment, ship the
    serialized form, hold a vote on it, then install? Yes — the
    `RouteTable` is `Clone + Debug`. But the proposal-vote
    machinery (which crate hosts it?) is unspecified. Cross-link
    to `FEDERATION-UNIFICATION-DESIGN.md` and any constitution
    crate doc.

11. **Capability-secure source splitting** (the
    `rbg::routing::PacketSource` / `FilterTree` shape): is this
    useful in dregg without seL4-style explicit ports? Inclined
    toward "yes" (CapTP sessions are roughly the seL4-port
    analog), but the integration story isn't sketched. If the
    answer is "not yet," defer the `wire::source_capability`
    module to the directory lift.

12. **Discord-bot use of DFA — does it bring value, or is it
    busywork?** The current hand-written `match` is fine. The
    payoff is unification with the rest of the mesh. If the
    designer's view is "starbridge-apps share one dispatch
    layer," then yes. Otherwise, skip.

---

## §10. Anti-promises (honest about what's hype)

What this design does *not* claim:

1. **DFA dispatch is not faster than hash-table lookup for swiss
   numbers.** The DFA is for *pattern* dispatch, not for
   point-lookup. Where swiss tables already work, they stay.

2. **In-circuit routing proofs are not free.** Adding a DFA-trace
   to a Receipt-bound proof grows the AIR; the
   `tests/src/dfa_circuit.rs` cost is real. Use them where they
   pay off (federation-attested forwarding decisions, bridge
   audit trails), not for every internal route.

3. **The `Userspace` open variant trades off auditability for
   flexibility.** A non-registered kind in a constitutionally
   bound route table is an attack surface. The registry mitigates
   but doesn't eliminate.

4. **`rbg::routing` is well-written for what it is, but it is
   not a complete implementation of a production routing
   layer.** It has no governance hooks, no real source-of-truth
   for `RouteTarget` semantics, no integration tests with
   `wire::server.rs`. The lift is "take what's good (the
   compiler, the AIR-trace), leave what's not (the stub types,
   the PacketSource/FilterTree until we need it)".

5. **The directory lift (Phase 5) is a separate workstream.**
   This design does not commit to delivering it; it commits to
   not blocking it. The DFA engine refactor is the *foundation*
   that the directory work depends on.

6. **`apps/governed-namespace::routes` is genuinely a duplicate
   reinvention**, but it's been that way long enough that there
   may be subtle differences in the prefix-match semantics (e.g.,
   normalized leading `/`, trailing-slash handling) that the lift
   needs to preserve. Tests-first migration is the safety net.

7. **The 1-2 week effort estimate assumes someone has read both
   `rbg::routing` and `wire::dfa_router` deeply enough to
   anticipate the type-system edits.** A fresh contributor would
   need 3-4 weeks. Budget accordingly.

8. **None of this fixes intent-pool privacy.** The DFA gossip
   filter scopes audience, but the intent payload itself is still
   in-the-clear within the scoped pool. Privacy (encrypted-payload
   pools, blinded matching) is its own design (see
   `intent/src/trustless.rs` for the WIP).

9. **Slot caveats and DFA routes don't replace cell programs.**
   They're new vocabulary *for* cell programs to use; the cell
   program itself remains the load-bearing predicate.

---

## §11. The minimal one-paragraph summary

There are three DFA-ish implementations in the tree.
`wire/src/dfa_router.rs` is the canonical home but has a 255-state
cap and only supports URL-style trie patterns; it's
governance-bound but has no production consumers.
`apps/governed-namespace/src/routes.rs` is a 287-line longest-prefix
matcher that pretends to be a DFA and reinvents what wire already
provides. `rbg/src/routing.rs` is a 1346-line, workspace-excluded,
edition-2021 implementation of the actual NFA→DFA pipeline with
combinators, intersection, AIR-trace emission, and
capability-secure source splitting. The proposal is to **lift the
compiler and AIR-trace from `rbg::routing` into
`wire::dfa_router`**, add an open `RouteTarget::Userspace` variant
plus a `kind` registry, generalize state IDs to `u32`, finish the
threshold-signature verification in `GovernedRouter::update_routes`,
and then wire the unified engine into three real consumers:
governed-namespace (replacing its duplicate), intent gossip topic
filtering, and the wire ingress pre-filter. The DFA engine and the
slot-caveat evaluator are orthogonal — routes select *where*,
caveats decide *whether* — and compose at the dispatcher. CapTP's
swiss-table stays as the fast path with the DFA wrapping it as a
pre-filter at ingress. The directory cluster
(`DirectoryCell` / `ScopedIntentPool` / `MetaDirectory`) is a
separate, larger lift into its own `dregg-directory` crate, out of
scope for this PR but enabled by it. Phases 1-4 are ~2-4 weeks;
Phase 5 (the directory lift) is its own multi-week workstream.

---

## §12. Citations (file pointers)

- Wire DFA router: `/Users/ember/dev/breadstuffs/wire/src/dfa_router.rs:1-700`
- Wire CapTP routing: `/Users/ember/dev/breadstuffs/wire/src/captp_routing.rs:1-279`
- RBG routing engine: `/Users/ember/dev/breadstuffs/rbg/src/routing.rs:1-1346`
- RBG directory cluster: `/Users/ember/dev/breadstuffs/rbg/src/directory.rs:1-1707`
- RBG VFS: `/Users/ember/dev/breadstuffs/rbg/src/vfs.rs:1-1517`
- Governed-namespace routing reinvention: `/Users/ember/dev/breadstuffs/apps/governed-namespace/src/routes.rs:1-287`
- Governed-namespace test that *claims* to use wire dfa router: `/Users/ember/dev/breadstuffs/apps/governed-namespace/src/main.rs:1139-1177` (doesn't actually import `dregg_wire::dfa_router`)
- Workspace exclusion of `rbg/`: `/Users/ember/dev/breadstuffs/Cargo.toml:10-12`
- Intent MatchSpec: `/Users/ember/dev/breadstuffs/intent/src/lib.rs:344-382`
- Intent matcher: `/Users/ember/dev/breadstuffs/intent/src/matcher.rs:1-100`
- Intent gossip (flat broadcast): `/Users/ember/dev/breadstuffs/intent/src/gossip.rs`
- DFA-in-circuit constraint: `/Users/ember/dev/breadstuffs/circuit/src/dsl/circuit.rs:1711-1941`
- DFA-in-circuit test: `/Users/ember/dev/breadstuffs/tests/src/dfa_circuit.rs`
- Slot caveats design (compose target): `/Users/ember/dev/breadstuffs/SLOT-CAVEATS-DESIGN.md`
- Storage / RBG / DFA audit (the open loop): `/Users/ember/dev/breadstuffs/STORAGE-REFLECTIVITY-RBG-DFA-AUDIT.md`
- Apps audit (Tier-2 #10 `CommittedMap`): `/Users/ember/dev/breadstuffs/APPS-AS-USERSPACE-AUDIT.md`
- Federation unification (constitution binding): `/Users/ember/dev/breadstuffs/FEDERATION-UNIFICATION-DESIGN.md`
- Preflight router check: `/Users/ember/dev/breadstuffs/preflight/src/checks/routing.rs`
- Test harness (router_sim): `/Users/ember/dev/breadstuffs/teasting/src/router_sim.rs`
- Test harness (mesh_sim): `/Users/ember/dev/breadstuffs/teasting/src/mesh_sim.rs`
- Discord-bot commands (slash-command dispatch candidate): `/Users/ember/dev/breadstuffs/discord-bot/src/commands/mod.rs`
- CapTP swiss-table: `/Users/ember/dev/breadstuffs/captp/src/handoff.rs:369-467`
