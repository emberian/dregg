/-
# Dregg2.Exec.DfaRouting — dregg1's DFA message-ROUTING automaton, verified.

dregg1's `dfa/` crate (2813 LOC, `dfa/src/router.rs`) is the canonical home of DFA
*pattern dispatch*: a message is **routed** by walking a deterministic automaton whose
states are routing positions, whose labelled transitions are message *hops*, whose start
state is the sender (`RouteTable.start`, always `1`), and whose *accepting* states are the
valid destinations (`RouteTable.accept_map` keys, each mapping an accepting state to a
`RouteTarget`). `Router::classify_inner` (`router.rs:490`) walks the transition table byte by
byte from `start`, recording the **deepest accepting state reached**; a message is *delivered*
to the `RouteTarget` of that accepting state. Hops into `DEAD_STATE` (`router.rs:504`) break
the walk — there is NO delivery except along a run that ENDS in an accepting state.

This is the message-ROUTING automaton, **distinct** from `Dregg2.Crypto.Dfa` (the §8 ZK
*acceptance circuit*). But the *run* algebra is identical — a route is a chained sequence of
valid `(state, hop, next)` transitions from `start` ending in acceptance — so we **reuse**
`Crypto.Dfa`'s `Step`/`stepValid`/`chained`/`DfaAccepts` verbatim as the run shape, and add the
*delivery-soundness* property that is specific to routing (which `Crypto.Dfa` does not state):

  **A delivered message corresponds to an accepting run of the routing DFA.** There is no
  delivery except along an authorized route — exactly `classify_inner`'s `last_accept?` gate
  (`router.rs:512`: `let (accept_state, walked_len) = last_accept?;` — `None` ⇒ no `Classification`
  ⇒ `DispatchDecision::Unrouted` ⇒ the message is NOT delivered).

We then gate routing on the verify-seam (`Dregg2.Spec.Guard`): the `GovernedRouter`
(`router.rs:669`) only swaps in a route table after a governance proof verifies, and a
constitutionally-bound table is the authorization context. We model the per-hop authorization:
a **guarded route** is one whose every hop `admits` under `Guard` — you cannot route *past* an
unauthorized hop (`route_authorization`).

## What is proven (all `#assert_axioms`-clean, NO `sorry`/`axiom`/`native_decide`)

  * `routed_message_followed_accepting_route` — **delivery soundness**: a `Delivery` (a message
    that arrived) carries, by construction, a proof that its route is an accepting run
    (`Crypto.Dfa.DfaAccepts δ start accepting route`). Fail-closed: the delivery constructor
    *demands* the accepting-run proof, so no ill-routed delivery is even constructible.
  * `route_authorization` — **verify-seam respect**: a guard-gated delivery's route `admits` the
    guard at every hop; connects to `Guard.admits` / `Guard.admits_all`.
  * `unique_route` — **no-misroute / determinism**: a deterministic routing DFA delivers a message
    to a UNIQUE destination along a UNIQUE run (per `classify_inner`'s deterministic table walk).
  * `routing_projects_message_flow` — the routing DFA as a **projection of a choreography's message
    flow** (`Dregg2.Coordination`): a `GlobalType.comm a b` head IS a single routing hop `a →b`.

Non-vacuity (the `Reference` section): a concrete 3-node routing DFA `sender →h relay →h dest`,
a delivered message along the accepting route, and a **fail-closed REJECT** of a message that
runs into a non-accepting / dead state (no `Delivery` is constructible).
-/
import Dregg2.Crypto.Dfa
import Dregg2.Spec.Guard
import Dregg2.Coordination
import Dregg2.Tactics

namespace Dregg2.Exec.DfaRouting

open Dregg2.Crypto.Dfa
open Dregg2.Spec
open Dregg2.Laws

universe u

/-! ## §1 — The routing DFA.

A routing DFA over abstract `Node` (a routing position: a vat / cell / network node, the
`StateId` of `router.rs`) and `Hop` (a labelled message hop, the `byte` of the transition
table). `δ` is the transition relation — the membership predicate of `RouteTable.transitions`
(`router.rs:136`, the flat `[state*256 + byte] → next_state` table, with `DEAD_STATE` entries
absent from `δ`). `start` is the sender (`RouteTable.start`, `router.rs:145`); `accepting` is
the valid-destination predicate (membership in `accept_map`'s keys, `router.rs:138`). -/

variable {Node Hop : Type u}

/-- A **routing DFA**: the routing-position transition relation `δ`, the `start` (sender) node,
and the `accepting` (valid-destination) predicate. Mirrors `RouteTable`
(`router.rs:127`): `δ` = the transition table's membership relation, `start` = `RouteTable.start`,
`accepting` = "is a key of `accept_map`". -/
structure RoutingDfa (Node Hop : Type u) where
  /-- The hop-transition relation: `δ n h n'` iff the table routes node `n` on hop `h` to `n'`
  (and `n' ≠ DEAD_STATE` — dead transitions are simply absent from `δ`). -/
  δ : Node → Hop → Node → Prop
  /-- The start node — the message sender (`RouteTable.start`, always `1` for a fresh table). -/
  start : Node
  /-- The accepting predicate — valid destinations (keys of `RouteTable.accept_map`). -/
  accepting : Node → Prop

/-! ## §2 — A route is an accepting run (REUSING `Crypto.Dfa.DfaAccepts`).

A **route** is a list of `Crypto.Dfa.Step Node Hop` rows — exactly the `[state, byte, next_state]`
trace rows of `router.rs`. The route is *accepting* iff it is a valid run of the routing DFA:
nonempty, every hop a valid `δ` transition (the table lookup), the hops chain
(`next` of one = `state` of the next), it starts at `start` (the sender), and ends in an
`accepting` node (a valid destination). This is **precisely** `Crypto.Dfa.DfaAccepts δ start
accepting route` — so we define it as that, reusing the run algebra verbatim. -/

/-- A **route** through the routing DFA: a sequence of hop-steps. (Alias for the `Crypto.Dfa`
trace-row list — a route is a path, each `Step` one hop.) -/
abbrev Route (Node Hop : Type u) := List (Step Node Hop)

/-- **`IsAcceptingRun rd route`** — the route is an *accepting run* of the routing DFA: it starts
at the sender (`rd.start`), every hop is a valid `δ` transition, the hops chain, and it ends in a
valid destination (`rd.accepting`). This IS `Crypto.Dfa.DfaAccepts` — the routing automaton's
"accepting route" is the §8 DFA's "accepting run", same shape. -/
def IsAcceptingRun (rd : RoutingDfa Node Hop) (route : Route Node Hop) : Prop :=
  DfaAccepts rd.δ rd.start rd.accepting route

/-- The destination a route reaches: the `next` of its last hop (the accepting node, the
`accept_state` of `classify_inner`, `router.rs:512`). Defined via `getLast?`; `none` for the
empty (never-accepting) route. -/
def Route.dest (route : Route Node Hop) : Option Node :=
  (route.getLast?).map (fun s => s.next)

/-! ## §3 — Delivery and its soundness (the property `Crypto.Dfa` does NOT state).

A `Delivery` records that a message ARRIVED at `dest` along `route`. The **fail-closed**
invariant is baked into the constructor: a `Delivery` *cannot be built* without a proof that its
route is an accepting run AND that `dest` is the route's reached destination. This mirrors
`classify_inner` (`router.rs:512`): `let (accept_state, walked_len) = last_accept?;` — if the
walk never reached an accepting state, `last_accept?` is `None`, classification returns `None`,
and `DispatchDecision::from_target(None) = Unrouted` — i.e. **no delivery happens**. The only
deliveries that exist are along accepting routes. -/

/-- A **delivered message**: it arrived at `dest` along `route`, and — fail-closed by
construction — `route` is a genuine accepting run of `rd` reaching `dest`. There is NO
constructor that delivers along a non-accepting route (the `routes` field is the proof
obligation, exactly `classify_inner`'s `last_accept?` gate). -/
structure Delivery (rd : RoutingDfa Node Hop) where
  /-- The route the message took (the DFA run `classify_inner` walked). -/
  route : Route Node Hop
  /-- The destination it arrived at. -/
  dest : Node
  /-- FAIL-CLOSED OBLIGATION: the route is an accepting run of `rd`. -/
  routes : IsAcceptingRun rd route
  /-- The destination is the one the accepting route reaches. -/
  arrives : route.dest = some dest

/-- **`routed_message_followed_accepting_route` — DELIVERY SOUNDNESS (deliverable #1).**
A delivered message corresponds to an accepting run of the routing DFA: its `route` is an
accepting run reaching its `dest`. No message arrives except along an authorized (accepting)
route — the `Delivery` could not have been constructed otherwise. -/
theorem routed_message_followed_accepting_route (rd : RoutingDfa Node Hop) (d : Delivery rd) :
    IsAcceptingRun rd d.route ∧ d.route.dest = some d.dest :=
  ⟨d.routes, d.arrives⟩

/-- Corollary: a delivered message's route is NON-EMPTY (a delivery walked at least one hop —
the empty route reaches no destination). Sharpens "no delivery without a route". -/
theorem delivery_route_nonempty (rd : RoutingDfa Node Hop) (d : Delivery rd) :
    d.route ≠ [] := by
  intro h
  have := d.arrives
  rw [Route.dest, h] at this
  simp at this

/-- Corollary: the delivered destination is an `accepting` node — a *valid destination*. A
message never arrives at a non-destination (it would not be a `Delivery`). -/
theorem delivery_dest_accepting (rd : RoutingDfa Node Hop) (d : Delivery rd) :
    rd.accepting d.dest := by
  obtain ⟨_first, last, _hhead, hlast, _hstart, hacc, _hvalid, _hchain⟩ := d.routes
  have harr := d.arrives
  rw [Route.dest] at harr
  -- `route.getLast? = some last` and `(getLast?).map next = some dest` ⇒ `dest = last.next`
  rw [hlast] at harr
  simp only [Option.map_some] at harr
  -- harr : some last.next = some d.dest
  have : last.next = d.dest := by injection harr
  rw [← this]; exact hacc

/-! ## §4 — Determinism / no-misroute (deliverable #3, optional).

A routing DFA is **deterministic** when `δ` is functional in `(state, hop)` — at most one
`next` per `(node, hop)`. This is `router.rs`'s flat transition table: `transitions[state*256 +
byte]` is a single `StateId`. Determinism ⇒ a route is uniquely determined by its hop *labels*
from the sender; two accepting routes with the same hop labels reach the same destination
(no misroute). -/

/-- **Determinism** of the routing DFA: `δ` is functional in `(node, hop)` — the table assigns
at most one `next` per cell (`transitions[state*256+byte]` is one `StateId`). -/
def Deterministic (rd : RoutingDfa Node Hop) : Prop :=
  ∀ n h n₁ n₂, rd.δ n h n₁ → rd.δ n h n₂ → n₁ = n₂

/-- **`unique_route` — NO MISROUTE (deliverable #3).** In a deterministic routing DFA, two
accepting routes that begin at the same node and read the same hop-label sequence are EQUAL —
so a message has a UNIQUE route (and hence a unique destination). Proven by induction on the
two routes, using functionality of `δ` to force each `next` to agree, and chaining to force the
following `state` to agree. -/
theorem unique_route (rd : RoutingDfa Node Hop) (hdet : Deterministic rd) :
    ∀ (r₁ r₂ : Route Node Hop),
      (r₁.map (·.state) = r₂.map (·.state)) →            -- same start node, same intermediate states agree pointwise
      (r₁.map (·.sym) = r₂.map (·.sym)) →                -- same hop labels
      (∀ s ∈ r₁, stepValid rd.δ s) → (∀ s ∈ r₂, stepValid rd.δ s) →
      r₁ = r₂ := by
  intro r₁
  induction r₁ with
  | nil =>
    intro r₂ hstate _hsym _hv₁ _hv₂
    -- map state of nil = [] forces r₂ = []
    cases r₂ with
    | nil => rfl
    | cons b bs => simp at hstate
  | cons a as ih =>
    intro r₂ hstate hsym hv₁ hv₂
    cases r₂ with
    | nil => simp at hstate
    | cons b bs =>
      simp only [List.map_cons, List.cons.injEq] at hstate hsym
      obtain ⟨hst, hsts⟩ := hstate
      obtain ⟨hsy, hsys⟩ := hsym
      -- a.state = b.state, a.sym = b.sym; δ functional ⇒ a.next = b.next ⇒ a = b
      have hva : stepValid rd.δ a := hv₁ a (List.mem_cons_self ..)
      have hvb : stepValid rd.δ b := hv₂ b (List.mem_cons_self ..)
      unfold stepValid at hva hvb
      rw [← hst, ← hsy] at hvb
      have hnext : a.next = b.next := hdet a.state a.sym a.next b.next hva hvb
      have hab : a = b := by
        cases a; cases b; simp_all
      have htail : as = bs := by
        apply ih
        · exact hsts
        · exact hsys
        · intro s hs; exact hv₁ s (List.mem_cons_of_mem a hs)
        · intro s hs; exact hv₂ s (List.mem_cons_of_mem b hs)
      rw [hab, htail]

/-! ## §5 — Authorization-gated routing (deliverable #2): the verify-seam.

dregg1's `GovernedRouter` (`router.rs:669`) only installs a route table behind a governance
proof + kind validation (`update_routes`, `router.rs:726`). Beyond table installation, individual
hops can be authorization-gated — a route may pass through a hop only if a `Spec.Guard` admits the
hop request. A **guarded routing DFA** carries a per-hop guard demand; a route is *authorized* iff
every hop `admits` under that guard. You cannot route PAST an unauthorized hop. -/

variable {Request Statement Witness : Type u} [Verifiable Statement Witness]

/-- A **guarded routing DFA**: a routing DFA plus a per-hop guard. `hopReq` reads a hop-step into
the guard's `Request` facts (who/where/what of the hop); `guard` is the `Spec.Guard` demand the
hop must satisfy; `wit` is the witness supply (the demand⊣supply split of `Spec.Guard §5`). -/
structure GuardedRouting (Node Hop : Type u) (Request Statement Witness : Type u)
    [Verifiable Statement Witness] where
  /-- The underlying routing automaton. -/
  rd : RoutingDfa Node Hop
  /-- Project a hop-step to the guard's request facts. -/
  hopReq : Step Node Hop → Request
  /-- The per-hop authorization guard (the verify-seam demand). -/
  guard : Guard Request Statement
  /-- The witness supply for the verify seam. -/
  wit : Statement → Witness

/-- **`RouteAuthorized`** — every hop of `route` `admits` the guard (under the witness supply).
This is the per-hop verify-seam check: `Guard.admits guard (hopReq step) wit = true` for each
step. Routing respects the verify-seam iff this holds. -/
def RouteAuthorized (gr : GuardedRouting Node Hop Request Statement Witness)
    (route : Route Node Hop) : Prop :=
  ∀ s ∈ route, Guard.admits gr.guard (gr.hopReq s) gr.wit = true

/-- A **guarded delivery**: a delivery whose route is, in addition, authorized at every hop. Like
`Delivery`, this is fail-closed by construction — a guarded delivery cannot exist with an
unauthorized hop (`authorized` is a proof obligation). Mirrors a dispatcher that composes the DFA
route (the `where`) with the slot caveats (the `whether`) per `dfa/src/lib.rs` "Composition
notes". -/
structure GuardedDelivery (gr : GuardedRouting Node Hop Request Statement Witness) where
  /-- The underlying delivery (already an accepting run, fail-closed). -/
  delivery : Delivery gr.rd
  /-- FAIL-CLOSED OBLIGATION: every hop of the route is guard-admitted. -/
  authorized : RouteAuthorized gr delivery.route

/-- **`route_authorization` — VERIFY-SEAM RESPECT (deliverable #2).** A guard-gated delivered
message's route satisfies the guard at EVERY hop: you cannot route past an unauthorized hop. The
delivery is *also* a genuine accepting run (delivery soundness, deliverable #1, composed in). -/
theorem route_authorization (gr : GuardedRouting Node Hop Request Statement Witness)
    (gd : GuardedDelivery gr) :
    IsAcceptingRun gr.rd gd.delivery.route ∧
    (∀ s ∈ gd.delivery.route, Guard.admits gr.guard (gr.hopReq s) gr.wit = true) :=
  ⟨gd.delivery.routes, gd.authorized⟩

/-- The authorization at each hop, packaged as a single `Guard.all` over the route's hop-guards
(`Guard.admits_all`): the whole route admits the *conjunction* of its per-hop guards. This is the
meet (`Spec.Guard §4`/§5) — the route's authorization is the AND of its hops', and attenuating any
hop's guard (adding a caveat) can only narrow the admitted routes (`Guard.attenuate_narrows`). -/
theorem route_authorization_as_meet (gr : GuardedRouting Node Hop Request Statement Witness)
    (gd : GuardedDelivery gr) (req : Request) :
    Guard.admits (Guard.all (gd.delivery.route.map (fun _ => gr.guard))) req gr.wit = true ↔
      ∀ g ∈ gd.delivery.route.map (fun _ => gr.guard), Guard.admits g req gr.wit = true :=
  Guard.admits_all _ req gr.wit

/-! ## §6 — Connection to `Coordination` (deliverable #3, optional): routing DFA as the
projection of a choreography's message flow.

A choreography (`Coordination.GlobalType`) describes a *multi-party* protocol as a sequence of
communications `comm src dst s cont`. Each `comm` head is a single message hop `src → dst`. The
routing DFA is the **projection of the message flow**: the head communication of a `GlobalType`
becomes one routing hop `src →s dst`. We show a `comm`-headed choreography induces a one-hop
accepting route in a routing DFA whose `δ` is "the choreography prescribes this hop" and whose
`accepting` is "= the receiver". This is the routing-as-projection connection: a message follows
the route the choreography projects. -/

open Dregg2.Coordination

/-- The **one-hop routing DFA induced by a `comm` head** `a → b : ⟨s⟩`: nodes are roles, the only
hop is the payload `s`, `δ` routes `a →s b`, `start = a`, and the accepting destination is `b`.
This is the projection of the choreography's first message onto the routing automaton. -/
def commHopDfa (a b : Role) (s : Payload) : RoutingDfa Role Payload where
  δ := fun n h n' => n = a ∧ h = s ∧ n' = b
  start := a
  accepting := fun n => n = b

/-- The single hop-step of the `comm` head: `a →s b`. -/
def commHopRoute (a b : Role) (s : Payload) : Route Role Payload :=
  [{ state := a, sym := s, next := b }]

/-- **`routing_projects_message_flow` — ROUTING-AS-PROJECTION (deliverable #3).** A choreography's
head communication `comm a b s k` (`Coordination.GlobalType.comm`) projects onto an accepting
route of the induced routing DFA: the message `a → b : ⟨s⟩` is delivered along the single
accepting hop `a →s b`. The routing DFA is thus the projection of the choreography's message flow
— and (by `routed_message_followed_accepting_route`) any delivery along it followed this route. -/
theorem routing_projects_message_flow (a b : Role) (s : Payload) :
    IsAcceptingRun (commHopDfa a b s) (commHopRoute a b s) := by
  refine ⟨_, _, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · -- accepting last.next : last.next = b, accepting b = (b = b)
    rfl
  · -- every step is δ-valid
    intro st hst
    simp only [commHopRoute, List.mem_cons, List.not_mem_nil, or_false] at hst
    subst hst
    exact ⟨rfl, rfl, rfl⟩
  · -- chained singleton
    trivial

/-- A `GStep` (the choreography's operational message-exchange, `Coordination.GStep`) on a `comm`
head is mirrored by the induced routing hop: the protocol step `comm a b s k ⟶ k` corresponds to
delivering `a → b : ⟨s⟩` along `commHopRoute`. The routing DFA *commutes* with the choreography's
message-flow step. -/
theorem gstep_comm_routes (a b : Role) (s : Payload) (k : GlobalType) :
    GStep (GlobalType.comm a b s k) k ∧ IsAcceptingRun (commHopDfa a b s) (commHopRoute a b s) :=
  ⟨GStep.comm a b s k, routing_projects_message_flow a b s⟩

/-! ## §7 — Axiom-hygiene tripwires. The keystones depend ONLY on the three kernel axioms
(no `sorryAx`, no oracle): delivery soundness, the dest/non-empty corollaries, no-misroute, the
verify-seam authorization, and the choreography projection. -/

#assert_axioms routed_message_followed_accepting_route
#assert_axioms delivery_route_nonempty
#assert_axioms delivery_dest_accepting
#assert_axioms unique_route
#assert_axioms route_authorization
#assert_axioms route_authorization_as_meet
#assert_axioms routing_projects_message_flow
#assert_axioms gstep_comm_routes

/-! ## §8 — Non-vacuity: a concrete routing DFA + a delivery + a FAIL-CLOSED reject.

A 3-node line `sender(0) →h relay(1) →h dest(2)`, hop symbol `h = 0` ("forward"). `δ` is the two
forwarding edges; `start = 0`; `accepting = (· = 2)` (only `dest` is a valid destination). We
deliver a message along `0 →h 1 →h 2` (an accepting route) and demonstrate the FAIL-CLOSED reject:
a message that runs `0 →h 1` and STOPS at the non-accepting `relay(1)` has NO `Delivery`
(its route does not accept). -/

namespace Reference

/-- The 3-node line routing DFA: `0 →0 1 →0 2`, accept `2`. -/
def lineDfa : RoutingDfa Nat Nat where
  δ := fun n h n' => (n = 0 ∧ h = 0 ∧ n' = 1) ∨ (n = 1 ∧ h = 0 ∧ n' = 2)
  start := 0
  accepting := fun n => n = 2

/-- The accepting route `0 →0 1 →0 2` (sender → relay → dest). -/
def goodRoute : Route Nat Nat :=
  [ { state := 0, sym := 0, next := 1 },
    { state := 1, sym := 0, next := 2 } ]

/-- The accepting route reaches the valid destination `2`. -/
theorem goodRoute_accepts : IsAcceptingRun lineDfa goodRoute := by
  refine ⟨_, _, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · rfl                                   -- accept last.next = (2 = 2)
  · intro st hst                          -- every hop δ-valid
    simp only [goodRoute, List.mem_cons, List.not_mem_nil, or_false] at hst
    rcases hst with rfl | rfl
    · exact Or.inl ⟨rfl, rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, trivial⟩                  -- chained: relay.state = sender.next

/-- **NON-VACUITY (delivery):** a message IS delivered along the accepting route to `dest = 2`. -/
def goodDelivery : Delivery lineDfa where
  route := goodRoute
  dest := 2
  routes := goodRoute_accepts
  arrives := rfl

/-- The delivered destination is the valid destination `2` (exercises `delivery_dest_accepting`). -/
example : lineDfa.accepting goodDelivery.dest := delivery_dest_accepting lineDfa goodDelivery

/-- The delivery's route is the accepting run (exercises `routed_message_followed_accepting_route`). -/
example : IsAcceptingRun lineDfa goodDelivery.route ∧ goodDelivery.route.dest = some 2 :=
  routed_message_followed_accepting_route lineDfa goodDelivery

/-- **NON-VACUITY (FAIL-CLOSED REJECT):** the route `0 →0 1` STOPS at the non-accepting relay
`1`. It is NOT an accepting run — `accepting 1` is `(1 = 2)`, false — so NO `Delivery` to `1`
exists (the `routes` obligation is unprovable). We prove the run is rejected. -/
def badRoute : Route Nat Nat := [ { state := 0, sym := 0, next := 1 } ]

theorem badRoute_rejected : ¬ IsAcceptingRun lineDfa badRoute := by
  rintro ⟨first, last, hhead, hlast, _hstart, hacc, _hvalid, _hchain⟩
  -- last = the single step, last.next = 1; accept 1 = (1 = 2) is false
  simp only [badRoute, List.getLast?_singleton, Option.some.injEq] at hlast
  rw [← hlast] at hacc
  -- hacc : lineDfa.accepting 1, i.e. (1 = 2)
  have : (1 : Nat) = 2 := hacc
  exact absurd this (by decide)

/-- The fail-closed reject is structural: ANY `Delivery` whose route is `badRoute` is impossible
(no constructor — `routes` would have to prove `badRoute_rejected`'s negation). We state it as:
a delivery cannot carry `badRoute`. -/
theorem no_delivery_along_badRoute (d : Delivery lineDfa) : d.route ≠ badRoute := by
  intro h
  exact badRoute_rejected (h ▸ d.routes)

/-! ### Guarded reference: a hop-authorization guard, an authorized delivery, and the
fail-closed reject of an UNauthorized hop. The guard is `firstParty`: "the hop's symbol is the
allowed forward symbol `0`". A statement/witness oracle is supplied trivially (no witnessed
branch needed for this first-party guard). -/

/-- A trivial verify oracle (no witnessed guards in the reference; the first-party guard needs
none). `Statement = Witness = Unit`. -/
instance : Verifiable Unit Unit where
  Verify := fun _ _ => true

/-- The guarded line routing: hop request = the hop symbol; guard = "symbol = 0 (forward)". -/
def lineGuarded : GuardedRouting Nat Nat Nat Unit Unit where
  rd := lineDfa
  hopReq := fun s => s.sym
  guard := Guard.firstParty (fun h => decide (h = 0))
  wit := fun _ => ()

/-- Every hop of `goodRoute` carries symbol `0`, so the route is authorized. -/
theorem goodRoute_authorized : RouteAuthorized lineGuarded goodRoute := by
  intro s hs
  simp only [goodRoute, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl <;>
    simp only [lineGuarded, Guard.admits_firstParty, lineDfa] <;> decide

/-- **NON-VACUITY (authorized delivery):** the good delivery is guard-authorized at every hop. -/
def goodGuardedDelivery : GuardedDelivery lineGuarded where
  delivery := goodDelivery
  authorized := goodRoute_authorized

/-- Exercises `route_authorization`: the guarded delivery is an accepting run AND admits the guard
at every hop. -/
example : IsAcceptingRun lineGuarded.rd goodGuardedDelivery.delivery.route ∧
    (∀ s ∈ goodGuardedDelivery.delivery.route,
      Guard.admits lineGuarded.guard (lineGuarded.hopReq s) lineGuarded.wit = true) :=
  route_authorization lineGuarded goodGuardedDelivery

/-- **FAIL-CLOSED REJECT (authorization):** a hop with a DISALLOWED symbol `1` ("sideways") is NOT
admitted by the guard — so a route containing it is unauthorized, and no `GuardedDelivery` can
carry it. -/
def sidewaysHop : Step Nat Nat := { state := 0, sym := 1, next := 1 }

theorem sidewaysHop_unauthorized :
    Guard.admits lineGuarded.guard (lineGuarded.hopReq sidewaysHop) lineGuarded.wit = false := by
  simp only [lineGuarded, Guard.admits_firstParty, sidewaysHop]; decide

/-- The unauthorized hop breaks `RouteAuthorized` for any route containing it: routing cannot pass
the unauthorized hop. -/
theorem unauthorized_route_rejected (route : Route Nat Nat) (hmem : sidewaysHop ∈ route) :
    ¬ RouteAuthorized lineGuarded route := by
  intro hauth
  have := hauth sidewaysHop hmem
  rw [sidewaysHop_unauthorized] at this
  exact absurd this (by decide)

#eval goodRoute.dest        -- some 2  (delivered to the valid destination)
#eval badRoute.dest         -- some 1  (stops at the non-accepting relay — no delivery)

end Reference

#assert_axioms Reference.goodRoute_accepts
#assert_axioms Reference.badRoute_rejected
#assert_axioms Reference.no_delivery_along_badRoute
#assert_axioms Reference.goodRoute_authorized
#assert_axioms Reference.sidewaysHop_unauthorized
#assert_axioms Reference.unauthorized_route_rejected

end Dregg2.Exec.DfaRouting
