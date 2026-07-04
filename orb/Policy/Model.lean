/-
Policy — the declared-surface admission model (cold plane).

A running network node has two planes.  The *hot* plane moves bytes per packet.
The *cold* plane answers the question this file is about: what may the node
listen on, serve, and admit, and does the running state ever exceed what its
configuration declares?  The property proved here — every observable action is
covered by the live configuration — is what older notes called the
*confinement* theorem, restated concretely as a transition-system invariant.

The model is a small state machine.

  * `Config`   — the declared surface: a list of listeners (address, port, a
                 TLS-required flag, a per-listener connection cap) and a list of
                 routes (a host/path key to a handler reference).  This is the
                 single source of truth for "what is declared".

  * `Running`  — the live state: the set of currently-bound listeners, the set
                 of listeners with an active TLS context, a per-listener live
                 connection count, one live `Config` *snapshot*, and an
                 append-only log of served responses (the observations the
                 invariants range over).

  * transitions — `accept` (admit one connection under the cap), `serve`
                 (emit one response, enforce-or-refuse on the TLS-required and
                 route-declared gates), `reload` (swap the whole config snapshot
                 in one step), and `adopt` (bind a declared listener into the
                 running set, reusing rather than re-binding).

Everything is a pure function of an explicit state; a transition is one atomic
step.  The reload is modelled as the single whole-snapshot swap it is: one
field replaced wholesale, never field-by-field, so no reader can observe a
config that mixes the old and new snapshots.
-/

namespace Policy

/-- A route key: an abstract host and path identity.  Concrete hosts/paths are
irrelevant to the admission invariants, so they are opaque `Nat` identities. -/
structure RouteKey where
  host : Nat
  path : Nat
deriving DecidableEq, Repr

/-- One declared route: a key resolving to a handler/upstream reference. -/
structure RouteCfg where
  key : RouteKey
  /-- Handler / upstream reference (opaque identity). -/
  handler : Nat
deriving DecidableEq, Repr

/-- One declared listener.  `id` is the stable identity a listener keeps across
a reload (adoption reuses it); `addr`/`port` are its bind address; `tlsRequired`
is the enforce-TLS flag; `connCap` is the per-listener admission bound. -/
structure ListenerCfg where
  id : Nat
  addr : Nat
  port : Nat
  tlsRequired : Bool
  connCap : Nat
deriving DecidableEq, Repr

/-- The declared surface. -/
structure Config where
  listeners : List ListenerCfg
  routes : List RouteCfg
deriving DecidableEq, Repr

/-- The declared listener with a given id, if any (first match). -/
def Config.listener? (c : Config) (lid : Nat) : Option ListenerCfg :=
  c.listeners.find? (fun l => l.id == lid)

/-- `c` declares a listener with id `lid`. -/
def Config.declaresListener (c : Config) (lid : Nat) : Prop :=
  (c.listener? lid).isSome

/-- `c` declares a listener with id `lid` that requires TLS. -/
def Config.tlsListener (c : Config) (lid : Nat) : Prop :=
  ∃ l, c.listener? lid = some l ∧ l.tlsRequired = true

/-- `c` declares a route for key `rk`. -/
def Config.declaresRoute (c : Config) (rk : RouteKey) : Bool :=
  c.routes.any (fun r => decide (r.key = rk))

/-- One served response, as observed: the listener it is attributed to, the
route key it matched, and whether it went out as plaintext (no TLS). -/
structure Served where
  lid : Nat
  route : RouteKey
  plaintext : Bool
deriving DecidableEq, Repr

/-- The live running state.

`live` is a total map (listener id → current live connection count); listeners
that are not bound sit at `0` (invariant `unboundZero`).  The config snapshot is
a single field — the atomic unit a reload swaps. -/
structure Running where
  /-- The live config snapshot. -/
  cfg : Config
  /-- Currently-bound listener ids (no duplicates: invariant `boundNodup`). -/
  bound : List Nat
  /-- Listener ids with an active TLS context. -/
  tlsCtx : List Nat
  /-- Per-listener live connection count. -/
  live : Nat → Nat
  /-- Append-only log of served responses (the observations). -/
  served : List Served

/-- Cold boot: the declared config, nothing bound yet, all counts zero. -/
def init (c : Config) : Running where
  cfg := c
  bound := []
  tlsCtx := []
  live := fun _ => 0
  served := []

/-! ### Transitions -/

/-- Increment the count at one listener id, leaving the rest untouched. -/
def bumpAt (lid : Nat) (f : Nat → Nat) : Nat → Nat :=
  fun k => if k = lid then f k + 1 else f k

@[simp] theorem bumpAt_self (lid : Nat) (f : Nat → Nat) :
    bumpAt lid f lid = f lid + 1 := by simp [bumpAt]

theorem bumpAt_other {lid k : Nat} (f : Nat → Nat) (h : k ≠ lid) :
    bumpAt lid f k = f k := by simp [bumpAt, h]

/-- Admit one connection on listener `lid`.  Refuses (stutters) unless the
listener is declared, bound, and strictly below its cap — so the live count is
never pushed above the declared cap. -/
def accept (lid : Nat) (st : Running) : Running :=
  match st.cfg.listener? lid with
  | none => st
  | some l =>
      if lid ∈ st.bound ∧ st.live lid < l.connCap then
        { st with live := bumpAt lid st.live }
      else st

/-- The serve gate.  Returns the observation to record, or `none` to refuse.
Enforce-or-refuse:

  * an undeclared or unbound listener serves nothing;
  * a TLS-required listener refuses a plaintext response (never downgrades);
  * a TLS-required listener refuses until its TLS context is active;
  * an undeclared route serves nothing. -/
def serveDecision (lid : Nat) (rk : RouteKey) (plaintext : Bool)
    (st : Running) : Option Served :=
  match st.cfg.listener? lid with
  | none => none
  | some l =>
      if lid ∉ st.bound then none
      else if l.tlsRequired = true ∧ plaintext = true then none
      else if l.tlsRequired = true ∧ lid ∉ st.tlsCtx then none
      else if st.cfg.declaresRoute rk = false then none
      else some ⟨lid, rk, plaintext⟩

/-- Serve one response on listener `lid` for route key `rk`.  Only a request
that passes every gate (`serveDecision`) appends an observation; a refused
request stutters. -/
def serve (lid : Nat) (rk : RouteKey) (plaintext : Bool) (st : Running) : Running :=
  match serveDecision lid rk plaintext st with
  | none => st
  | some s => { st with served := s :: st.served }

/-- The listener-adoption precondition for a reload to `c'`: every currently-
bound listener's declared entry is carried across *identically* (adopted, not
re-bound).  Routes may change freely; a bound listener's bind parameters may
not — changing them is a re-bind, not a hot reload. -/
def adoptableB (c' : Config) (st : Running) : Bool :=
  st.bound.all (fun lid => decide (c'.listener? lid = st.cfg.listener? lid))

/-- Reload: the single whole-snapshot swap.  When the adoption precondition
holds the live config field is replaced wholesale by `c'`; otherwise the old
config is retained.  Nothing else in the state moves — the bound set, TLS
contexts, live counts and observation log are untouched, so no reader sees a
listener transiently unbound or double-bound, and no reader sees a config that
mixes the two snapshots. -/
def reload (c' : Config) (st : Running) : Running :=
  if adoptableB c' st then { st with cfg := c' } else st

/-- Adopt a declared listener into the bound set, reusing its declared identity
rather than re-binding.  Refuses if the listener is already bound (no
double-bind) or is not declared.  A newly-adopted listener starts at zero live
connections and gets an active TLS context exactly when it is TLS-required. -/
def adopt (lid : Nat) (st : Running) : Running :=
  if lid ∈ st.bound then st
  else match st.cfg.listener? lid with
    | none => st
    | some l =>
        { st with
          bound := lid :: st.bound,
          tlsCtx := if l.tlsRequired then lid :: st.tlsCtx else st.tlsCtx }

/-- One step of the machine is any of the four transitions. -/
inductive Step : Running → Running → Prop where
  | accept (lid : Nat) (st : Running) : Step st (accept lid st)
  | serve (lid : Nat) (rk : RouteKey) (pt : Bool) (st : Running) : Step st (serve lid rk pt st)
  | reload (c' : Config) (st : Running) : Step st (reload c' st)
  | adopt (lid : Nat) (st : Running) : Step st (adopt lid st)

/-- States reachable from a cold boot by any sequence of steps. -/
inductive Reachable (c : Config) : Running → Prop where
  | init : Reachable c (init c)
  | step {st st' : Running} : Reachable c st → Step st st' → Reachable c st'

end Policy
