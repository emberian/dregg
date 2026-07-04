/-!
# 0-RTT anti-replay on a sharded server — the model

TLS 1.3 0-RTT early data is replayable by an on-path attacker: the
ClientHello + early data flight can be copied and re-delivered arbitrarily
(RFC 8446 Appendix E.5; RFC 9001 §4.9.1 and §9.2). A single-process server
defeats this with a strike register — accept a resumption ticket's early
data at most once. On a **shared-nothing sharded** server (per-core
engines, no shared memory) a naive strike register breaks: the attacker
simply replays the flight toward a *different* shard, and per-shard
registers each accept "for the first time".

This model renders the sharded design that repairs the property:

* **Single-owner tickets.** Each resumption ticket is minted by exactly
  one shard — its *owner* — and the owner's identity is embedded in the
  server-chosen connection ID the resumption rides on, so normal steering
  routes a resumption attempt back to its owner. Client-visibly tickets
  roam freely; owner affinity is a routing detail (`Cfg.owner` is a static
  minting map).
* **Core-local strike register.** Only the owner ever consults or updates
  the register for its tickets; a register write is the *decision* for
  that ticket.
* **Mis-steer ⇒ asynchronous owner-check.** A resumption landing on a
  non-owner shard (load-balancer re-hash, topology change) is *not*
  rejected: the receiving shard holds the early data and sends the owner
  an owner-check message; the owner decides against its own register and
  answers with a strike-ack (`ok = true`: accept) or strike-nack. The
  anti-replay decision is per *connection attempt*, not per packet, so
  this one message rides the handshake path only.
* **Owner gone ⇒ decline.** If the owner is unreachable (crash, resize,
  migration), the held early data is declined and the connection falls
  back to 1-RTT — a latency regression, never a second accept.

The adversary is demonic where the world is demonic:

* the **network** may replay any early-data attempt to **any** shard,
  any number of times, in any interleaving (the `localAccept` /
  `localReject` / `forward` moves are unboundedly enabled);
* shards may **crash** at any moment (crash is permanent for a shard
  identity — a rebooted core comes back empty and mints under a fresh
  identity, so it never resurrects a lost register);
* the **inter-shard ring** may drop any message at any time (`lose`),
  and any wait may time out (`timeout`) — but it does **not duplicate**
  messages: the transport between shards is a point-to-point SPSC ring,
  not the attacker's network. This non-duplication is the one seam
  assumption the theorem stands on, and it is discharged by the ring
  implementation, not by this model.

`Quic.ReplayTheorems` proves the headline: **across all shards and all
interleavings, each ticket's early data is accepted at most once**
(`accepted_at_most_once`), by single-owner serialization — plus the
owner-gone and mis-steer corollaries.
-/

namespace Quic.Replay

/-- Ticket identity (the resumption ticket / its PSK identity). -/
abbrev TicketId := Nat

/-- Shard identity (one per-core engine). -/
abbrev Shard := Nat

/-- Connection-attempt identity: distinguishes distinct early-data
attempts carrying the same ticket (replays included). -/
abbrev AttemptId := Nat

/-- The static minting map: the owner shard embedded in the server-chosen
connection ID a resumption ticket rides on. Fixed at mint time. -/
structure Cfg where
  owner : TicketId → Shard

/-- In-flight inter-shard traffic: owner-check requests and strike-ack /
strike-nack responses. `requester` is the mis-steered shard holding the
early data; `a` names its connection attempt. -/
inductive Wire where
  | req (t : TicketId) (requester : Shard) (a : AttemptId)
  | resp (t : TicketId) (requester : Shard) (a : AttemptId) (ok : Bool)
deriving Repr, DecidableEq

/-- Global state: the per-shard strike registers (as the set of
`(shard, ticket)` marks — only ever grown, and only by the owner shard),
the crashed shards, and the in-flight inter-shard messages. -/
structure St where
  used : List (Shard × TicketId)
  dead : List Shard
  wires : List Wire
deriving Repr, DecidableEq

/-- Initial state: registers empty, everything alive, nothing in flight. -/
def init : St := { used := [], dead := [], wires := [] }

/-- Transition labels. Accept events are observable as `localAccept`
(correctly-steered path: the owner decides on arrival) and `acceptRemote`
(mis-steered path: a strike-ack arrived back). Decline events are
`localReject` / `declineRemote` / `timeout` — all fall back to 1-RTT. -/
inductive Lbl where
  /-- An early-data attempt for `t` arrived at its live owner and the
  register had no mark: mark and **accept**. -/
  | localAccept (t : TicketId) (a : AttemptId)
  /-- An early-data attempt for `t` arrived at its live owner and the
  register was already marked: decline to 1-RTT. -/
  | localReject (t : TicketId) (a : AttemptId)
  /-- An early-data attempt for `t` arrived at live non-owner shard `s`
  (mis-steer): hold the early data, send the owner an owner-check. -/
  | forward (t : TicketId) (s : Shard) (a : AttemptId)
  /-- The live owner processes an owner-check for `t` from `s`, register
  unmarked: mark, answer with a strike-ack. -/
  | ownerOk (t : TicketId) (s : Shard) (a : AttemptId)
  /-- The live owner processes an owner-check for `t` from `s`, register
  already marked: answer with a strike-nack. -/
  | ownerNo (t : TicketId) (s : Shard) (a : AttemptId)
  /-- A strike-ack reached live requester `s`: **accept** the held early
  data of attempt `a`. -/
  | acceptRemote (t : TicketId) (s : Shard) (a : AttemptId)
  /-- A strike-nack reached requester `s`: decline to 1-RTT. -/
  | declineRemote (t : TicketId) (s : Shard) (a : AttemptId)
  /-- Requester `s` gave up waiting (owner gone, message lost, or just
  slow): decline attempt `a` to 1-RTT. Always enabled. -/
  | timeout (t : TicketId) (s : Shard) (a : AttemptId)
  /-- Shard `s` dies. Permanent for this shard identity. -/
  | crash (s : Shard)
  /-- The inter-shard ring drops message `w`. -/
  | lose (w : Wire)
deriving Repr, DecidableEq

/-- The transition relation: a demonic scheduler/attacker chooses any
enabled move. Early-data arrivals are fused into the decision moves
(`localAccept`/`localReject`/`forward`), which are enabled unboundedly —
this *is* the replay adversary: any ticket, any shard, any attempt id,
any number of times. -/
inductive Step (cfg : Cfg) : St → Lbl → St → Prop where
  | localAccept {s : St} {t : TicketId} {a : AttemptId}
      (halive : cfg.owner t ∉ s.dead)
      (hnew : (cfg.owner t, t) ∉ s.used) :
      Step cfg s (.localAccept t a)
        { s with used := (cfg.owner t, t) :: s.used }
  | localReject {s : St} {t : TicketId} {a : AttemptId}
      (halive : cfg.owner t ∉ s.dead)
      (hused : (cfg.owner t, t) ∈ s.used) :
      Step cfg s (.localReject t a) s
  | forward {s : St} {t : TicketId} {sh : Shard} {a : AttemptId}
      (hmiss : sh ≠ cfg.owner t)
      (halive : sh ∉ s.dead) :
      Step cfg s (.forward t sh a)
        { s with wires := s.wires ++ [.req t sh a] }
  | ownerOk {s : St} {t : TicketId} {sh : Shard} {a : AttemptId}
      {w₁ w₂ : List Wire}
      (halive : cfg.owner t ∉ s.dead)
      (hwire : s.wires = w₁ ++ .req t sh a :: w₂)
      (hnew : (cfg.owner t, t) ∉ s.used) :
      Step cfg s (.ownerOk t sh a)
        { s with used := (cfg.owner t, t) :: s.used,
                 wires := w₁ ++ w₂ ++ [.resp t sh a true] }
  | ownerNo {s : St} {t : TicketId} {sh : Shard} {a : AttemptId}
      {w₁ w₂ : List Wire}
      (halive : cfg.owner t ∉ s.dead)
      (hwire : s.wires = w₁ ++ .req t sh a :: w₂)
      (hused : (cfg.owner t, t) ∈ s.used) :
      Step cfg s (.ownerNo t sh a)
        { s with wires := w₁ ++ w₂ ++ [.resp t sh a false] }
  | acceptRemote {s : St} {t : TicketId} {sh : Shard} {a : AttemptId}
      {w₁ w₂ : List Wire}
      (halive : sh ∉ s.dead)
      (hwire : s.wires = w₁ ++ .resp t sh a true :: w₂) :
      Step cfg s (.acceptRemote t sh a) { s with wires := w₁ ++ w₂ }
  | declineRemote {s : St} {t : TicketId} {sh : Shard} {a : AttemptId}
      {w₁ w₂ : List Wire}
      (hwire : s.wires = w₁ ++ .resp t sh a false :: w₂) :
      Step cfg s (.declineRemote t sh a) { s with wires := w₁ ++ w₂ }
  | timeout {s : St} {t : TicketId} {sh : Shard} {a : AttemptId} :
      Step cfg s (.timeout t sh a) s
  | crash {s : St} {sh : Shard} :
      Step cfg s (.crash sh) { s with dead := sh :: s.dead }
  | lose {s : St} {w : Wire} {w₁ w₂ : List Wire}
      (hwire : s.wires = w₁ ++ w :: w₂) :
      Step cfg s (.lose w) { s with wires := w₁ ++ w₂ }

/-- Finite traces. -/
inductive Trace (cfg : Cfg) : St → List Lbl → St → Prop where
  | nil {s : St} : Trace cfg s [] s
  | cons {s s' s'' : St} {l : Lbl} {ls : List Lbl}
      (h : Step cfg s l s') (t : Trace cfg s' ls s'') :
      Trace cfg s (l :: ls) s''

/-- Reachability from the initial state. -/
def Reachable (cfg : Cfg) (s : St) : Prop :=
  ∃ ls, Trace cfg init ls s

/-- Is this label an accept of ticket `t`' early data (either path)? -/
def Lbl.isAccept (t : TicketId) : Lbl → Bool
  | .localAccept t' _ => t' == t
  | .acceptRemote t' _ _ => t' == t
  | _ => false

/-- Is this label an owner *decision* for ticket `t` (the register
write)? Exactly the two moves guarded by `hnew`. -/
def Lbl.isDecision (t : TicketId) : Lbl → Bool
  | .localAccept t' _ => t' == t
  | .ownerOk t' _ _ => t' == t
  | _ => false

/-- Number of accepts of ticket `t`' early data in a trace. -/
def accepts (t : TicketId) (ls : List Lbl) : Nat :=
  ls.countP (Lbl.isAccept t)

/-- Number of owner decisions for ticket `t` in a trace. -/
def decisions (t : TicketId) (ls : List Lbl) : Nat :=
  ls.countP (Lbl.isDecision t)

/-- Is this wire a strike-ack for ticket `t`? -/
def Wire.isOk (t : TicketId) : Wire → Bool
  | .resp t' _ _ ok => t' == t && ok
  | _ => false

/-- In-flight strike-acks for ticket `t`. -/
def okWires (t : TicketId) (s : St) : Nat :=
  s.wires.countP (Wire.isOk t)

/-- Whether the owner's register carries the mark for `t` (0 or 1): the
single decision token of the whole design. -/
def struck (cfg : Cfg) (t : TicketId) (s : St) : Nat :=
  if (cfg.owner t, t) ∈ s.used then 1 else 0

end Quic.Replay
