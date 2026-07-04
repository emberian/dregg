/-!
# A submission/completion ring, modeled as a two-player LTS — core types

This file gives the state space for a labeled transition system modeling a
kernel submission/completion ring (SQ/CQ pair with provided-buffer rings,
multishot receive, linked submissions, and completion-queue overflow).

Two players act on the state:

* the **client** (the code under verification): submits operations, reaps
  completions in queue order, recycles buffer ids it holds, publishes the
  buffer-ring tail, re-arms multishot receives;
* the **environment** (the kernel side, *demonic*): completes in-flight
  operations in any order compatible with link chains, delivers multishot
  completion streams, binds one buffer id per buffer-select completion,
  signals buffer exhaustion (`ENOBUFS`) at any moment, delivers data-with-
  no-buffer completions, and — when the completion queue is full — either
  retains completions in an overflow list (`nodrop` feature present) or
  silently drops them (`nodrop` absent).

The verification target is the buffer-lease lifecycle: every buffer id the
environment lends via a buffer-select completion is recycled exactly once by
the client — no double recycle, no leak — under every demonic interleaving,
including exhaustion/re-arm boundaries. See `Uring.Conservation` and
`Uring.RecycleOnce` for the theorems and `Uring.Counterexample` for the
named counterexample when the `nodrop` feature is absent.
-/

namespace Uring

/-- Buffer id (`bid`) in a provided-buffer ring. -/
abbrev Bid := Nat

/-- File descriptor identifying a stream (socket). -/
abbrev Fd := Nat

/-- Operation token (the `user_data` correlator carried from SQE to CQE). -/
abbrev OpId := Nat

/-- What kind of operation an SQE requests. Minimal but demonically honest:
one-shot ops (send/read/nop class), multishot buffer-select receive, and
close (which may race in-flight ops on the same fd). -/
inductive OpKind where
  /-- A one-shot operation: yields exactly one plain completion. -/
  | oneshot
  /-- Multishot buffer-select receive on `fd`: yields a stream of
  completions, each binding one buffer id, until a final completion with
  the more-flag cleared. -/
  | recvMulti (fd : Fd)
  /-- Close `fd`. Deliberately does **not** cancel in-flight operations on
  `fd`: the environment may complete them, or keep delivering on an armed
  multishot, after the close completes (stale-completion edges). -/
  | close (fd : Fd)
deriving DecidableEq, Repr

/-- A submission-queue entry. `pred` encodes a link chain: the environment
may not complete this op while `pred` is still in flight. -/
structure Sqe where
  id   : OpId
  kind : OpKind
  pred : Option OpId := none
deriving DecidableEq, Repr

/-- The payload of a completion-queue entry. -/
inductive Payload where
  /-- Completion of a non-buffer op (one-shot, close). -/
  | plain
  /-- Buffer-select receive completion: the kernel bound buffer `b` and
  lends it to the client. This is the lease-granting event. -/
  | buf (b : Bid)
  /-- Data arrived on `fd` but no buffer could be bound: the data is
  irrecoverably lost. The client discipline kills this stream. -/
  | bufferless (fd : Fd)
  /-- Buffer exhaustion (`ENOBUFS`) on `fd`: the multishot terminates
  (more-flag cleared) and the client must re-arm. -/
  | enobufs (fd : Fd)
deriving DecidableEq, Repr

/-- The buffer id a payload carries, if any. -/
def Payload.bid? : Payload → Option Bid
  | .buf b => some b
  | _ => none

/-- A completion-queue entry. `more = true` means the multishot that
produced it remains armed. -/
structure Cqe where
  id      : OpId
  payload : Payload
  more    : Bool
deriving DecidableEq, Repr

/-- Static ring configuration. -/
structure Cfg where
  /-- Number of buffer ids in the provided-buffer ring: the bid universe is
  `[0, nbufs)`. -/
  nbufs : Nat
  /-- Completion-queue capacity; completions beyond it overflow. -/
  cqCap : Nat
  /-- Whether the ring advertises the no-drop feature: a full completion
  queue retains further completions kernel-side instead of dropping them. -/
  nodrop : Bool
deriving DecidableEq, Repr

/-- LTS state: what both players can jointly observe/affect.

Buffer-ring publication is explicit: `recycle` puts a bid in `pending`
(ring entry written, tail not yet advanced); only `publish` (the tail
store) makes it visible to the environment in `free`. Exhaustion can
therefore strike while the client sits on recycled-but-unpublished
entries — the interleavings the property must survive. -/
structure St where
  /-- Next fresh `user_data` token (client-owned counter). -/
  nextId   : OpId
  /-- Submitted, not yet finally completed (SQ side; submission here is
  write+publish fused, since splitting the SQ tail store adds no behavior
  visible to the buffer-lease property). -/
  inflight : List Sqe
  /-- The completion queue, in kernel publication order (client reaps the
  head). -/
  cq       : List Cqe
  /-- Kernel-retained overflow completions (`nodrop` feature only). -/
  ovf      : List Cqe
  /-- Count of completions silently dropped on overflow (no `nodrop`). -/
  dropped  : Nat
  /-- Published free buffer ids: ring entries below the published tail,
  available for the environment to bind. -/
  free     : List Bid
  /-- Recycled but unpublished buffer ids (tail not yet advanced). -/
  pending  : List Bid
  /-- Buffer ids the client holds: lease reaped, not yet recycled. -/
  held     : List Bid
  /-- Streams the client has killed (after a bufferless completion). -/
  dead     : List Fd
deriving DecidableEq, Repr

/-- Initial state for a configuration: all buffer ids published and free,
nothing in flight, nothing armed. -/
def init (cfg : Cfg) : St :=
  { nextId := 0, inflight := [], cq := [], ovf := [], dropped := 0
    free := List.range cfg.nbufs, pending := [], held := [], dead := [] }

/-! ## Bid accounting

`owned` collects, as a list-multiset, every location a buffer id can
inhabit from the client+kernel joint perspective: published free entries,
recycled-unpublished entries, client-held leases, and leases riding
unreaped completions (queued or kernel-retained overflow). The
conservation theorem says each bid of the universe occurs exactly once in
`owned` — which is simultaneously no-leak and no-duplication. -/

/-- Buffer ids carried by a list of completions. -/
def cqBids (l : List Cqe) : List Bid :=
  l.filterMap fun c => c.payload.bid?

@[simp] theorem cqBids_nil : cqBids [] = [] := rfl

@[simp] theorem cqBids_cons (c : Cqe) (l : List Cqe) :
    cqBids (c :: l) = c.payload.bid?.toList ++ cqBids l := by
  cases h : c.payload.bid? <;> simp [cqBids, List.filterMap_cons, h]

@[simp] theorem cqBids_append (l₁ l₂ : List Cqe) :
    cqBids (l₁ ++ l₂) = cqBids l₁ ++ cqBids l₂ :=
  List.filterMap_append l₁ l₂ _

/-- Every location a bid can legitimately inhabit, as one multiset. -/
def owned (s : St) : List Bid :=
  s.free ++ s.pending ++ s.held ++ cqBids s.cq ++ cqBids s.ovf

/-- The client-facing locations of a bid: held leases plus leases riding
unreaped completions. Zero here means the bid is at rest (free or pending)
or leaked; in particular no recycle of it can be enabled until the
environment lends it again. -/
def hot (s : St) (b : Bid) : Nat :=
  (s.held ++ cqBids s.cq ++ cqBids s.ovf).count b

/-- Count of `b` in the whole bid universe. -/
theorem count_range (n b : Nat) :
    (List.range n).count b = if b < n then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.count_append, ih, List.count_singleton]
    rcases Nat.lt_trichotomy b n with h | h | h
    · simp [Nat.ne_of_gt h, Nat.lt_succ_of_lt h, h]
    · subst h; simp
    · have h1 : ¬ b < n := Nat.not_lt.mpr (Nat.le_of_lt h)
      have h2 : ¬ b < n + 1 := Nat.not_lt.mpr h
      have h3 : n ≠ b := Nat.ne_of_lt h
      simp [h1, h2, h3]

@[simp] theorem count_owned_init (cfg : Cfg) (b : Bid) :
    (owned (init cfg)).count b = if b < cfg.nbufs then 1 else 0 := by
  simp [owned, init, count_range]

end Uring
