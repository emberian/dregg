import Uring.Basic

/-!
# The two-player labeled transition system

Client moves carry the client discipline as guards (this *is* the protocol
under verification); environment moves are guarded only by what the ring
interface contract itself permits — anything else may happen, in any
interleaving. In particular the environment may:

* complete any in-flight one-shot in any order compatible with link chains;
* deliver buffer-select completions on any armed multishot, choosing *any*
  published free entry (a superset of the FIFO ring contract — proving
  against the superset only strengthens the result);
* end a multishot stream at any completion (more-flag cleared);
* signal `ENOBUFS` **at any moment**, even when published entries exist
  (internal ring lag / racing consumers), terminating the multishot;
* deliver data with no buffer bound (the irrecoverable-loss completion);
* overflow: when the completion queue is at capacity, a further completion
  is retained kernel-side if `nodrop` is advertised, else silently dropped.
-/

namespace Uring

/-- Where a freshly produced completion goes: the queue if there is room;
otherwise the kernel-retained overflow list when `nodrop` is advertised;
otherwise it is silently dropped (counted only). This is the sole edge on
which a buffer id can vanish. -/
def post (cfg : Cfg) (s : St) (c : Cqe) : St :=
  if s.cq.length < cfg.cqCap then { s with cq := s.cq ++ [c] }
  else if cfg.nodrop then { s with ovf := s.ovf ++ [c] }
  else { s with dropped := s.dropped + 1 }

/-- Client dispatch on reaping completion `c` (the drain loop body):
a buffer lease is taken into `held`; a bufferless completion kills its
stream; plain and `ENOBUFS` completions carry no state beyond enabling
re-arm. -/
def dispatch (s : St) (c : Cqe) : St :=
  match c.payload with
  | .plain => s
  | .buf b => { s with held := b :: s.held }
  | .bufferless fd => { s with dead := fd :: s.dead }
  | .enobufs _ => s

/-- Client submission discipline per op kind: a multishot receive may not
be armed on a killed stream nor double-armed. (Initial arm and post-
`ENOBUFS` re-arm are the same edge; re-arming is enabled precisely because
exhaustion removed the op from flight.) -/
def kindOk (q : Sqe) (s : St) : Prop :=
  match q.kind with
  | .recvMulti fd => fd ∉ s.dead ∧ ∀ r ∈ s.inflight, r.kind ≠ OpKind.recvMulti fd
  | _ => True

/-- A link predecessor must name an op still in flight at submission. -/
def predOk (q : Sqe) (s : St) : Prop :=
  match q.pred with
  | none => True
  | some p => p ∈ s.inflight.map Sqe.id

/-- Link-chain guard for completion: an op may complete only once its
predecessor is no longer in flight. -/
def linkFree (q : Sqe) (rest : List Sqe) : Prop :=
  match q.pred with
  | none => True
  | some p => p ∉ rest.map Sqe.id

/-- Transition labels. Client: `submit`, `reap`, `recycle`, `publish`.
Environment: `complete`, `deliver`, `starve`, `exhaust`, `flush`. -/
inductive Lbl where
  | submit (q : Sqe)
  | reap (c : Cqe)
  | recycle (b : Bid)
  | publish
  | complete (i : OpId)
  | deliver (fd : Fd) (b : Bid) (more : Bool)
  | starve (fd : Fd) (more : Bool)
  | exhaust (fd : Fd)
  | flush (c : Cqe)
deriving DecidableEq, Repr

/-- The product LTS: client discipline × demonic environment. -/
inductive Step (cfg : Cfg) : St → Lbl → St → Prop where
  /-- CLIENT: submit a fresh op (SQE write + tail publish, fused). -/
  | submit {s : St} {q : Sqe}
      (hid : q.id = s.nextId) (hk : kindOk q s) (hp : predOk q s) :
      Step cfg s (.submit q)
        { s with inflight := q :: s.inflight, nextId := s.nextId + 1 }
  /-- CLIENT: reap the completion at the queue head and dispatch it. -/
  | reap {s : St} {c : Cqe} {rest : List Cqe}
      (hcq : s.cq = c :: rest) :
      Step cfg s (.reap c) (dispatch { s with cq := rest } c)
  /-- CLIENT: recycle a held buffer id — write the ring entry, tail not yet
  advanced. Guard: the client only recycles what it holds, and gives the
  lease up in the same move. -/
  | recycle {s : St} {b : Bid} {h₁ h₂ : List Bid}
      (hheld : s.held = h₁ ++ b :: h₂) :
      Step cfg s (.recycle b)
        { s with held := h₁ ++ h₂, pending := b :: s.pending }
  /-- CLIENT: advance the buffer-ring tail, publishing all pending entries. -/
  | publish {s : St} :
      Step cfg s .publish
        { s with free := s.free ++ s.pending, pending := [] }
  /-- ENV: complete any in-flight non-multishot op, in any link-respecting
  order (close-with-in-flight edges included: a close may complete before
  or after other ops on its fd). -/
  | complete {s : St} {q : Sqe} {q₁ q₂ : List Sqe}
      (hin : s.inflight = q₁ ++ q :: q₂)
      (hms : ∀ fd, q.kind ≠ OpKind.recvMulti fd)
      (hlk : linkFree q (q₁ ++ q₂)) :
      Step cfg s (.complete q.id)
        (post cfg { s with inflight := q₁ ++ q₂ } ⟨q.id, .plain, false⟩)
  /-- ENV: multishot buffer-select delivery, stream continuing: bind any
  published free entry and lend it via a completion with the more-flag set. -/
  | deliver_more {s : St} {q : Sqe} {fd : Fd} {b : Bid} {f₁ f₂ : List Bid}
      (hq : q ∈ s.inflight) (hk : q.kind = OpKind.recvMulti fd)
      (hfree : s.free = f₁ ++ b :: f₂) :
      Step cfg s (.deliver fd b true)
        (post cfg { s with free := f₁ ++ f₂ } ⟨q.id, .buf b, true⟩)
  /-- ENV: multishot buffer-select delivery that also ends the stream
  (more-flag cleared): the op leaves flight; re-arm becomes possible. -/
  | deliver_final {s : St} {q : Sqe} {fd : Fd} {b : Bid}
      {q₁ q₂ : List Sqe} {f₁ f₂ : List Bid}
      (hin : s.inflight = q₁ ++ q :: q₂) (hk : q.kind = OpKind.recvMulti fd)
      (hfree : s.free = f₁ ++ b :: f₂) :
      Step cfg s (.deliver fd b false)
        (post cfg { s with inflight := q₁ ++ q₂, free := f₁ ++ f₂ }
          ⟨q.id, .buf b, false⟩)
  /-- ENV: data arrived but no buffer was bound — the bytes are lost.
  Stream may or may not survive (`more`); no free entry is consumed. -/
  | starve_more {s : St} {q : Sqe} {fd : Fd}
      (hq : q ∈ s.inflight) (hk : q.kind = OpKind.recvMulti fd) :
      Step cfg s (.starve fd true)
        (post cfg s ⟨q.id, .bufferless fd, true⟩)
  | starve_final {s : St} {q : Sqe} {fd : Fd} {q₁ q₂ : List Sqe}
      (hin : s.inflight = q₁ ++ q :: q₂) (hk : q.kind = OpKind.recvMulti fd) :
      Step cfg s (.starve fd false)
        (post cfg { s with inflight := q₁ ++ q₂ } ⟨q.id, .bufferless fd, false⟩)
  /-- ENV: buffer exhaustion at any moment — no guard on `free` being
  empty; the published tail may lag, or a racing consumer may have taken
  the last visible entry. Terminates the multishot (more-flag cleared). -/
  | exhaust {s : St} {q : Sqe} {fd : Fd} {q₁ q₂ : List Sqe}
      (hin : s.inflight = q₁ ++ q :: q₂) (hk : q.kind = OpKind.recvMulti fd) :
      Step cfg s (.exhaust fd)
        (post cfg { s with inflight := q₁ ++ q₂ } ⟨q.id, .enobufs fd, false⟩)
  /-- ENV: flush one kernel-retained overflow completion into the queue
  once there is room (`nodrop` path). -/
  | flush {s : St} {c : Cqe} {rest : List Cqe}
      (hovf : s.ovf = c :: rest) (hroom : s.cq.length < cfg.cqCap) :
      Step cfg s (.flush c) { s with ovf := rest, cq := s.cq ++ [c] }

/-- Finite traces of the product LTS. -/
inductive Trace (cfg : Cfg) : St → List Lbl → St → Prop where
  | nil {s : St} : Trace cfg s [] s
  | cons {s s' s'' : St} {l : Lbl} {ls : List Lbl}
      (h : Step cfg s l s') (t : Trace cfg s' ls s'') :
      Trace cfg s (l :: ls) s''

/-- Reachability from the initial state. -/
def Reachable (cfg : Cfg) (s : St) : Prop :=
  ∃ ls, Trace cfg (init cfg) ls s

theorem Trace.single {cfg : Cfg} {s s' : St} {l : Lbl}
    (h : Step cfg s l s') : Trace cfg s [l] s' :=
  .cons h .nil

theorem Trace.append {cfg : Cfg} {s s' s'' : St} {l₁ l₂ : List Lbl}
    (t₁ : Trace cfg s l₁ s') (t₂ : Trace cfg s' l₂ s'') :
    Trace cfg s (l₁ ++ l₂) s'' := by
  induction t₁ with
  | nil => exact t₂
  | cons h _ ih => exact .cons h (ih t₂)

/-- A trace over concatenated labels splits at the seam. -/
theorem Trace.append_split {cfg : Cfg} {s s'' : St} {l₁ l₂ : List Lbl}
    (t : Trace cfg s (l₁ ++ l₂) s'') :
    ∃ mid, Trace cfg s l₁ mid ∧ Trace cfg mid l₂ s'' := by
  induction l₁ generalizing s with
  | nil => exact ⟨s, .nil, t⟩
  | cons l ls ih =>
    cases t with
    | cons h t' =>
      obtain ⟨mid, tl, tr⟩ := ih t'
      exact ⟨mid, .cons h tl, tr⟩

/-- Progress half of no-leak: a held lease always has its recycle move
enabled — the discipline can never wedge a buffer it holds. -/
theorem recycle_enabled {cfg : Cfg} {s : St} {b : Bid}
    (h : b ∈ s.held) : ∃ s', Step cfg s (.recycle b) s' := by
  obtain ⟨h₁, h₂, hs⟩ := List.append_of_mem h
  exact ⟨_, .recycle hs⟩

end Uring
