/-
Shed — buffer-exhaustion and overload-shedding edges, with explicit
accounting.

The unhappy paths of the receive pipeline for one socket, sans-IO. Inbound
completion units (one unit = one receive completion's payload, abstract
here) are admitted into a per-socket FIFO backlog awaiting the consumer.
Three loss/kill edges exist, and the design rule is that **every one is a
named transition with a declared policy — never an implicit fallthrough**:

  * **Backlog cap with oldest-drop.** The backlog is capped (default: a
    quarter of the shared buffer-ring size — an anti-starvation ratio, so a
    single slow consumer cannot pin the whole ring). On overflow the
    *oldest* entry is dropped and its buffer recycled; the drop is recorded
    in the ledger as `shed`.
  * **Bufferless kill.** A completion arrives carrying a byte count but no
    buffer — the shared pool was exhausted, so the data is irrecoverably
    lost. Policy: record the unit as `killed` and close the socket (a
    connection that has lost inbound bytes must not continue).
  * **Admission refusal.** Units offered to a closed socket are refused
    outright — recorded in the `refused` ledger, never admitted.

The point of the machine is the **no-silent-shed accounting identity**: at
every reachable state,

    settled.map fst ++ backlog = admitted

where `settled` is the single ordered ledger of every unit that left the
backlog, each tagged with its explicit fate (`delivered`, `shed`, or
`killed`). The identity says three things at once:

  1. **Accounting** — every admitted unit is either still backlogged or has
     exactly one recorded fate. Nothing vanishes silently.
  2. **Order** — units settle in admission order (the backlog is FIFO and
     both consumption and oldest-drop take the front), so the ledger is a
     faithful prefix of the admission sequence.
  3. **No invention** — nothing settles that was not admitted.

Alongside it: the backlog never exceeds its cap, and a closed socket holds
no backlog (its buffers were recycled — explicitly, as `shed`).
-/

namespace Flow

/-- The explicit fate of a settled unit. Every way out of the backlog is
one of these — the "declared policy" per edge. -/
inductive Fate where
  /-- Consumed by the handler: fully processed. -/
  | delivered
  /-- Dropped by the declared backlog policy (oldest-drop on overflow, or
  recycle at close). -/
  | shed
  /-- Irrecoverably lost at the buffer-exhaustion edge; the socket was
  closed in the same step. -/
  | killed
  deriving Repr, DecidableEq, Inhabited

/-- Default backlog capacity: one quarter of the shared buffer-ring size
(64/4), so one slow consumer cannot starve the ring for every other
socket on the loop. -/
def recvBacklogCap : Nat := 16

/-- Per-socket shed state, over an abstract unit type `α`.

`backlog` and `closed` are the operational state; `settled`, `admitted`,
and `refused` are ghost ledgers for the accounting identity. -/
structure ShedQueue (α : Type u) where
  /-- Backlog capacity (units). -/
  cap : Nat
  /-- FIFO backlog of admitted, not-yet-consumed units. -/
  backlog : List α
  /-- Ghost: every unit that left the backlog, in order, with its fate. -/
  settled : List (α × Fate)
  /-- Ghost: every unit the machine admitted, in order. -/
  admitted : List α
  /-- Ghost: units refused at admission — offered to a closed socket;
  never admitted, never owing a fate. -/
  refused : List α
  /-- The socket has been closed. -/
  closed : Bool

/-- A fresh socket with capacity `cap`. -/
def ShedQueue.init (cap : Nat) : ShedQueue α := ⟨cap, [], [], [], [], false⟩

/-- Result code: the declared policy outcome of each event. -/
inductive ShedResult where
  /-- Unit admitted into the backlog, under cap. -/
  | admitted
  /-- Unit admitted; the backlog was full, so the *oldest* entry was shed
  by policy (recorded). -/
  | admittedDropOldest
  /-- Unit refused at admission: socket closed. -/
  | refused
  /-- The oldest backlogged unit was consumed by the handler. -/
  | consumed
  /-- Nothing to consume. -/
  | idle
  /-- Bufferless completion: unit killed, socket closed. -/
  | killedClosed
  /-- Close acknowledged. -/
  | closedOk
  deriving Repr, DecidableEq, Inhabited

/-- Events driving one socket's shed edges. -/
inductive ShedEv (α : Type u) where
  /-- A completion carrying unit `u` *with* a pool buffer arrives. -/
  | admit (u : α)
  /-- The handler consumes the oldest backlogged unit. -/
  | consume
  /-- A completion carrying unit `u` but *no* buffer arrives: the pool was
  exhausted and the data is lost. -/
  | bufferlessKill (u : α)
  /-- The socket is closed; backlogged buffers are recycled (shed). -/
  | close

/-- One step of the shed machine. -/
def ShedQueue.step (s : ShedQueue α) : ShedEv α → ShedQueue α × ShedResult
  | .admit u =>
    if s.closed then
      ({ s with refused := s.refused ++ [u] }, .refused)
    else if s.backlog.length < s.cap then
      ({ s with backlog := s.backlog ++ [u],
                admitted := s.admitted ++ [u] }, .admitted)
    else
      match s.backlog with
      | [] =>
        -- cap = 0: the unit is admitted and immediately shed — explicitly.
        ({ s with settled := s.settled ++ [(u, .shed)],
                  admitted := s.admitted ++ [u] }, .admittedDropOldest)
      | v :: rest =>
        ({ s with backlog := rest ++ [u],
                  settled := s.settled ++ [(v, .shed)],
                  admitted := s.admitted ++ [u] }, .admittedDropOldest)
  | .consume =>
    match s.backlog with
    | [] => (s, .idle)
    | v :: rest =>
      ({ s with backlog := rest,
                settled := s.settled ++ [(v, .delivered)] }, .consumed)
  | .bufferlessKill u =>
    if s.closed then
      ({ s with refused := s.refused ++ [u] }, .refused)
    else
      ({ s with backlog := [],
                settled := s.settled ++ s.backlog.map (fun v => (v, .shed))
                             ++ [(u, .killed)],
                admitted := s.admitted ++ [u],
                closed := true }, .killedClosed)
  | .close =>
    if s.closed then (s, .closedOk)
    else
      ({ s with backlog := [],
                settled := s.settled ++ s.backlog.map (fun v => (v, .shed)),
                closed := true }, .closedOk)

/-- Run a trace of events. -/
def ShedQueue.run (s : ShedQueue α) : List (ShedEv α) → ShedQueue α
  | [] => s
  | e :: es => ((s.step e).1).run es

/-- The machine invariant.

1. **The no-silent-shed identity**: the settled ledger's units, followed
   by the backlog, are exactly the admitted units in order.
2. The backlog respects the cap.
3. A closed socket holds no backlog. -/
def ShedQueue.Inv (s : ShedQueue α) : Prop :=
  s.settled.map Prod.fst ++ s.backlog = s.admitted ∧
  s.backlog.length ≤ s.cap ∧
  (s.closed = true → s.backlog = [])

theorem ShedQueue.init_inv (cap : Nat) :
    (ShedQueue.init cap : ShedQueue α).Inv := by
  simp [Inv, init]

/-- Tagging a list and projecting the tags away is the identity. -/
private theorem map_fst_tag (l : List α) (f : Fate) :
    l.map (Prod.fst ∘ fun v => (v, f)) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    calc (x :: xs).map (Prod.fst ∘ fun v => (v, f))
        = x :: xs.map (Prod.fst ∘ fun v => (v, f)) := rfl
      _ = x :: xs := by rw [ih]

/-- **Preservation**: every edge — admission, oldest-drop, consumption,
bufferless kill, close — preserves the accounting identity, the cap bound,
and the closed-empty condition. -/
theorem ShedQueue.step_inv (s : ShedQueue α) (e : ShedEv α) (h : s.Inv) :
    (s.step e).1.Inv := by
  obtain ⟨hacct, hcap, hclosed⟩ := h
  cases e with
  | admit u =>
    cases hc : s.closed with
    | true =>
      simp only [step, hc, if_pos]
      exact ⟨hacct, hcap, fun _ => hclosed hc⟩
    | false =>
      by_cases hlen : s.backlog.length < s.cap
      · refine ⟨?_, ?_, ?_⟩
        · simp [step, hc, hlen, ← hacct]
        · simp only [step, hc, Bool.false_eq_true, if_false, hlen, if_pos]
          simp
          omega
        · simp [step, hc, hlen]
      · cases hb : s.backlog with
        | nil =>
          have hcap0 : s.cap = 0 := by rw [hb] at hlen; simp at hlen; omega
          refine ⟨?_, ?_, ?_⟩
          · simp [step, hc, hlen, hb, hcap0, ← hacct]
          · simp [step, hc, hlen, hb, hcap0]
          · simp [step, hc, hlen, hb, hcap0]
        | cons v rest =>
          have hlen' : ¬ (rest.length + 1 < s.cap) := by
            rw [hb] at hlen; simpa using hlen
          have hcap' : rest.length + 1 ≤ s.cap := by
            rw [hb] at hcap; simpa using hcap
          refine ⟨?_, ?_, ?_⟩
          · simp [step, hc, hlen, hlen', hb, ← hacct]
          · simp [step, hc, hlen, hlen', hb]
            omega
          · simp [step, hc, hlen, hlen', hb]
  | consume =>
    cases hb : s.backlog with
    | nil => simp only [step, hb]; exact ⟨hacct, hcap, hclosed⟩
    | cons v rest =>
      have hne : s.closed = false := by
        cases hcc : s.closed with
        | false => rfl
        | true => rw [hclosed hcc] at hb; cases hb
      constructor
      · simp only [step, hb, List.map_append, List.map_cons, List.map_nil,
          List.append_assoc]
        rw [← hacct, hb]
        simp
      · refine ⟨?_, ?_⟩
        · simp only [step, hb]
          rw [hb] at hcap
          simp at hcap ⊢
          omega
        · intro hcc
          simp only [step, hb] at hcc ⊢
          rw [hne] at hcc
          cases hcc
  | bufferlessKill u =>
    cases hc : s.closed with
    | true =>
      simp only [step, hc, if_pos]
      exact ⟨hacct, hcap, fun _ => hclosed hc⟩
    | false =>
      refine ⟨?_, by simp [step, hc], by simp [step, hc]⟩
      simp [step, hc, map_fst_tag, ← hacct]
  | close =>
    cases hc : s.closed with
    | true => simp only [step, hc, if_pos]; exact ⟨hacct, hcap, hclosed⟩
    | false =>
      refine ⟨?_, by simp [step, hc], by simp [step, hc]⟩
      simp [step, hc, map_fst_tag, ← hacct]

/-- The invariant holds along every trace from every invariant state. -/
theorem ShedQueue.run_inv (s : ShedQueue α) (es : List (ShedEv α))
    (h : s.Inv) : (s.run es).Inv := by
  induction es generalizing s with
  | nil => exact h
  | cons e es ih => exact ih _ (s.step_inv e h)

/-- The invariant holds along every trace from a fresh socket. -/
theorem ShedQueue.run_init_inv (cap : Nat) (es : List (ShedEv α)) :
    ((ShedQueue.init cap : ShedQueue α).run es).Inv :=
  run_inv _ es (init_inv cap)

/-- **No silent shed** (membership form): every admitted unit is either
still backlogged or has an explicitly recorded fate — delivered, shed, or
killed. There is no fourth way out. -/
theorem ShedQueue.no_silent_shed (s : ShedQueue α) (h : s.Inv) (u : α)
    (hu : u ∈ s.admitted) :
    u ∈ s.backlog ∨ ∃ f, (u, f) ∈ s.settled := by
  rw [← h.1] at hu
  rcases List.mem_append.mp hu with hs | hb
  · rcases List.mem_map.mp hs with ⟨⟨v, f⟩, hmem, hfst⟩
    exact Or.inr ⟨f, by cases hfst; exact hmem⟩
  · exact Or.inl hb

/-- **No invention**: everything in the ledger or the backlog was admitted. -/
theorem ShedQueue.settled_admitted (s : ShedQueue α) (h : s.Inv) (u : α)
    (f : Fate) (hu : (u, f) ∈ s.settled) : u ∈ s.admitted := by
  rw [← h.1]
  exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨(u, f), hu, rfl⟩))

/-- **Order**: the settled ledger is a prefix of the admission sequence —
units settle in the order they were admitted. -/
theorem ShedQueue.settled_prefix (s : ShedQueue α) (h : s.Inv) :
    ∃ rest, s.settled.map Prod.fst ++ rest = s.admitted :=
  ⟨s.backlog, h.1⟩

/-- **The cap is respected** at every reachable state. -/
theorem ShedQueue.backlog_bounded (s : ShedQueue α) (h : s.Inv) :
    s.backlog.length ≤ s.cap :=
  h.2.1

/-- **Oldest-drop is exact.** When the backlog is full, admitting `u` sheds
precisely the *oldest* entry (the front), records it, and keeps FIFO order
for the rest: the backlog becomes `rest ++ [u]`. -/
theorem ShedQueue.oldest_drop_exact (s : ShedQueue α) (u v : α)
    (rest : List α) (hb : s.backlog = v :: rest) (hc : s.closed = false)
    (hfull : ¬ s.backlog.length < s.cap) :
    (s.step (.admit u)).1.backlog = rest ++ [u] ∧
    (s.step (.admit u)).1.settled = s.settled ++ [(v, .shed)] ∧
    (s.step (.admit u)).2 = .admittedDropOldest := by
  have hfull' : ¬ (rest.length + 1 < s.cap) := by
    rw [hb] at hfull; simpa using hfull
  simp [step, hc, hfull, hfull', hb]

/-- **Consumption is FIFO**: consuming takes exactly the oldest entry and
records it delivered. -/
theorem ShedQueue.consume_fifo (s : ShedQueue α) (v : α) (rest : List α)
    (hb : s.backlog = v :: rest) :
    (s.step .consume).1.backlog = rest ∧
    (s.step .consume).1.settled = s.settled ++ [(v, .delivered)] := by
  simp [step, hb]

/-- **Refusal is not admission**: a unit offered to a closed socket is
recorded refused and the admission ledger is untouched — the accounting
identity owes it nothing. -/
theorem ShedQueue.closed_refuses (s : ShedQueue α) (u : α)
    (hc : s.closed = true) :
    (s.step (.admit u)).1.admitted = s.admitted ∧
    (s.step (.admit u)).1.refused = s.refused ++ [u] ∧
    (s.step (.admit u)).2 = .refused := by
  simp [step, hc]

/-- **The bufferless kill is loud.** Pool exhaustion under data loses the
unit — but the loss is recorded (`killed`), the backlog is explicitly
recycled (`shed`), and the socket closes in the same step. Nothing about
the edge is silent. -/
theorem ShedQueue.bufferless_kill_closes (s : ShedQueue α) (u : α)
    (hc : s.closed = false) :
    (s.step (.bufferlessKill u)).1.closed = true ∧
    (s.step (.bufferlessKill u)).1.backlog = [] ∧
    (u, Fate.killed) ∈ (s.step (.bufferlessKill u)).1.settled := by
  simp [step, hc]

end Flow
