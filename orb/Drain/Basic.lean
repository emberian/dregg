/-
Drain — graceful-shutdown / connection-draining as a transition system.

A server lifecycle passes through four modes:

    running   — accepting new connections; requests run normally.
    draining  — begin-drain has fired (e.g. on SIGTERM): the listener stops
                admitting new connections, and the requests already in flight
                are allowed to complete.
    drained   — every in-flight request has completed (the in-flight count has
                reached zero); no work remains.
    closed    — the server has released the listener. Terminal / absorbing.

Time is an explicit input; there is no ambient clock.  The transitions that
observe time carry the current clock reading `now`, and a drain `deadline`
(recorded when draining begins) bounds how long stragglers are waited on.  Once
the clock reaches the deadline, a force-close transition closes the server,
counting any still-in-flight requests as *force-closed* rather than dropping
them silently.

State (`DState`):

  * `mode`         — the lifecycle mode above;
  * `inflight`     — the number of requests currently in flight;
  * `entered`      — accounting tally: total requests ever admitted;
  * `completed`    — accounting tally: requests that completed normally;
  * `forcedClosed` — accounting tally: requests force-closed at the deadline;
  * `deadline`     — the clock value at/after which stragglers are force-closed;
  * `clock`        — the last observed clock reading.

The three tallies are accounting instrumentation.  They let the model state, as
an identity, that every admitted request is in exactly one of three places —
still in flight, completed, or force-closed — so none is silently lost
(`Accounted`, theorem 2).

Transitions (`step`):

  * `beginDrain dl`  — running → draining (or straight to drained when nothing
    is in flight), recording the deadline `dl`.  Idempotent once out of running.
  * `acceptReq`      — an accept attempt: admitted (in running) or refused (in
    every other mode).  New work is shut off here, exactly at begin-drain.
  * `complete`       — one in-flight request completes; in draining, completing
    the last one moves to drained.
  * `tick now`       — the clock advances to `now`; a drained server closes.
  * `forceClose now` — at/after the deadline, a draining server closes,
    accounting its stragglers as force-closed.

Theorems (this file, step level; lifted over traces in `Drain.Trace`):

  1. `acceptReq_refused_of_not_running` / `acceptReq_admit_only_running` /
     `running_acceptReq_admits` — once draining, no accept is admitted; an
     admission happens only in running.
  2. `step_accounted`, `step_completed_mono`, `step_forcedClosed_mono` — the
     accounting identity is preserved and the completed / force-closed tallies
     never decrease: no in-flight request is silently lost.
  3. `complete_reaches_drained`, `complete_stays_draining`, `step_drainShape` —
     drained is reached exactly when the in-flight count hits zero.
  4. `closed_absorbing` — closed is absorbing.
  5. `forceClose_before_deadline_stutters`, `forceClose_at_deadline`,
     `forceClose_honors_deadline`, `forceClose_drops_only_after_deadline` — a
     force-close happens only at/after the deadline.
-/

namespace Drain

/-- The server lifecycle mode. -/
inductive Mode where
  | running
  | draining
  | drained
  | closed
deriving DecidableEq, Repr, Inhabited

/-- Drain inputs.  `beginDrain` carries the deadline recorded at SIGTERM;
`tick` and `forceClose` carry the current clock reading `now`. -/
inductive Event where
  | beginDrain (dl : Nat)
  | acceptReq
  | complete
  | tick (now : Nat)
  | forceClose (now : Nat)
deriving DecidableEq, Repr

/-- The observable outcome of an accept attempt. -/
inductive Output where
  | admitted
  | refused
deriving DecidableEq, Repr

/-- Drain state.  `entered`, `completed`, `forcedClosed` are accounting tallies;
`deadline` is set when draining begins; `clock` is the last observed reading. -/
structure DState where
  mode : Mode
  inflight : Nat
  entered : Nat
  completed : Nat
  forcedClosed : Nat
  deadline : Nat
  clock : Nat
deriving DecidableEq, Repr

/-- A fresh, running server: nothing in flight, all tallies zero. -/
def init : DState :=
  { mode := .running, inflight := 0, entered := 0, completed := 0,
    forcedClosed := 0, deadline := 0, clock := 0 }

/-- One step.  Every (mode, event) pair is handled, so `step` is total.
`beginDrain` stops accepting and moves out of running (straight to drained when
idle).  `acceptReq` admits only in running.  `complete` retires one in-flight
request, moving draining → drained when it retires the last.  `tick` advances
the clock and closes a drained server.  `forceClose` closes a draining server
only at/after the deadline, tallying its stragglers as force-closed. -/
def step (s : DState) : Event → DState × List Output
  | .beginDrain dl =>
    match s.mode with
    | .running =>
      if 0 < s.inflight then ({ s with mode := .draining, deadline := dl }, [])
      else ({ s with mode := .drained, deadline := dl }, [])
    | .draining => (s, [])
    | .drained => (s, [])
    | .closed => (s, [])
  | .acceptReq =>
    match s.mode with
    | .running =>
      ({ s with inflight := s.inflight + 1, entered := s.entered + 1 },
        [Output.admitted])
    | .draining => (s, [Output.refused])
    | .drained => (s, [Output.refused])
    | .closed => (s, [Output.refused])
  | .complete =>
    match s.mode with
    | .running =>
      if 0 < s.inflight then
        ({ s with inflight := s.inflight - 1, completed := s.completed + 1 }, [])
      else (s, [])
    | .draining =>
      if 0 < s.inflight then
        ({ s with mode := (if s.inflight = 1 then .drained else .draining),
                  inflight := s.inflight - 1, completed := s.completed + 1 }, [])
      else (s, [])
    | .drained => (s, [])
    | .closed => (s, [])
  | .tick now =>
    match s.mode with
    | .running => ({ s with clock := max s.clock now }, [])
    | .draining => ({ s with clock := max s.clock now }, [])
    | .drained => ({ s with mode := .closed, clock := max s.clock now }, [])
    | .closed => ({ s with clock := max s.clock now }, [])
  | .forceClose now =>
    match s.mode with
    | .running => (s, [])
    | .draining =>
      if s.deadline ≤ now then
        ({ s with mode := .closed, forcedClosed := s.forcedClosed + s.inflight,
                  inflight := 0, clock := max s.clock now }, [])
      else (s, [])
    | .drained => (s, [])
    | .closed => (s, [])

/-! ### Determinism and totality -/

/-- **Determinism.** `step` is a function, so identical inputs give identical
results. -/
theorem step_deterministic {s : DState} {e : Event} {r₁ r₂ : DState × List Output}
    (h₁ : r₁ = step s e) (h₂ : r₂ = step s e) : r₁ = r₂ := by rw [h₁, h₂]

/-- **Totality (mode).** From any state and event `step` lands in one of the
four modes — there are no stuck states. -/
theorem mode_total (s : DState) (e : Event) :
    (step s e).1.mode = .running ∨ (step s e).1.mode = .draining
      ∨ (step s e).1.mode = .drained ∨ (step s e).1.mode = .closed := by
  cases (step s e).1.mode
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

/-- Every step emits at most one output. -/
theorem output_le_one (s : DState) (e : Event) : (step s e).2.length ≤ 1 := by
  cases e <;> simp only [step] <;> (repeat' split) <;> simp

/-! ### Theorem 1 — once draining, no accept is admitted -/

/-- In running, an accept is admitted and the in-flight count rises by one. -/
theorem running_acceptReq_admits {s : DState} (h : s.mode = .running) :
    (step s .acceptReq).2 = [Output.admitted]
      ∧ (step s .acceptReq).1.inflight = s.inflight + 1
      ∧ (step s .acceptReq).1.entered = s.entered + 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [step, h]

/-- **New work is shut off exactly at begin-drain.** In any mode other than
running an accept attempt is refused. -/
theorem acceptReq_refused_of_not_running {s : DState} (h : s.mode ≠ .running) :
    (step s .acceptReq).2 = [Output.refused] := by
  simp only [step]
  split
  · rename_i hm; exact absurd hm h
  · rfl
  · rfl
  · rfl

/-- Consequently, no accept is admitted once out of running. -/
theorem acceptReq_no_admit_of_not_running {s : DState} (h : s.mode ≠ .running) :
    Output.admitted ∉ (step s .acceptReq).2 := by
  rw [acceptReq_refused_of_not_running h]; simp

/-- An admission can only occur in running. -/
theorem acceptReq_admit_only_running {s : DState}
    (h : (step s .acceptReq).2 = [Output.admitted]) : s.mode = .running := by
  simp only [step] at h
  split at h
  · rename_i hm; exact hm
  · simp at h
  · simp at h
  · simp at h

/-- A refused accept leaves the in-flight count unchanged: refusal charges
nothing. -/
theorem acceptReq_refused_inflight_unchanged {s : DState} (h : s.mode ≠ .running) :
    (step s .acceptReq).1.inflight = s.inflight := by
  simp only [step]
  split
  · rename_i hm; exact absurd hm h
  · rfl
  · rfl
  · rfl

/-! ### Theorem 2 — the accounting identity: no request silently lost -/

/-- The accounting invariant: every admitted request is either still in flight,
completed, or force-closed. -/
def Accounted (s : DState) : Prop :=
  s.entered = s.inflight + s.completed + s.forcedClosed

/-- The accounting identity holds at a fresh server. -/
theorem accounted_init : Accounted init := by simp [Accounted, init]

/-- **Every step preserves the accounting identity.** Whatever a transition
does — admit, complete, force-close, or stutter — the tally of entered requests
still equals in-flight + completed + force-closed.  Nothing is lost. -/
theorem step_accounted {s : DState} (e : Event) (h : Accounted s) :
    Accounted (step s e).1 := by
  simp only [Accounted] at h ⊢
  cases e <;> simp only [step] <;> (repeat' split) <;> simp_all <;> omega

/-- The completed tally never decreases: a completed request stays counted. -/
theorem step_completed_mono (s : DState) (e : Event) :
    s.completed ≤ (step s e).1.completed := by
  cases e <;> simp only [step] <;> (repeat' split) <;> simp <;> omega

/-- The force-closed tally never decreases: a force-closed request stays
counted. -/
theorem step_forcedClosed_mono (s : DState) (e : Event) :
    s.forcedClosed ≤ (step s e).1.forcedClosed := by
  cases e <;> simp only [step] <;> (repeat' split) <;> simp <;> omega

/-- The entered tally never decreases. -/
theorem step_entered_mono (s : DState) (e : Event) :
    s.entered ≤ (step s e).1.entered := by
  cases e <;> simp only [step] <;> (repeat' split) <;> simp <;> omega

/-! ### Theorem 3 — drained is reached exactly when the in-flight count is zero -/

/-- The drain-shape invariant tying mode to the in-flight count: draining always
has work outstanding, drained and closed never do. -/
def DrainShape (s : DState) : Prop :=
  (s.mode = .draining → 0 < s.inflight)
    ∧ (s.mode = .drained → s.inflight = 0)
    ∧ (s.mode = .closed → s.inflight = 0)

/-- The drain-shape invariant holds at a fresh (running) server. -/
theorem drainShape_init : DrainShape init := by simp [DrainShape, init]

/-- **Every step preserves the drain-shape invariant.** -/
theorem step_drainShape {s : DState} (e : Event) (h : DrainShape s) :
    DrainShape (step s e).1 := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [DrainShape]
  cases e <;> simp only [step] <;> (repeat' split) <;>
    refine ⟨fun hh => ?_, fun hh => ?_, fun hh => ?_⟩ <;> simp_all <;> omega

/-- **Progress: retiring the last in-flight request reaches drained.** In
draining, a `complete` that empties the in-flight set moves to drained. -/
theorem complete_reaches_drained {s : DState} (h : s.mode = .draining)
    (h1 : s.inflight = 1) :
    (step s .complete).1.mode = .drained ∧ (step s .complete).1.inflight = 0 := by
  simp only [step, h]
  rw [if_pos (by omega)]
  simp [h1]

/-- With more than one request still in flight, a `complete` stays in draining —
drained is not reached early. -/
theorem complete_stays_draining {s : DState} (h : s.mode = .draining)
    (h2 : 2 ≤ s.inflight) :
    (step s .complete).1.mode = .draining := by
  simp only [step, h]
  rw [if_pos (by omega)]
  dsimp only
  rw [if_neg (by omega)]

/-! ### Theorem 4 — closed is absorbing -/

/-- **Closed is absorbing.** From closed, every event leaves the mode closed. -/
theorem closed_absorbing {s : DState} (e : Event) (h : s.mode = .closed) :
    (step s e).1.mode = .closed := by
  cases e <;> simp only [step, h]

/-- In closed, the in-flight count and every tally are frozen. -/
theorem closed_counters_frozen {s : DState} (e : Event) (h : s.mode = .closed) :
    (step s e).1.inflight = s.inflight
      ∧ (step s e).1.entered = s.entered
      ∧ (step s e).1.completed = s.completed
      ∧ (step s e).1.forcedClosed = s.forcedClosed := by
  cases e <;> simp [step, h]

/-! ### Theorem 5 — the deadline is honored -/

/-- **No early force-close.** Before the deadline, a `forceClose` stutters: a
draining server with stragglers is left untouched. -/
theorem forceClose_before_deadline_stutters {s : DState} {now : Nat}
    (h : s.mode = .draining) (hd : now < s.deadline) :
    step s (.forceClose now) = (s, []) := by
  simp only [step, h]
  rw [if_neg (by omega)]

/-- At/after the deadline, a `forceClose` closes the draining server and moves
its stragglers to the force-closed tally (nothing dropped uncounted). -/
theorem forceClose_at_deadline {s : DState} {now : Nat}
    (h : s.mode = .draining) (hd : s.deadline ≤ now) :
    (step s (.forceClose now)).1.mode = .closed
      ∧ (step s (.forceClose now)).1.forcedClosed = s.forcedClosed + s.inflight
      ∧ (step s (.forceClose now)).1.inflight = 0 := by
  simp only [step, h]
  rw [if_pos hd]
  exact ⟨rfl, rfl, rfl⟩

/-- **The deadline is honored.** If a `forceClose` closes a server that was not
already closed, the clock had reached the deadline. -/
theorem forceClose_honors_deadline {s : DState} {now : Nat}
    (h0 : s.mode ≠ .closed)
    (hc : (step s (.forceClose now)).1.mode = .closed) :
    s.deadline ≤ now := by
  rcases Nat.lt_or_ge now s.deadline with hlt | hge
  · -- below the deadline every mode stutters, so the mode cannot become closed.
    exfalso
    have hstut : step s (.forceClose now) = (s, []) := by
      cases hm : s.mode with
      | running => simp [step, hm]
      | draining => simp only [step, hm]; rw [if_neg (by omega)]
      | drained => simp [step, hm]
      | closed => simp [step, hm]
    rw [hstut] at hc
    exact h0 hc
  · exact hge

/-- **No straggler dropped early.** If a `forceClose` actually force-closes a
request (the force-closed tally strictly rises), the deadline had been
reached. -/
theorem forceClose_drops_only_after_deadline {s : DState} {now : Nat}
    (h : s.forcedClosed < (step s (.forceClose now)).1.forcedClosed) :
    s.deadline ≤ now := by
  simp only [step] at h
  split at h
  · simp at h
  · split at h
    · assumption
    · simp at h
  · simp at h
  · simp at h

end Drain
