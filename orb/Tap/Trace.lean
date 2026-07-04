/-
Tap.Trace — the four headline security theorems for the gated tap, and the
observation-only forwarding model.

All four are corollaries of `run_sink` (the master identity in `Tap.Basic`):
after any trace the sink is the starting sink followed by exactly the packets
that arrived while the gate was up, in order.

  1. `no_copy_when_disabled` / `sink_disabled_window` (**theorem 1**) — over any
     trace in which the gate is never enabled, the sink receives NOTHING: it is
     unchanged (empty, from a fresh disabled start).  The packet is not read
     into the tap path — the guard precedes all tap work.

  2. `enabled_faithful` / `sink_enabled_window` (**theorem 2**) — over the
     enabled window the sink receives EXACTLY the tapped packets, in order: no
     drop, no injection, no reorder.  Stated as an equality of the sink to the
     full packet list of the window.

  3. `enable_starts_copy` / `disable_stops_copy` + `run_enabled` (**theorem 3**)
     — gate transitions are the sole control.  A `.pkt` never changes the gate
     (`step_pkt_enabled`), so the running gate is a pure function of the control
     edges (`run_enabled`); a `.enable` edge starts copying the very next packet
     regardless of the prior gate, a `.disable` edge stops it, cleanly.

  4. `forward_packet_id` / `forward_gate_independent` (**theorem 4**) — the tap
     is side-effect-free on the dataplane packet.  The forwarded packet equals
     the input packet, and is independent of the tap state (enabled or not) — the
     observation cannot mutate or divert the traffic it observes.
-/

import Tap.Basic

namespace Tap

variable {α : Type}

/-! ### Theorem 1 — no copy while the gate is never enabled -/

/-- With the gate down and no `.enable` in the trace, the specification sink for
the window is empty: nothing is ever due to be copied. -/
theorem tappedFrom_false_of_noEnable :
    ∀ es : List (Ev α), hasEnable es = false → tappedFrom false es = [] := by
  intro es
  induction es with
  | nil => intro _; rfl
  | cons e es ih =>
    cases e with
    | pkt p =>
      intro h
      have h' : hasEnable es = false := by simpa [hasEnable] using h
      simp [tappedFrom, ih h']
    | enable => intro h; simp [hasEnable] at h
    | disable =>
      intro h
      have h' : hasEnable es = false := by simpa [hasEnable] using h
      simp [tappedFrom, ih h']

/-- **Theorem 1 (general form).**  Starting from a disabled state, over any trace
that never enables the gate, the sink is UNCHANGED — not a single packet is
copied.  The gate stays provably down throughout (see `run_enabled` /
`gateAfter_false_of_noEnable`), so the guard rejects every packet before any tap
work. -/
theorem sink_disabled_window (s : State α) (hs : s.enabled = false)
    (es : List (Ev α)) (h : hasEnable es = false) :
    (run s es).sink = s.sink := by
  rw [run_sink, hs, tappedFrom_false_of_noEnable es h, List.append_nil]

/-- **Theorem 1 (headline).**  From the initial (disabled, empty) state, over any
trace in which the gate is never enabled, the sink log is EMPTY.  This is the
info-leak-safety property: no enable edge ⟹ nothing leaves the dataplane into
the diagnostic sink. -/
theorem no_copy_when_disabled (es : List (Ev α)) (h : hasEnable es = false) :
    (run (init : State α) es).sink = [] := by
  have := sink_disabled_window (init : State α) rfl es h
  simpa [init] using this

/-- The gate is provably down at the end of any trace that never enables it —
witnessing that `no_copy_when_disabled` is about a gate that was never up, at any
point, not merely at the end. -/
theorem gateAfter_false_of_noEnable :
    ∀ es : List (Ev α), hasEnable es = false → gateAfter false es = false := by
  intro es
  induction es with
  | nil => intro _; rfl
  | cons e es ih =>
    cases e with
    | pkt p =>
      intro h
      have h' : hasEnable es = false := by simpa [hasEnable] using h
      simp [gateAfter, ih h']
    | enable => intro h; simp [hasEnable] at h
    | disable =>
      intro h
      have h' : hasEnable es = false := by simpa [hasEnable] using h
      simp [gateAfter, ih h']

/-! ### Theorem 2 — faithful copy over the enabled window -/

/-- With the gate up and no `.disable` in the trace, the specification sink for
the window is EXACTLY every packet in the window, in order. -/
theorem tappedFrom_true_of_noDisable :
    ∀ es : List (Ev α), hasDisable es = false → tappedFrom true es = pktsOf es := by
  intro es
  induction es with
  | nil => intro _; rfl
  | cons e es ih =>
    cases e with
    | pkt p =>
      intro h
      have h' : hasDisable es = false := by simpa [hasDisable] using h
      simp [tappedFrom, pktsOf, ih h']
    | enable =>
      intro h
      have h' : hasDisable es = false := by simpa [hasDisable] using h
      simp [tappedFrom, pktsOf, ih h']
    | disable => intro h; simp [hasDisable] at h

/-- **Theorem 2 (general form).**  Over an enabled window (gate up on entry, no
`.disable` edge) the sink grows by EXACTLY the packets of the window, in arrival
order — no drop, no injection, no reorder. -/
theorem sink_enabled_window (s : State α) (hs : s.enabled = true)
    (es : List (Ev α)) (h : hasDisable es = false) :
    (run s es).sink = s.sink ++ pktsOf es := by
  rw [run_sink, hs, tappedFrom_true_of_noDisable es h]

/-- **Theorem 2 (headline).**  From a fresh enabled start, the sink is EXACTLY the
list of packets of the window — every tapped packet, once, in order, and nothing
else.  Faithful capture: no drop (every `.pkt` appears), no injection (only
`.pkt`s appear), no reorder (list order = arrival order). -/
theorem enabled_faithful (es : List (Ev α)) (h : hasDisable es = false) :
    (run (initOn : State α) es).sink = pktsOf es := by
  have := sink_enabled_window (initOn : State α) rfl es h
  simpa [initOn] using this

/-! ### Theorem 3 — gate transitions are the sole control -/

/-- **Theorem 3a.**  The gate at any point of a run is a pure function of the
control edges of the trace: packets are invisible to it.  (This is `run_enabled`
combined with the fact that `gateAfter` ignores `.pkt`.)  Together with
`step_pkt_enabled` this says nothing but an `.enable` / `.disable` edge can move
the gate — hence can change what the tap copies. -/
theorem gate_is_control_only (s : State α) (es : List (Ev α)) :
    (run s es).enabled = gateAfter s.enabled es := run_enabled s es

/-- **Theorem 3b — the enable edge starts copying, cleanly.**  Regardless of the
prior gate `s.enabled`, once a `.enable` edge is seen the very next packet `p` is
copied to the sink (it heads the newly-tapped suffix).  The right-hand side does
not mention `s.enabled`: the control edge OVERRIDES the prior gate. -/
theorem enable_starts_copy (s : State α) (p : α) (es : List (Ev α)) :
    (run s (.enable :: .pkt p :: es)).sink = s.sink ++ (p :: tappedFrom true es) := by
  rw [run_sink]
  simp [tappedFrom]

/-- **Theorem 3c — the disable edge stops copying, cleanly.**  Regardless of the
prior gate, once a `.disable` edge is seen the next packet `p` is NOT copied — it
is absent from the sink suffix, which continues as the disabled window.  Again
the right-hand side is independent of `s.enabled`. -/
theorem disable_stops_copy (s : State α) (p : α) (es : List (Ev α)) :
    (run s (.disable :: .pkt p :: es)).sink = s.sink ++ tappedFrom false es := by
  rw [run_sink]
  simp [tappedFrom]

/-! ### Theorem 4 — observation-only: side-effect-free on the dataplane packet -/

/-- The dataplane forwarding step, with the tap spliced in.  It returns the
packet to forward downstream AND the updated tap state.  Crucially the forwarded
packet is the input `p` itself — the tap reads/copies but never rewrites it. -/
def forward (s : State α) (p : α) : α × State α :=
  (p, step s (.pkt p))

/-- **Theorem 4a.**  The forwarded packet is EXACTLY the input packet — the tap
never mutates the packet it observes. -/
theorem forward_packet_id (s : State α) (p : α) :
    (forward s p).1 = p := rfl

/-- **Theorem 4b — non-interference (observation-only).**  The forwarded packet
is independent of the tap state: whether the tap is enabled or disabled, and
whatever the sink holds, the same packet is forwarded.  The observation cannot
influence the dataplane it observes. -/
theorem forward_gate_independent (s₁ s₂ : State α) (p : α) :
    (forward s₁ p).1 = (forward s₂ p).1 := rfl

/-- The tap side of `forward` is exactly `step … (.pkt p)`, so the sink-level
theorems above characterise the forwarding step's observable effect on the sink,
while `forward_packet_id` fixes its effect on the dataplane (none). -/
theorem forward_tap (s : State α) (p : α) :
    (forward s p).2 = step s (.pkt p) := rfl

/-! ### Concrete sanity checks (α := Nat) -/

/-- Default-disabled tap drops everything: no enable edge ⟹ empty sink. -/
example : (run (init : State Nat) [.pkt 1, .pkt 2, .pkt 3]).sink = [] := rfl

/-- Gate control demonstrated end to end: enable captures, disable drops, the
second enable resumes — the sink is exactly the packets seen while up, in
order. -/
example :
    (run (init : State Nat)
      [.enable, .pkt 1, .pkt 2, .disable, .pkt 3, .enable, .pkt 4]).sink
      = [1, 2, 4] := rfl

/-- A packet before any enable is not copied; the enable edge starts copying. -/
example : (run (init : State Nat) [.pkt 9, .enable, .pkt 7]).sink = [7] := rfl

end Tap
