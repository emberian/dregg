/-
Tap.Basic — the gated diagnostic tap as a sequential transition system.

A diagnostic tap copies dataplane traffic to a diagnostic sink for inspection.
The security property is an information-leak boundary: the tap must copy a
packet ONLY when it has been explicitly enabled.  When disabled (the default)
the tap must not read, copy, delay, or otherwise touch the traffic — the guard
sits before any tap work, so a disabled tap is a structural no-op.

The model is a single gate (an enable flag) plus a sink (the diagnostic log).
The dataplane offers every packet to the tap via `step … (.pkt p)`.  Control
events (`.enable` / `.disable`) flip the gate.  A run folds a trace of these
events over the state from an initial state, exactly as `Rate.Trace` and
`StickTable.Trace` do.

The packet payload is abstract (`α`): the theorems hold for any payload type,
so nothing about the leak boundary depends on packet contents.

Master identity (`run_sink`): after any trace the sink is the starting sink
followed by exactly the packets that arrived while the gate was up, in arrival
order.  Every headline security theorem is a corollary of this one identity.
-/

namespace Tap

/-- A dataplane / control event offered to the tap.

* `.pkt p`  — a packet `p` traverses the dataplane; the tap is invoked on it.
* `.enable` — the control edge that turns the gate on.
* `.disable`— the control edge that turns the gate off.

`.enable` / `.disable` are the ONLY constructors that change the gate; a `.pkt`
never does (`step_pkt_enabled`).  This is the "gate transitions are the sole
control" structure, made syntactic. -/
inductive Ev (α : Type) where
  | pkt (p : α)
  | enable
  | disable
deriving Repr

/-- The tap state: the gate flag and the sink log (the packets the sink has
received, in arrival order).  The forwarded dataplane packet is NOT part of the
state — the tap is observation-only, so forwarding is modelled separately
(`forward`) and is provably independent of this state. -/
structure State (α : Type) where
  /-- The gate: `true` = tap enabled (copying), `false` = disabled (default). -/
  enabled : Bool
  /-- The diagnostic sink log: packets copied so far, oldest first. -/
  sink : List α
deriving Repr

variable {α : Type}

/-- The initial state: gate DISABLED (the safe default), sink empty. -/
def init : State α := { enabled := false, sink := [] }

/-- A fresh state with the gate already ENABLED, sink empty.  Used to state
enabled-window faithfulness from a clean start. -/
def initOn : State α := { enabled := true, sink := [] }

/-- One step of the tap.

The `.pkt` case is the guarded hot path: when the gate is up the packet is
appended to the sink (append-at-end preserves arrival order); when the gate is
down the state is returned UNCHANGED — the packet `p` is not even read into the
tap path (it does not appear on the right of the `false` branch).  This mirrors
the `if !is_enabled() { return; }` guard that precedes all tap work. -/
def step (s : State α) : Ev α → State α
  | .pkt p =>
      match s.enabled with
      | true  => { s with sink := s.sink ++ [p] }
      | false => s
  | .enable  => { s with enabled := true }
  | .disable => { s with enabled := false }

/-- Fold a trace of events over the state, left to right. -/
def run (s : State α) : List (Ev α) → State α
  | [] => s
  | e :: es => run (step s e) es

/-! ### Pure views of a trace

These read off, from the events alone, what the gate does and what the sink
should hold — the specification the `run` fold is checked against. -/

/-- The gate value after a trace, starting from `enabled`.  Only `.enable` /
`.disable` move it; `.pkt` leaves it. -/
def gateAfter (enabled : Bool) : List (Ev α) → Bool
  | [] => enabled
  | .pkt _ :: es => gateAfter enabled es
  | .enable :: es => gateAfter true es
  | .disable :: es => gateAfter false es

/-- The packets that SHOULD reach the sink over a trace, given the gate value
`enabled` on entry: exactly the `.pkt` events that occur while the gate is up,
in order.  A packet under a down gate contributes nothing. -/
def tappedFrom (enabled : Bool) : List (Ev α) → List α
  | [] => []
  | .pkt p :: es =>
      match enabled with
      | true  => p :: tappedFrom true es
      | false => tappedFrom false es
  | .enable :: es => tappedFrom true es
  | .disable :: es => tappedFrom false es

/-- Every packet in a trace, regardless of gate — the "no drop, no injection"
yardstick for the fully-enabled window. -/
def pktsOf : List (Ev α) → List α
  | [] => []
  | .pkt p :: es => p :: pktsOf es
  | .enable :: es => pktsOf es
  | .disable :: es => pktsOf es

/-- Whether a trace contains any `.enable` control edge. -/
def hasEnable : List (Ev α) → Bool
  | [] => false
  | .enable :: _ => true
  | _ :: es => hasEnable es

/-- Whether a trace contains any `.disable` control edge. -/
def hasDisable : List (Ev α) → Bool
  | [] => false
  | .disable :: _ => true
  | _ :: es => hasDisable es

/-! ### Step-level facts about the gate -/

/-- A packet never changes the gate.  (The gate is controlled solely by the
`.enable` / `.disable` edges — this is the step-level half of that claim.) -/
@[simp] theorem step_pkt_enabled (s : State α) (p : α) :
    (step s (.pkt p)).enabled = s.enabled := by
  cases hb : s.enabled <;> simp [step, hb]

/-- `.enable` sets the gate up. -/
@[simp] theorem step_enable_enabled (s : State α) :
    (step s (.enable : Ev α)).enabled = true := rfl

/-- `.disable` sets the gate down. -/
@[simp] theorem step_disable_enabled (s : State α) :
    (step s (.disable : Ev α)).enabled = false := rfl

/-- The gate after a run is exactly `gateAfter` of the trace: the running gate
is a pure function of the control edges (packets are invisible to it). -/
theorem run_enabled (s : State α) (es : List (Ev α)) :
    (run s es).enabled = gateAfter s.enabled es := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    cases e with
    | pkt p =>
      show (run (step s (.pkt p)) es).enabled = gateAfter s.enabled (.pkt p :: es)
      rw [ih (step s (.pkt p)), step_pkt_enabled]
      rfl
    | enable =>
      show (run (step s .enable) es).enabled = gateAfter s.enabled (.enable :: es)
      rw [ih (step s .enable)]; rfl
    | disable =>
      show (run (step s .disable) es).enabled = gateAfter s.enabled (.disable :: es)
      rw [ih (step s .disable)]; rfl

/-! ### The master accounting identity -/

/-- **`run_sink` — the master identity.**  After any trace, the sink is the
starting sink followed by exactly the packets that arrived while the gate was
up (`tappedFrom s.enabled es`), in arrival order.  No packet under a down gate
appears; every packet under an up gate appears exactly once, in order.

Every headline security theorem below is a corollary of this identity. -/
theorem run_sink (s : State α) (es : List (Ev α)) :
    (run s es).sink = s.sink ++ tappedFrom s.enabled es := by
  induction es generalizing s with
  | nil => simp [run, tappedFrom]
  | cons e es ih =>
    cases e with
    | pkt p =>
      show (run (step s (.pkt p)) es).sink = s.sink ++ tappedFrom s.enabled (.pkt p :: es)
      rw [ih (step s (.pkt p)), step_pkt_enabled]
      cases hb : s.enabled with
      | true => simp [step, tappedFrom, hb, List.append_assoc]
      | false => simp [step, tappedFrom, hb]
    | enable =>
      show (run (step s .enable) es).sink = s.sink ++ tappedFrom s.enabled (.enable :: es)
      rw [ih (step s .enable)]; simp [step, tappedFrom]
    | disable =>
      show (run (step s .disable) es).sink = s.sink ++ tappedFrom s.enabled (.disable :: es)
      rw [ih (step s .disable)]; simp [step, tappedFrom]

end Tap
