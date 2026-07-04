/-
Health — the probe-driven up/down machine with hysteresis.

Active health checking probes each backend on an interval; each probe yields
`pass` or `fail`. The verdict machine holds the current verdict (`up`) plus
two consecutive-streak counters, and flips only at configured thresholds:

    Up   --(fail × fall)-->  Down        (fall = unhealthy threshold)
    Down --(pass × rise)-->  Up          (rise = healthy threshold)

Any probe in the opposite direction resets the streak: the thresholds are
*consecutive*-result thresholds. This is the standard rise/fall hysteresis.

Theorems:

  * `noFlap_fail` / `noFlap_pass` — **no flapping**: with a threshold ≥ 2, a
    single anomalous probe never flips the verdict from a settled state;
  * `flip_requires_streak` — a verdict flip on ANY single step happens only
    when the full threshold streak has accumulated;
  * `up_survives_below_fall` / `down_at_fall` (and duals) — **exact threshold
    semantics**: from a settled Up it takes exactly `fall` consecutive
    failures to go Down — `fall − 1` do nothing durable;
  * `noFlap_trace` — the trace-level no-flap theorem: a probe history whose
    longest consecutive-failure run is `< fall` can NEVER take a settled Up
    machine down, no matter how the passes and fails interleave;
  * `mono_fall` — **monotone threshold semantics**: raising the fall
    threshold only preserves uptime (any burst survived at threshold `fall`
    is survived at any `fall' ≥ fall`);
  * decidability — states/probes have decidable equality and the machine is
    executable; `example`s below check concrete traces by `decide`.

The machine is per-(backend, probe-plane); its `up` verdict is snapshotted
into `Backend.healthy` (`Proxy.Basic`), which the selection algebra consumes.
-/

import Proxy.Basic

namespace Proxy

/-- Hysteresis thresholds. `rise` consecutive passes bring a Down backend Up;
`fall` consecutive failures bring an Up backend Down. Sane configs have both
≥ 1; ≥ 2 is what gives anti-flap (see `noFlap_fail`). -/
structure HealthGate where
  rise : Nat
  fall : Nat
deriving DecidableEq, Repr

/-- One probe outcome. -/
inductive Probe where
  | pass
  | fail
deriving DecidableEq, Repr

/-- Verdict + consecutive streak counters. Invariant kept informally: at most
one of the two streaks is nonzero (each probe resets the opposite streak). -/
structure HealthState where
  up : Bool
  passStreak : Nat
  failStreak : Nat
deriving DecidableEq, Repr

/-- A fresh backend, optimistically Up with clean streaks (the engine may
also start pessimistically; the theorems are stated from settled states of
either polarity). -/
def HealthState.initUp : HealthState := ⟨true, 0, 0⟩

/-- A settled Down state. -/
def HealthState.initDown : HealthState := ⟨false, 0, 0⟩

/-- One probe result. Streak accounting: a pass zeroes the fail streak and
extends the pass streak; if the machine is Down and the pass streak reaches
`rise`, the verdict flips to Up with clean streaks (dually for fail). -/
def hstep (g : HealthGate) (s : HealthState) (p : Probe) : HealthState :=
  match p with
  | .pass =>
    if s.up then ⟨true, s.passStreak + 1, 0⟩
    else if g.rise ≤ s.passStreak + 1 then ⟨true, 0, 0⟩
    else ⟨false, s.passStreak + 1, 0⟩
  | .fail =>
    if !s.up then ⟨false, 0, s.failStreak + 1⟩
    else if g.fall ≤ s.failStreak + 1 then ⟨false, 0, 0⟩
    else ⟨true, 0, s.failStreak + 1⟩

/-- Run a probe history, oldest first. -/
def hrun (g : HealthGate) (s : HealthState) : List Probe → HealthState
  | [] => s
  | p :: ps => hrun g (hstep g s p) ps

@[simp] theorem hrun_nil (g : HealthGate) (s : HealthState) :
    hrun g s [] = s := rfl

@[simp] theorem hrun_cons (g : HealthGate) (s : HealthState) (p : Probe)
    (ps : List Probe) : hrun g s (p :: ps) = hrun g (hstep g s p) ps := rfl

theorem hrun_append (g : HealthGate) (s : HealthState) (ps qs : List Probe) :
    hrun g s (ps ++ qs) = hrun g (hrun g s ps) qs := by
  induction ps generalizing s with
  | nil => rfl
  | cons p rest ih => rw [List.cons_append, hrun_cons, hrun_cons, ih]

theorem hrun_concat (g : HealthGate) (s : HealthState) (ps : List Probe)
    (p : Probe) : hrun g s (ps.concat p) = hstep g (hrun g s ps) p := by
  rw [List.concat_eq_append, hrun_append, hrun_cons, hrun_nil]

/-! ### Single-probe anti-flap -/

/-- **No flapping (Up).** With `fall ≥ 2`, one anomalous failure against a
settled Up machine does not flip the verdict. -/
theorem noFlap_fail {g : HealthGate} (h2 : 2 ≤ g.fall)
    {s : HealthState} (hup : s.up = true) (hsettle : s.failStreak = 0) :
    (hstep g s .fail).up = true := by
  simp only [hstep, hup, hsettle]
  have : ¬ g.fall ≤ 0 + 1 := by omega
  simp [this]

/-- **No flapping (Down).** With `rise ≥ 2`, one anomalous pass against a
settled Down machine does not flip the verdict: a dying backend does not
re-enter rotation off a single lucky probe. -/
theorem noFlap_pass {g : HealthGate} (h2 : 2 ≤ g.rise)
    {s : HealthState} (hdown : s.up = false) (hsettle : s.passStreak = 0) :
    (hstep g s .pass).up = false := by
  simp only [hstep, hdown, hsettle]
  have : ¬ g.rise ≤ 0 + 1 := by omega
  simp [this]

/-- Any single-step verdict flip is a threshold crossing: the machine never
changes its mind without the full consecutive streak. -/
theorem flip_requires_streak {g : HealthGate} {s : HealthState} {p : Probe}
    (hflip : (hstep g s p).up ≠ s.up) :
    (s.up = true  ∧ p = .fail ∧ g.fall ≤ s.failStreak + 1) ∨
    (s.up = false ∧ p = .pass ∧ g.rise ≤ s.passStreak + 1) := by
  cases p with
  | pass =>
    cases hup : s.up with
    | true => simp [hstep, hup] at hflip
    | false =>
      by_cases hr : g.rise ≤ s.passStreak + 1
      · exact Or.inr ⟨rfl, rfl, hr⟩
      · simp [hstep, hup, hr] at hflip
  | fail =>
    cases hup : s.up with
    | false => simp [hstep, hup] at hflip
    | true =>
      by_cases hf : g.fall ≤ s.failStreak + 1
      · exact Or.inl ⟨rfl, rfl, hf⟩
      · simp [hstep, hup, hf] at hflip

/-! ### Exact threshold semantics -/

/-- Generalized survival: an Up machine that has already absorbed `j`
consecutive failures absorbs `n` more without flipping, as long as the total
stays below the threshold. -/
theorem up_survives_below_fall' {g : HealthGate} (j n : Nat)
    (hlt : j + n < g.fall) :
    hrun g ⟨true, 0, j⟩ (List.replicate n .fail) = ⟨true, 0, j + n⟩ := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, hrun_cons]
    have hstep_eq : hstep g ⟨true, 0, j⟩ .fail = ⟨true, 0, j + 1⟩ := by
      have : ¬ g.fall ≤ j + 1 := by omega
      simp [hstep, this]
    rw [hstep_eq, ih (j + 1) (by omega)]
    have : j + 1 + n = j + (n + 1) := by omega
    rw [this]

/-- **Below the threshold, nothing flips**: from a settled Up state,
`n < fall` consecutive failures leave the machine Up. -/
theorem up_survives_below_fall {g : HealthGate} {n : Nat} (hlt : n < g.fall) :
    (hrun g .initUp (List.replicate n .fail)).up = true := by
  rw [HealthState.initUp, up_survives_below_fall' 0 n (by omega)]

/-- **At the threshold, it flips**: from a settled Up state, exactly `fall`
consecutive failures take the machine Down (with clean streaks). -/
theorem down_at_fall {g : HealthGate} (h1 : 1 ≤ g.fall) :
    hrun g .initUp (List.replicate g.fall .fail) = .initDown := by
  have hsplit : g.fall = (g.fall - 1) + 1 := by omega
  rw [HealthState.initUp, hsplit, List.replicate_succ']
  have hprefix := up_survives_below_fall' (g := g) 0 (g.fall - 1) (by omega)
  rw [Nat.zero_add] at hprefix
  rw [← List.concat_eq_append, hrun_concat, hprefix]
  have hlast : hstep g ⟨true, 0, g.fall - 1⟩ .fail = ⟨false, 0, 0⟩ := by
    have hc : g.fall ≤ (g.fall - 1) + 1 := by omega
    simp [hstep, hc]
  rw [hlast]
  rfl

/-- Dual generalized survival for the Down side. -/
theorem down_survives_below_rise' {g : HealthGate} (j n : Nat)
    (hlt : j + n < g.rise) :
    hrun g ⟨false, j, 0⟩ (List.replicate n .pass) = ⟨false, j + n, 0⟩ := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, hrun_cons]
    have hstep_eq : hstep g ⟨false, j, 0⟩ .pass = ⟨false, j + 1, 0⟩ := by
      have : ¬ g.rise ≤ j + 1 := by omega
      simp [hstep, this]
    rw [hstep_eq, ih (j + 1) (by omega)]
    have : j + 1 + n = j + (n + 1) := by omega
    rw [this]

/-- Below the rise threshold a Down machine stays Down… -/
theorem down_survives_below_rise {g : HealthGate} {n : Nat}
    (hlt : n < g.rise) :
    (hrun g .initDown (List.replicate n .pass)).up = false := by
  rw [HealthState.initDown, down_survives_below_rise' 0 n (by omega)]

/-- …and exactly `rise` consecutive passes bring it Up. -/
theorem up_at_rise {g : HealthGate} (h1 : 1 ≤ g.rise) :
    hrun g .initDown (List.replicate g.rise .pass) = .initUp := by
  have hsplit : g.rise = (g.rise - 1) + 1 := by omega
  rw [HealthState.initDown, hsplit, List.replicate_succ']
  have hprefix := down_survives_below_rise' (g := g) 0 (g.rise - 1) (by omega)
  rw [Nat.zero_add] at hprefix
  rw [← List.concat_eq_append, hrun_concat, hprefix]
  have hlast : hstep g ⟨false, g.rise - 1, 0⟩ .pass = ⟨true, 0, 0⟩ := by
    have hc : g.rise ≤ (g.rise - 1) + 1 := by omega
    simp [hstep, hc]
  rw [hlast]
  rfl

/-! ### Monotone threshold semantics -/

/-- **Monotonicity in the fall threshold.** A failure burst too short to take
the machine down at threshold `fall` is also too short at any higher
threshold: raising `fall` never converts an Up outcome into a Down one for
consecutive-failure bursts. (With `up_survives_below_fall`/`down_at_fall`
this pins the flip point as an exact, monotone function of the config.) -/
theorem mono_fall {g g' : HealthGate} (hmono : g.fall ≤ g'.fall) {n : Nat}
    (hsurvive : n < g.fall) :
    (hrun g' .initUp (List.replicate n .fail)).up = true :=
  up_survives_below_fall (by omega)

/-- Passes never take an Up machine down. -/
theorem up_stable_under_passes {g : HealthGate} (k n : Nat) :
    hrun g ⟨true, k, 0⟩ (List.replicate n .pass) = ⟨true, k + n, 0⟩ := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, hrun_cons]
    have hstep_eq : hstep g ⟨true, k, 0⟩ .pass = ⟨true, k + 1, 0⟩ := by
      simp [hstep]
    rw [hstep_eq, ih (k + 1)]
    have : k + 1 + n = k + (n + 1) := by omega
    rw [this]

theorem replicate_split {α : Type} (a b : Nat) (x : α) :
    List.replicate (a + b) x = List.replicate a x ++ List.replicate b x := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hone : a + 1 + b = (a + b) + 1 := by omega
    rw [hone, List.replicate_succ, ih, ← List.cons_append,
      ← List.replicate_succ]

/-- A Down machine recovers within any pass-burst at least `rise` long. -/
theorem recover_within {g : HealthGate} (h1 : 1 ≤ g.rise) {n : Nat}
    (hn : g.rise ≤ n) :
    (hrun g .initDown (List.replicate n .pass)).up = true := by
  have hsplit : n = g.rise + (n - g.rise) := by omega
  rw [hsplit, replicate_split, hrun_append, up_at_rise h1,
    HealthState.initUp, up_stable_under_passes]

/-- **Monotonicity in the rise threshold.** Lowering `rise` never converts a
recovery into a non-recovery: a pass burst long enough to recover at the
stricter threshold recovers at any laxer one. -/
theorem mono_rise {g g' : HealthGate} (hmono : g'.rise ≤ g.rise)
    (h1 : 1 ≤ g'.rise) {n : Nat} (hrecover : g.rise ≤ n) :
    (hrun g' .initDown (List.replicate n .pass)).up = true :=
  recover_within h1 (by omega)

/-! ### Trace-level anti-flap -/

/-- Length of the leading consecutive-failure run. -/
def leadingFails : List Probe → Nat
  | .fail :: ps => leadingFails ps + 1
  | _ => 0

/-- Longest consecutive-failure run anywhere in the trace. -/
def maxFailRun : List Probe → Nat
  | [] => 0
  | .pass :: ps => maxFailRun ps
  | .fail :: ps => Nat.max (leadingFails ps + 1) (maxFailRun ps)

theorem leadingFails_le_maxFailRun (ps : List Probe) :
    leadingFails ps ≤ maxFailRun ps := by
  induction ps with
  | nil => exact Nat.le_refl _
  | cons p rest ih =>
    cases p with
    | pass => simp [leadingFails, maxFailRun]
    | fail =>
      simp only [leadingFails, maxFailRun]
      exact Nat.le_max_left ..

/-- **Trace-level no-flap.** Take an Up machine that has already absorbed
`failStreak` consecutive failures. If the pending trace's longest failure run
is below the threshold — and the leading run doesn't complete the threshold
together with the already-absorbed streak — the machine stays Up through the
WHOLE trace, no matter how passes and failures interleave. Flapping requires
a genuine `fall`-long failure burst; sporadic anomalies can never accumulate
across intervening passes. -/
theorem noFlap_trace {g : HealthGate} {ps : List Probe} {s : HealthState}
    (hup : s.up = true)
    (hlead : s.failStreak + leadingFails ps < g.fall)
    (hrun_max : maxFailRun ps < g.fall) :
    (hrun g s ps).up = true := by
  induction ps generalizing s with
  | nil => simpa using hup
  | cons p rest ih =>
    cases p with
    | pass =>
      rw [hrun_cons]
      have hstep_eq : hstep g s .pass = ⟨true, s.passStreak + 1, 0⟩ := by
        simp [hstep, hup]
      rw [hstep_eq]
      have hmr : maxFailRun rest < g.fall := by
        simpa [maxFailRun] using hrun_max
      apply ih rfl
      · show (0 : Nat) + leadingFails rest < g.fall
        have hlf := leadingFails_le_maxFailRun rest
        omega
      · exact hmr
    | fail =>
      rw [hrun_cons]
      have hlead_eq : leadingFails (Probe.fail :: rest)
          = leadingFails rest + 1 := rfl
      have hnf : ¬ g.fall ≤ s.failStreak + 1 := by omega
      have hstep_eq : hstep g s .fail = ⟨true, 0, s.failStreak + 1⟩ := by
        simp [hstep, hup, hnf]
      rw [hstep_eq]
      have hmax_eq : maxFailRun (Probe.fail :: rest)
          = Nat.max (leadingFails rest + 1) (maxFailRun rest) := rfl
      have hle : maxFailRun rest
          ≤ Nat.max (leadingFails rest + 1) (maxFailRun rest) :=
        Nat.le_max_right ..
      apply ih rfl
      · show s.failStreak + 1 + leadingFails rest < g.fall
        omega
      · omega

/-! ### Decidability / executability

Verdict equality is decidable and the machine is executable; `decide` closes
concrete trace properties, which is what lets conformance vectors
(`health_state_transitions`-style rows) be checked against the model
mechanically. -/

example : Decidable ((hrun ⟨2, 3⟩ .initUp
    [.fail, .fail, .pass, .fail, .fail]).up = true) := inferInstance

/-- fall = 3: two failures, a pass, two more failures — never three in a row,
still Up. The interleaved pass resets the streak. -/
example :
    (hrun ⟨2, 3⟩ .initUp [.fail, .fail, .pass, .fail, .fail]).up = true := by
  decide

/-- fall = 3: three consecutive failures take it Down. -/
example :
    (hrun ⟨2, 3⟩ .initUp [.fail, .fail, .fail]).up = false := by decide

/-- rise = 2: one lucky pass does not resurrect a Down backend; two in a row
do. -/
example : (hrun ⟨2, 3⟩ .initDown [.pass]).up = false := by decide
example : (hrun ⟨2, 3⟩ .initDown [.pass, .pass]).up = true := by decide

/-- Flap sequence: fail-pass-fail-pass… never flips with fall ≥ 2. -/
example : (hrun ⟨2, 2⟩ .initUp
    [.fail, .pass, .fail, .pass, .fail, .pass, .fail, .pass]).up = true := by
  decide

end Proxy
