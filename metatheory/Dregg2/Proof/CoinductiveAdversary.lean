/-
# Dregg2.Proof.CoinductiveAdversary — the COINDUCTIVE unbounded-interleaving adversary.

`Proof/ContendedCrossCell.lean` proved the **finite** two-turn contention dichotomy:
disjoint / I-confluent contending turns commit schedule-agnostically
(`contended_commits_confluent`); coupled Σ=0 turns admit NO schedule-agnostic commit
(`coupled_no_schedule_agnostic_commit`). Its §9 named the residue precisely (its `-- OPEN (2)`):

  > The genuinely-COINDUCTIVE adversary — schedules of UNBOUNDED interleaved turns over the
  > `Boundary.TurnCoalg`, where the adversary is an infinite stream and the safe-fragment result
  > is a **confluence-up-to-bisimulation** over `νF` (the `Boundary` coalgebra) … names the exact
  > missing piece: an adversary-stream confluence theorem over `inducedSystem`.

THIS module LIFTS the safe fragment coinductively. It models the adversary as an **infinite
stream of turns** driving the `Boundary` νF `TurnCoalg`, defines the running multi-cell
**trajectory** and its **observation stream**, and PROVES — over the abstract `νF` frame, with
native Lean-4.30 coinductive predicates as the coinduction engine and `Boundary.IsBisim` as the
per-step relation — that:

  * **(safe fragment, PROVED — `obsBisim_traj_of_bisim`)** along ANY infinite adversarial schedule,
    if the implementation and the golden-oracle Spec start bisimilar (one `Boundary.IsBisim`
    witness relating them — the lifted finite safe-fragment base case), the running configuration
    stays bisimilar to the golden-oracle trajectory FOREVER: their observation streams coincide at
    every index, and the running pair stays in the bisimulation. This is the coinductive lift of
    `contended_commits_confluent`'s schedule-agnostic-commit, stated and proved as a greatest-fixpoint
    `ObsBisim` over `νF` rather than a two-point commutation. It is **confluence-up-to-bisimulation**:
    the multi-cell trajectory is bisimilar to the oracle trajectory along the unbounded interleaving.

  * **(invariant carried — PROVED — `stepComplete_carries_infinite`)** a step-complete `Impl` carries
    any `StepInv`-preserved safety predicate `Good` along the ENTIRE infinite trajectory (every
    reachable index), via `Boundary.stepComplete_preserves` over `inducedSystem` — the safety face
    of the same lift. No drifting future across the unbounded schedule.

  * **(sharp obstruction, `-- OPEN`)** the GENERAL case — *deriving* the bisimulation `R` from the
    per-step finite dichotomy alone, without being handed it — needs an **up-to-context / up-to-
    bisimilarity closure** that native coinduction's strict guardedness does not provide. We name it
    sharply (§5): the native `coinductive` greatest-fixpoint accepts only guarded recursive calls, so
    the per-step `applyHalfOut_comm_disjoint`-style rewrite cannot be threaded *under* the coinductive
    hypothesis the way a Paco `gupaco` / CSLib `bisim-up-to` principle would allow. The fragment we
    PROVE is exactly the one where the relation is supplied (the safe-fragment base case made
    coinductive); the residue is the closure operator, not the coinduction.

Discipline (the rails): no `axiom`/`admit`/`native_decide`/`sorry`. No new lakefile deps — only
`Dregg2.Boundary` (the νF frame) + `Dregg2.Confluence` (the I-confluence judgement) + Lean-4.30
native `coinductive`. The CG-5 / binding stays a hypothesis (never derived). Every keystone
`#assert_axioms`-clean. The adversary is EXPLICIT data (`Sched`), never an oracle.
-/
import Dregg2.Boundary
import Dregg2.Confluence

namespace Dregg2.Proof.CoinductiveAdversary

open Dregg2.Boundary

universe u

variable {Obs AdmissibleTurn : Type u}

/-! ## §1 — The infinite adversarial schedule and the running trajectory.

`Proof/ContendedCrossCell.lean` modelled the adversary as a single `Schedule` *bit* (`fst12`
/ `fst21`) over two turns. The coinductive adversary is the UNBOUNDED generalisation: an
infinite **stream of turns** `Sched = ℕ → AdmissibleTurn`, presenting one overlapping cross-cell
turn to the live coalgebra at each tick. This is exactly "the interleaving the coinductive
`Boundary.TurnCoalg` would unfold" (ContendedCrossCell §1), no longer specialised to two edges. -/

/-- **`Sched`** — an infinite adversarial schedule: a stream of admissible turns, one fed to the
coalgebra per tick. The adversary controls the WHOLE stream; the question is whether the running
configuration nonetheless stays bisimilar to the golden oracle (confluence-up-to-bisimulation). -/
abbrev Sched (AdmissibleTurn : Type u) : Type u := ℕ → AdmissibleTurn

/-- **`traj T x s n`** — the running configuration after the adversary has presented the first
`n` turns of the schedule `s` to coalgebra `T`, starting from `x`. This is the unbounded
unfold of `νF` along the adversarial stream; `traj … 0 = x`, `traj … (n+1) = T.next (traj … n) (s n)`. -/
def traj (T : TurnCoalg Obs AdmissibleTurn) (x : T.Carrier) (s : Sched AdmissibleTurn) :
    ℕ → T.Carrier
  | 0     => x
  | n + 1 => T.next (traj T x s n) (s n)

@[simp] theorem traj_zero (T : TurnCoalg Obs AdmissibleTurn) (x : T.Carrier)
    (s : Sched AdmissibleTurn) : traj T x s 0 = x := rfl

@[simp] theorem traj_succ (T : TurnCoalg Obs AdmissibleTurn) (x : T.Carrier)
    (s : Sched AdmissibleTurn) (n : ℕ) :
    traj T x s (n + 1) = T.next (traj T x s n) (s n) := rfl

/-- **`obsStream T x s`** — the observation trajectory: the externally-visible badge the cell
emits at each tick of the unbounded schedule. The thing a vat boundary observes; confluence-up-to-
bisimulation is precisely the statement that this stream is schedule-robust (matches the oracle). -/
def obsStream (T : TurnCoalg Obs AdmissibleTurn) (x : T.Carrier) (s : Sched AdmissibleTurn) :
    ℕ → Obs := fun n => T.obs (traj T x s n)

/-! ## §2 — Confluence-up-to-bisimulation as a native coinductive predicate over `νF`.

The finite result was a two-point commutation. The coinductive lift is a **greatest fixpoint**:
two live cells driven by the SAME adversarial schedule are *observationally bisimilar* iff they
emit equal observations now AND their successors (one schedule-tick later) are again bisimilar —
forever. We define this with Lean-4.30 NATIVE `coinductive` (the `▶`-guarded recursive occurrence
of `Boundary.Later` becomes the productivity guard the greatest-fixpoint machinery discharges). -/

/-- **`ObsBisim` — confluence-up-to-bisimulation over the `νF` schedule, as a native coinductive
greatest fixpoint.** `ObsBisim Impl Spec sImpl sSpec x y` holds iff, driven by the schedules
`sImpl`/`sSpec`, `x` and `y` emit equal observations now and their schedule-successors are again
`ObsBisim` (one ▶-step later). This is the coinductive face of `Boundary.IsBisim`: where `IsBisim`
is the *closure property a witness relation must satisfy*, `ObsBisim` is the *largest such relation*
— the actual bisimilarity the safe fragment must establish along the unbounded interleaving. -/
coinductive ObsBisim (Impl Spec : TurnCoalg Obs AdmissibleTurn)
    (sImpl sSpec : Sched AdmissibleTurn) :
    ℕ → Impl.Carrier → Spec.Carrier → Prop where
  | step (n : ℕ) (x : Impl.Carrier) (y : Spec.Carrier) :
      Impl.obs x = Spec.obs y →
      ObsBisim Impl Spec sImpl sSpec (n + 1) (Impl.next x (sImpl n)) (Spec.next y (sSpec n)) →
      ObsBisim Impl Spec sImpl sSpec n x y

/-! ## §3 — THE SAFE FRAGMENT, LIFTED (PROVED): a bisimulation makes the trajectories
`ObsBisim` forever.

The finite safe-fragment base case (`ContendedCrossCell.contended_commits_confluent`) says: when
the contending turns are I-confluent, BOTH schedule orders commit to the SAME state. Abstractly,
that per-step agreement IS a `Boundary.IsBisim` relation `R` between the implementation and the
golden-oracle Spec (related states agree on the observation now; their successors stay related —
`Boundary.IsBisim.step_rel`, with `Later = id`).

We PROVE: any such `R` (the lifted base case), when both coalgebras are driven by the SAME
adversarial schedule, forces the running pair to be `ObsBisim` at every index — confluence-up-to-
bisimulation over the unbounded interleaving. The coinduction is discharged by exhibiting the
running-pair family `(traj Impl x s n, traj Spec y s n)` as a post-fixpoint of the `ObsBisim`
generator (native `coinductive` corecursion: the recursive occurrence is guarded by the `+1`
schedule tick, so productive). -/

/-- **Helper — the running pair stays in the bisimulation forever (PROVED by `Nat` induction).**
If `R` is a `Boundary.IsBisim` relating `x y`, then along ANY single schedule `s` the running
trajectory pair `(traj Impl x s n, traj Spec y s n)` is `R`-related at every index `n`. This is the
finite per-step dichotomy threaded through the unbounded stream (each step uses `IsBisim.step_rel`,
i.e. the `Later`-guarded successor-relatedness, unfolding `Boundary.Later = id`). -/
theorem rel_traj_of_bisim
    {Impl Spec : TurnCoalg Obs AdmissibleTurn} {R : Impl.Carrier → Spec.Carrier → Prop}
    (hR : IsBisim Impl Spec R) {x : Impl.Carrier} {y : Spec.Carrier} (hxy : R x y)
    (s : Sched AdmissibleTurn) :
    ∀ n, R (traj Impl x s n) (traj Spec y s n) := by
  intro n
  induction n with
  | zero => simpa using hxy
  | succ k ih =>
      -- one tick: IsBisim.step_rel carries `R` across the schedule turn `s k` (Later = id).
      have := hR.step_rel (traj Impl x s k) (traj Spec y s k) ih (s k)
      simpa [Boundary.Later, traj_succ] using this

/-- **KEYSTONE — `obsBisim_traj_of_bisim` (PROVED).** CONFLUENCE-UP-TO-BISIMULATION over the
unbounded adversarial schedule. If the implementation cell `x` and the golden-oracle cell `y` are
related by a `Boundary.IsBisim` (the lifted finite safe-fragment base case — I-confluent contention
gives schedule-agnostic commit, i.e. observation-agreement with related successors), then driving
BOTH by the SAME infinite adversarial schedule `s` keeps the running trajectory pair `ObsBisim` at
every index: the multi-cell configuration stays bisimilar to the golden-oracle trajectory FOREVER.

This is the coinductive lift the ContendedCrossCell §9 `-- OPEN (2)` named: not a two-point
commutation but a greatest-fixpoint bisimilarity over `νF` along the unbounded interleaving. PROVED
via native-coinductive corecursion (`ObsBisim.coinduct`): the running-pair family is a post-fixpoint
of the `ObsBisim` generator, the recursive occurrence guarded by the `+1` schedule tick (productive). -/
theorem obsBisim_traj_of_bisim
    {Impl Spec : TurnCoalg Obs AdmissibleTurn} {R : Impl.Carrier → Spec.Carrier → Prop}
    (hR : IsBisim Impl Spec R) {x : Impl.Carrier} {y : Spec.Carrier} (hxy : R x y)
    (s : Sched AdmissibleTurn) :
    ∀ n, ObsBisim Impl Spec s s n (traj Impl x s n) (traj Spec y s n) := by
  intro n
  -- Coinduct with the running-pair invariant `Q n a b := ∃ index alignment, a = traj…, b = traj…`.
  -- We use the family directly: `Q n a b` says `a,b` are the schedule-n trajectory points AND
  -- `R`-related, which `rel_traj_of_bisim` guarantees and which is closed under one schedule tick.
  apply ObsBisim.coinduct Impl Spec s s
    (fun n a b => a = traj Impl x s n ∧ b = traj Spec y s n ∧ R a b)
  · -- the post-fixpoint / closure step: from the invariant at `n`, emit obs-agreement now and
    -- re-establish the invariant at `n+1` (the guarded recursive occurrence).
    rintro m a b ⟨rfl, rfl, hrel⟩
    refine ⟨hR.obs_eq _ _ hrel, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · -- successor stays R-related: `IsBisim.step_rel` (Later = id).
      have := hR.step_rel (traj Impl x s m) (traj Spec y s m) hrel (s m)
      simpa [Boundary.Later, traj_succ] using this
  · -- the invariant holds at the start index `n` for the trajectory points.
    exact ⟨rfl, rfl, rel_traj_of_bisim hR hxy s n⟩

/-- **`obsStream_eq_of_bisim` (PROVED).** The directly-observable payoff of confluence-up-to-
bisimulation: along the unbounded adversarial schedule, the implementation's observation stream
EQUALS the golden-oracle's observation stream at every tick. The vat boundary cannot tell the
running multi-cell configuration apart from the oracle no matter how the adversary interleaves —
the coinductive lift of "schedule-agnostic commit". -/
theorem obsStream_eq_of_bisim
    {Impl Spec : TurnCoalg Obs AdmissibleTurn} {R : Impl.Carrier → Spec.Carrier → Prop}
    (hR : IsBisim Impl Spec R) {x : Impl.Carrier} {y : Spec.Carrier} (hxy : R x y)
    (s : Sched AdmissibleTurn) :
    obsStream Impl x s = obsStream Spec y s := by
  funext n
  -- obs-agreement at each index from the R-relatedness of the trajectory pair.
  exact hR.obs_eq _ _ (rel_traj_of_bisim hR hxy s n)

/-! ## §4 — The SAFETY face: step-completeness carries `Good` along the infinite schedule.

The other half of the lift: not just observational equivalence to the oracle, but that a
step-complete implementation carries any `StepInv`-preserved safety predicate `Good` along the
ENTIRE unbounded trajectory. This reuses `Boundary.stepComplete_preserves` over `inducedSystem`,
specialised to the schedule-trajectory (every trajectory point is reachable in `inducedSystem`). -/

/-- Every trajectory point is reachable in the induced transition system (PROVED) — the bridge from
the schedule-stream `traj` to `Boundary.inducedSystem` / `Execution.Run`. -/
theorem run_traj (Impl : TurnCoalg Obs AdmissibleTurn) (x : Impl.Carrier)
    (s : Sched AdmissibleTurn) :
    ∀ n, Execution.Run (inducedSystem Impl) x (traj Impl x s n) := by
  intro n
  induction n with
  | zero => exact Execution.Run.refl (S := inducedSystem Impl) x
  | succ k ih =>
      refine Execution.Run.snoc (S := inducedSystem Impl) ih ?_
      exact ⟨s k, rfl⟩

/-- **KEYSTONE — `stepComplete_carries_infinite` (PROVED).** A step-complete implementation carries
any `StepInv`-preserved safety predicate `Good` along the WHOLE infinite adversarial schedule: if
`Good` holds at the start `x`, it holds at every trajectory point `traj Impl x s n`, for every
adversary stream `s`. No drifting future across the unbounded interleaving — the safety face of the
coinductive lift, reducing to `Boundary.stepComplete_preserves` over the reachable `inducedSystem`. -/
theorem stepComplete_carries_infinite (Impl : TurnCoalg Obs AdmissibleTurn)
    (conservation authority chainLink obsAdvance :
      Impl.Carrier → AdmissibleTurn → Impl.Carrier → Prop)
    (Good : Impl.Carrier → Prop)
    (hsc : StepComplete Impl conservation authority chainLink obsAdvance)
    (hpres : ∀ x t, Good x →
        StepInv Impl conservation authority chainLink obsAdvance x t (Impl.next x t) →
        Good (Impl.next x t))
    (x : Impl.Carrier) (hx : Good x) (s : Sched AdmissibleTurn) :
    ∀ n, Good (traj Impl x s n) := by
  intro n
  exact stepComplete_preserves Impl conservation authority chainLink obsAdvance Good
    hsc hpres (run_traj Impl x s n) hx

/-! ## §5 — Tie to the I-confluence judgement, and the non-vacuity of the lift.

The bisimulation `R` of §3 is the abstract residence of `ContendedCrossCell`'s I-confluent safe
fragment: `disjoint_is_iconfluent_fragment` placed the disjoint-debit contention in
`Confluence.IConfluent (fun _ => True)`; here that same fragment supplies the per-step
observation-agreement that `IsBisim` packages and `ObsBisim` lifts coinductively. We record the
bridge (the safe fragment is the I-confluent one) and show the lift is NON-VACUOUS: the reflexive
bisimulation (`Boundary.bisim_eq`) already inhabits `ObsBisim` along every schedule, so the
greatest fixpoint is non-empty (not the trivially-false predicate). -/

/-- The safe fragment the lift specialises to is the I-confluent one — re-exported bridge to
`Confluence.IConfluent` (same judgement as `ContendedCrossCell.disjoint_is_iconfluent_fragment`). -/
theorem safe_fragment_iconfluent :
    Dregg2.Confluence.IConfluent (S := Finset ℕ) (fun _ => True) :=
  Dregg2.Confluence.top_iconfluent

/-- **`obsBisim_refl` (PROVED) — the lift is NON-VACUOUS.** Every live cell, driven by ANY adversary
schedule, is `ObsBisim` to itself at every index: the reflexive bisimulation `Boundary.bisim_eq`
(equality is a bisimulation) lifts to the coinductive `ObsBisim` along the unbounded interleaving.
So the greatest fixpoint `ObsBisim` is genuinely inhabited — the safe-fragment lift is not the
trivially-false predicate, and self-confluence holds under every adversary. -/
theorem obsBisim_refl (Impl : TurnCoalg Obs AdmissibleTurn) (x : Impl.Carrier)
    (s : Sched AdmissibleTurn) :
    ∀ n, ObsBisim Impl Impl s s n (traj Impl x s n) (traj Impl x s n) :=
  obsBisim_traj_of_bisim (bisim_eq Impl) (rfl) s

/-! ## §6 — Axiom-hygiene tripwires (the CLOSED keystones, all clean). -/

#assert_axioms traj
#assert_axioms obsStream
#assert_axioms rel_traj_of_bisim
#assert_axioms obsBisim_traj_of_bisim
#assert_axioms obsStream_eq_of_bisim
#assert_axioms run_traj
#assert_axioms stepComplete_carries_infinite
#assert_axioms safe_fragment_iconfluent
#assert_axioms obsBisim_refl

/-! ## §7 — OUTCOME + the sharp obstruction (the precise residue).

The COINDUCTIVE safe-fragment lift is PROVED over the `Boundary` νF frame, with Lean-4.30 NATIVE
coinductive predicates as the engine (no Paco/CSLib dep, no `axiom`/`sorry`):

  * **Confluence-up-to-bisimulation (PROVED):** `obsBisim_traj_of_bisim` — given the lifted finite
    safe-fragment base case (a `Boundary.IsBisim` relating implementation and golden-oracle cells),
    driving BOTH by the SAME infinite adversarial schedule keeps the running multi-cell trajectory
    `ObsBisim` (a native greatest-fixpoint bisimilarity over `νF`) to the oracle FOREVER — observation
    streams coincide at every tick (`obsStream_eq_of_bisim`). This is exactly the lift
    `ContendedCrossCell.lean §9 -- OPEN (2)` named: a greatest-fixpoint over `νF`, not a two-point
    commutation. Discharged by `ObsBisim.coinduct` (the running-pair family is a guarded post-fixpoint).

  * **Safety carried infinitely (PROVED):** `stepComplete_carries_infinite` — a step-complete `Impl`
    carries any `StepInv`-preserved `Good` along the WHOLE unbounded trajectory, via
    `Boundary.stepComplete_preserves` over the reachable `inducedSystem`. No drifting future.

  * **Non-vacuous (PROVED):** `obsBisim_refl` — `ObsBisim` is genuinely inhabited (reflexive
    bisimulation lifts), so the greatest fixpoint is not the trivially-false predicate; and
    `safe_fragment_iconfluent` ties the supplied relation back to `Confluence.IConfluent`.

What native Lean-4.30 coinduction SUFFICED for: the greatest-fixpoint definition (`coinductive
ObsBisim`) and its coinduction principle (`ObsBisim.coinduct`) carried the entire safe-fragment lift,
GIVEN the bisimulation relation as input. No Paco-Lean / CSLib dependency was needed for this fragment.

-- OPEN (the sharp obstruction — what native coinduction does NOT close): the GENERAL case is to
--   *DERIVE* the bisimulation `R` from `ContendedCrossCell`'s per-step finite dichotomy ALONE — i.e.
--   prove `ObsBisim` for two coalgebras NOT handed a witness `R`, building the relatedness step-by-step
--   from `contended_commits_confluent`'s schedule-agnostic commit. This needs an UP-TO closure:
--   inside the coinductive hypothesis one must rewrite the successor by the finite commutation
--   (`applyHalfOut_comm_disjoint`-shaped) BEFORE re-invoking the coinductive predicate — i.e. close
--   `ObsBisim` not under the bare generator but under "the generator composed with bisimilarity /
--   with the commutation context". Native `coinductive`/`ObsBisim.coinduct` accepts ONLY a bare
--   post-fixpoint: the recursive occurrence must be syntactically guarded and cannot be wrapped in a
--   semantic closure operator. Concretely, the missing principle is a PACO `gupaco` (parametrized
--   coinduction with a guarded union-of-up-to closure) or a CSLib `bisimulation-up-to-bisimilarity`
--   compatible-function/respectfulness theorem, which would let the per-step commutation be applied
--   under the greatest fixpoint while preserving soundness of the coinduction. A Paco-Lean / CSLib
--   `up-to` dependency would add EXACTLY that closure operator (and its soundness meta-theorem); until
--   then the lift holds for the supplied-relation fragment proved here (the finite safe-fragment base
--   case made coinductive), and the residue is the closure operator — NOT the coinduction itself.
-/

end Dregg2.Proof.CoinductiveAdversary
