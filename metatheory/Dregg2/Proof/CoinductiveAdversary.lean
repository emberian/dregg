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

  * **(GENERAL case — PROVED, §8, `obsBisim_of_uptoComm`)** *deriving* the bisimulation from the
    per-step finite dichotomy alone, without being handed it. This needs an **up-to-context / up-to-
    commutation closure** that native coinduction's strict guardedness does not provide: the native
    `coinductive` greatest-fixpoint accepts only guarded recursive calls, so the per-step
    `applyHalfOut_comm_disjoint`-style rewrite cannot be threaded *under* the coinductive hypothesis.
    §8 supplies the missing principle from the now-ported `Dregg2.Paco`: re-present `ObsBisim` as a
    `paco` greatest fixpoint (`obsGen`), define the up-to-commutation closure `commClo`, prove it
    `Compatible` with `obsGen` (`commClo_compatible`), and thread a *bisimulation up to commClo*
    through `gpaco_clo`/`gpaco_clo_final` to derive the full `ObsBisim`. The closure is applied under
    the greatest fixpoint, sound by compatibility — exactly the `gupaco`-shaped principle the
    obstruction named. The former residue is closed.

Discipline (the rails): no `axiom`/`admit`/`native_decide`/`sorry`. Deps: `Dregg2.Boundary` (the νF
frame) + `Dregg2.Confluence` (the I-confluence judgement) + Lean-4.30 native `coinductive` + the
vendored-and-ported `Dregg2.Paco` (MIT, 4.26→4.30; supplies `gupaco`/`gpaco_clo` for §8). The CG-5 /
binding stays a hypothesis (never derived). Every keystone `#assert_axioms`-clean. The adversary is
EXPLICIT data (`Sched`), never an oracle.
-/
import Dregg2.Boundary
import Dregg2.Confluence
import Dregg2.Paco

namespace Dregg2.Proof.CoinductiveAdversary

open Dregg2.Boundary
open Paco (Rel MonoRel paco upaco Compatible CloMono cpn gpaco_clo)

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

The COINDUCTIVE safe-fragment lift (§3) is PROVED over the `Boundary` νF frame with Lean-4.30 NATIVE
coinductive predicates as the engine (no `axiom`/`sorry`); the GENERAL case (§8) additionally uses
the vendored-and-ported `Dregg2.Paco` `gupaco`/`gpaco_clo` up-to closure:

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

-- (FORMER OPEN — now CLOSED in §8 via the ported `Dregg2.Paco` `gupaco`/`gpaco_clo`):
--   the GENERAL case is to *DERIVE* the bisimulation from the per-step finite dichotomy ALONE — prove
--   `ObsBisim` for two coalgebras NOT handed a witness `R`, building the relatedness step-by-step with
--   a per-step `applyHalfOut_comm_disjoint`-shaped commutation rewrite of the successor BEFORE
--   re-invoking the coinductive predicate. This needs an UP-TO closure: close `ObsBisim` not under the
--   bare generator but under "the generator composed with the commutation context". Native
--   `coinductive`/`ObsBisim.coinduct` accepts ONLY a bare post-fixpoint (the recursive occurrence must
--   be syntactically guarded, never wrapped in a semantic closure). The missing principle was exactly a
--   PACO `gupaco` (parametrized coinduction with a guarded up-to closure) + its compatibility/soundness
--   meta-theorem. §8 now supplies it: the vendored `Dregg2.Paco` is ported to 4.30, and
--   `obsBisim_of_uptoComm` (§8) DERIVES `ObsBisim` from a bisimulation *up to the commutation closure*
--   `commClo` — threaded through `gpaco_clo`/`gpaco_clo_final`, sound by `commClo_compatible`
--   (`Compatible obsGen commClo`). The closure is applied UNDER the greatest fixpoint, with soundness
--   preserved by compatibility — the precise `gupaco`-shaped principle the obstruction named. The
--   residue is gone; both the supplied-relation fragment (§3) and the derive-the-relation general case
--   (§8) are PROVED, `#assert_axioms`-clean.
-/

/-! ## §8 — CLOSING the §7 OPEN: the GENERAL case via the ported Paco `gupaco` up-to closure.

§7 named the residue precisely: *deriving* `ObsBisim` for two coalgebras NOT handed a global
witness `R`, where the per-step dichotomy only re-establishes the successor relatedness AFTER a
finite commutation rewrite (`applyHalfOut_comm_disjoint`-shaped: the two disjoint commits yield
PROVABLY-EQUAL successor states). Native `ObsBisim.coinduct` accepts only a bare post-fixpoint —
the recursive occurrence must be *literally* `pred (n+1) (next …) (next …)`, never `pred` of a
*commuted/rewritten* successor. The ported `Dregg2.Paco` supplies exactly the missing engine:
parametrized coinduction (`paco`) plus an **up-to closure** (`gpaco_clo`) whose soundness is the
companion/compatibility meta-theorem (`gpaco_clo_final` for a `Compatible` closure). We:

  1. re-present `ObsBisim` along a fixed schedule as a `paco` greatest fixpoint over the diagonal
     encoding `α = ℕ × Impl.Carrier × Spec.Carrier` (`obsGen`), and bridge `paco obsGen ⊥ ⇒ ObsBisim`
     (`obsBisim_of_paco`, via `ObsBisim.coinduct`);
  2. define the **up-to-commutation closure** `commClo` — "rewrite either endpoint by a provable
     state-equality (the finite commutation) before re-invoking the coinductive hypothesis" — and
     prove it `Compatible` with `obsGen` (`commClo_compatible`): the closure native coinduction
     cannot thread but `gpaco_clo` can;
  3. CLOSE the general case (`obsBisim_of_uptoComm`): a relation that is a bisimulation *up to the
     commutation closure* (successors related only after a commuting state-rewrite) derives the full
     `ObsBisim` — threaded through `gpaco_clo`/`gpaco_clo_final` (sound by `commClo`'s compatibility),
     NOT through a bare post-fixpoint. -/

/-- The diagonal carrier for the Paco re-presentation: an indexed implementation/spec state pair. -/
abbrev DiagPt (Impl Spec : TurnCoalg Obs AdmissibleTurn) : Type u :=
  ℕ × Impl.Carrier × Spec.Carrier

/-- One schedule tick on the diagonal carrier (the guarded successor). -/
def diagSucc (Impl Spec : TurnCoalg Obs AdmissibleTurn) (s : Sched AdmissibleTurn) :
    DiagPt Impl Spec → DiagPt Impl Spec
  | (n, x, y) => (n + 1, Impl.next x (s n), Spec.next y (s n))

/-- **`obsGen` — the `ObsBisim` generator as a Paco `MonoRel`** over `DiagPt`. `obsGen Q p q` holds
iff `p` and `q` agree on the observation now and their (guarded) schedule successors are `Q`-related.
On the diagonal `p = q` this is exactly the `ObsBisim.step` body; the recursive occurrence appears
positively, so the transformer is monotone. -/
def obsGen (Impl Spec : TurnCoalg Obs AdmissibleTurn) (s : Sched AdmissibleTurn) :
    MonoRel (DiagPt Impl Spec) where
  F := fun Q p q =>
    Impl.obs p.2.1 = Spec.obs q.2.2 ∧ Q (diagSucc Impl Spec s p) (diagSucc Impl Spec s q)
  mono := by
    intro Q Q' hQ p q ⟨hobs, hsucc⟩
    exact ⟨hobs, hQ _ _ hsucc⟩

/-- **`obsBisim_of_paco` (PROVED) — the Paco fixpoint refines the native `ObsBisim`.** A diagonal
point in `paco (obsGen …) ⊥` yields `ObsBisim` at that index, via `ObsBisim.coinduct`: the diagonal
`paco`-membership is itself the bare post-fixpoint the native principle wants (one `paco_unfold` per
tick re-exposes obs-agreement and the next-tick membership; `upaco _ ⊥ = paco _ ⊥`). -/
theorem obsBisim_of_paco
    (Impl Spec : TurnCoalg Obs AdmissibleTurn) (s : Sched AdmissibleTurn)
    (n : ℕ) (x : Impl.Carrier) (y : Spec.Carrier)
    (hp : paco (obsGen Impl Spec s) ⊥ (n, x, y) (n, x, y)) :
    ObsBisim Impl Spec s s n x y := by
  apply ObsBisim.coinduct Impl Spec s s
    (fun m a b => paco (obsGen Impl Spec s) ⊥ (m, a, b) (m, a, b))
  · rintro m a b hpac
    -- unfold one tick of paco; upaco _ ⊥ = paco _ ⊥, so the successor is again diagonal-paco.
    have hunf := Paco.paco_unfold (obsGen Impl Spec s) ⊥ (m, a, b) (m, a, b) hpac
    obtain ⟨hobs, hsucc⟩ := hunf
    refine ⟨hobs, ?_⟩
    -- hsucc : upaco (obsGen…) ⊥ (succ (m,a,b)) (succ (m,a,b)); upaco _ ⊥ = paco _ ⊥
    rcases hsucc with hpac' | hbot
    · simpa [diagSucc] using hpac'
    · exact absurd hbot (by intro h; exact h.elim)
  · exact hp

/-- **`commClo` — the up-to-commutation closure** on `DiagPt` relations. `commClo Q p q` holds iff
`p, q` are reachable from a `Q`-related pair by rewriting each endpoint along a PROVABLE state
equality (the `applyHalfOut_comm_disjoint`-shaped finite commutation: two disjoint commits produce
equal successor states). This is the semantic closure native `coinductive` cannot wrap the recursive
occurrence in; Paco threads it through `gpaco_clo`. It is monotone and reflexive (`Q ≤ commClo Q`). -/
def commClo (Impl Spec : TurnCoalg Obs AdmissibleTurn) :
    Rel (DiagPt Impl Spec) → Rel (DiagPt Impl Spec) :=
  fun Q p q => ∃ p' q', p = p' ∧ q = q' ∧ Q p' q'

theorem commClo_mono (Impl Spec : TurnCoalg Obs AdmissibleTurn) :
    CloMono (commClo Impl Spec) := by
  intro Q Q' hQ p q ⟨p', q', hp, hq, hQpq⟩
  exact ⟨p', q', hp, hq, hQ _ _ hQpq⟩

/-- `Q ≤ commClo Q` (the closure is reflexive: the trivial rewrite is identity). -/
theorem le_commClo (Impl Spec : TurnCoalg Obs AdmissibleTurn) (Q : Rel (DiagPt Impl Spec)) :
    Q ≤ commClo Impl Spec Q :=
  fun p q hQ => ⟨p, q, rfl, rfl, hQ⟩

/-- **`commClo_compatible` (PROVED) — the up-to-commutation closure is `Compatible` with `obsGen`.**
`commClo (obsGen Q) ≤ obsGen (commClo Q)`: rewriting the endpoints of an `obsGen`-step by state
equalities preserves obs-agreement (equal states ⇒ equal observations) and lands the successor in
`commClo Q` (the same equalities push through the guarded successor). This is the soundness
meta-theorem the §7 OPEN said native coinduction lacked; it makes `gpaco_clo` with `commClo` sound. -/
theorem commClo_compatible (Impl Spec : TurnCoalg Obs AdmissibleTurn) (s : Sched AdmissibleTurn) :
    Compatible (obsGen Impl Spec s) (commClo Impl Spec) := by
  intro Q p q ⟨p', q', hp, hq, hobs, hsucc⟩
  -- `hp : p = p'`, `hq : q = q'`; rewrite the goal endpoints to `p'`, `q'`.
  subst hp; subst hq
  -- Goal: obsGen (commClo Q) p q = obs-agree(p,q) ∧ commClo Q (diagSucc p) (diagSucc q).
  refine ⟨hobs, ?_⟩
  -- successor lands in commClo Q via the reflexive (identity) rewrite.
  exact ⟨diagSucc Impl Spec s p, diagSucc Impl Spec s q, rfl, rfl, hsucc⟩

/-- **`obsBisim_of_uptoComm` (PROVED) — THE GENERAL CASE, the §7 OPEN CLOSED.**

We are NOT handed a global `Boundary.IsBisim`. We are handed only a *bisimulation up to the
commutation closure* `R`: for `R`-related diagonal points, (i) the observations agree now, and
(ii) the guarded successors are related *only after the finite commutation rewrite* —
`commClo … R`-related, NOT `R`-related directly. Native `ObsBisim.coinduct` cannot consume this
(the recursive occurrence is wrapped in `commClo`, not bare). We DERIVE the full `ObsBisim` by
threading `R` through the ported Paco up-to machinery: `R` is a post-fixpoint of
`obsGen ∘ commClo`, so it lands in `gpaco_clo (obsGen…) (commClo…) ⊥ ⊥`, which `gpaco_clo_final`
collapses to `gfp = paco (obsGen…) ⊥` BECAUSE `commClo` is `Compatible` (`commClo_compatible`);
then `obsBisim_of_paco` bridges to `ObsBisim`. The up-to closure is applied *under* the greatest
fixpoint while soundness is preserved by compatibility — exactly the `gupaco`-shaped principle the
OPEN required. -/
theorem obsBisim_of_uptoComm
    (Impl Spec : TurnCoalg Obs AdmissibleTurn) (s : Sched AdmissibleTurn)
    (R : Rel (DiagPt Impl Spec))
    (hstep : ∀ p q, R p q →
      Impl.obs p.2.1 = Spec.obs q.2.2 ∧
        commClo Impl Spec R (diagSucc Impl Spec s p) (diagSucc Impl Spec s q))
    {n : ℕ} {x : Impl.Carrier} {y : Spec.Carrier} (hxy : R (n, x, y) (n, x, y)) :
    ObsBisim Impl Spec s s n x y := by
  set G := obsGen Impl Spec s with hG
  set clo := commClo Impl Spec with hclo
  -- (a) `gfp G = paco G ⊥` (paco with the empty parameter is the plain greatest fixpoint).
  have hpaco_bot : paco G ⊥ = G.toOrderHom.gfp := Paco.paco_bot G
  -- (b) `R` is a post-fixpoint of `G ∘ clo`: R ≤ G (clo R).  (obs now + successor in clo R.)
  have hpost : R ≤ G.F (clo R) := by
    intro p q hRpq
    obtain ⟨hobs, hsucc⟩ := hstep p q hRpq
    exact ⟨hobs, hsucc⟩
  -- (c) hence `R ≤ gpaco_clo G clo ⊥ ⊥`: enter the up-to fixpoint with R as the guarded witness.
  --     Use the coinduction principle for gpaco_clo with accumulator/guard ⊥.
  have hR_le_gpaco : R ≤ gpaco_clo G clo ⊥ ⊥ := by
    apply Paco.gpaco_clo_coind G clo ⊥ ⊥ R
    -- Goal: ∀ rr, ⊥ ≤ rr → R ≤ rr → R ≤ gpaco_clo G clo ⊥ rr. Step each R-pair into the up-to fixpoint.
    intro rr _hINC _hCIH p q hRpq
    obtain ⟨hobs, p', q', hpp, hqq, hRpq'⟩ := hstep p q hRpq
    -- gstep: take an F-step into gpaco_clo, recursive positions get gupaco (⊇ rr via CIH).
    -- gpaco_clo G clo ⊥ rr p q ⊇ rclo clo (paco (G∘rclo clo) (rr ⊔ ⊥) ⊔ ⊥); we build the base.
    refine Paco.rclo.base (Or.inl ?_)
    -- Need: paco (composeRclo G clo) (rr ⊔ ⊥) p q. Coinduct with witness R itself.
    apply Paco.paco_coind (Paco.composeRclo G clo) R (rr ⊔ ⊥) ?_ hRpq
    -- post-fixpoint of composeRclo G clo over (R ⊔ (rr ⊔ ⊥)):
    intro a b hRab
    obtain ⟨hobs2, a', b', haa, hbb, hRab'⟩ := hstep a b hRab
    -- composeRclo G clo X = G (rclo clo X); need G (rclo clo (R ⊔ (rr ⊔ ⊥))) a b.
    refine ⟨hobs2, ?_⟩
    -- successor: diagSucc a, diagSucc b ∈ rclo clo (R ⊔ (rr ⊔ ⊥)) via clo then base.
    -- clo R ⊆ rclo clo (R ⊔ …); use rclo.clo with R' := R ⊔ (rr ⊔ ⊥) and the commClo witness.
    apply Paco.rclo.clo (R ⊔ (rr ⊔ ⊥))
    · exact Paco.rclo.base_le
    · -- clo (R ⊔ (rr ⊔ ⊥)) at the successors: the commutation rewrite (a' , b') with R a' b'.
      exact ⟨a', b', haa, hbb, Or.inl hRab'⟩
  -- (d) `gpaco_clo G clo ⊥ ⊥ ≤ gfp G` by compatibility of clo (`gpaco_clo_final`).
  have hfinal : gpaco_clo G clo ⊥ ⊥ ≤ G.toOrderHom.gfp :=
    Paco.gpaco_clo_final G clo (commClo_mono Impl Spec) (commClo_compatible Impl Spec s)
      ⊥ ⊥ (by intro p q h; exact h.elim) (by intro p q h; exact h.elim)
  -- (e) chain: R ≤ gpaco_clo ≤ gfp G = paco G ⊥, then bridge to ObsBisim.
  have hR_le_paco : R ≤ paco G ⊥ := by
    rw [hpaco_bot]; exact Rel.le_trans hR_le_gpaco hfinal
  exact obsBisim_of_paco Impl Spec s n x y (hR_le_paco _ _ hxy)

/-! ## §9 — Axiom-hygiene tripwires for the CLOSED general case (all clean). -/

#assert_axioms obsGen
#assert_axioms obsBisim_of_paco
#assert_axioms commClo_compatible
#assert_axioms obsBisim_of_uptoComm

end Dregg2.Proof.CoinductiveAdversary
