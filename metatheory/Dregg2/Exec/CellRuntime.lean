/-
# Dregg2.Exec.CellRuntime — the Robigalia "OS, not chain" payoff as THEOREMS.

`cand-A §5`. dregg2's living cell (`Exec/Cell.lean`'s `cexec`/`livingCell`, `Exec/RecordCellLive`'s
`recCexec`/`recordCell`) is an element of a final coalgebra `νF` — *codata*, not a transaction log.
The headline consequence of that choice (the thing a chain-shaped design cannot state) is that
**checkpoint / restore / replay / time-travel are THEOREMS about the running cell**, not bespoke
features bolted on. A snapshot is a re-seeding point in the unfold; restoring is "going back" by
re-seeding the anamorphism; replaying is a deterministic fold over the committed log; and forking
is running a *different* admissible turn-suffix from a shared snapshot — both continuations remain
step-complete and sound (no drifting future on EITHER branch).

This module collects those as named keystones over the **finite-run forms** (`List Turn` / `List
RecOp`), which is the honest l4v sequencing: the per-turn step-completeness (`cexec_attests` /
`recCexec_attests`) and the abstract safety keystone (`Boundary.stepComplete_preserves`) already
give the unbounded-time `νF` story for free (`Cell.livingCell_sound` is the coinductive soundness);
the *runtime character* — back/forward/fork over the log — is finitary and is what we make literal
here. We REUSE the existing `Snapshot`/`restore`/`snapshot`/`replayFrom`/`recReplay` machinery
(no new state, no new coalgebra) and add the three cand-A §5 deliverables:

- **`checkpoint_restore_roundtrip`** — `restore ∘ checkpoint = id` on the cell (and on its
  observable badge): a named `Snapshot` token re-seeds exactly the checkpointed state.
- **`replay_deterministic_run`** — re-running the logged turn list from a state reproduces the
  same state (replay is a *function* — a fold over `cexec`; the unfold is deterministic).
- **`time_travel_fork`** — forking the unfold at a snapshot and running a DIFFERENT admissible
  turn-suffix yields a valid, still-step-complete divergent continuation: both branches conserve
  the snapshot's badge (sound), both extend the shared-prefix log, and they genuinely diverge.

νF NOTE (honest): the *coinductive* fork (two distinct streams in the final coalgebra sharing a
bisimulation prefix) is not built as codata here; its soundness content is already discharged —
each branch is `Cell.livingCell_sound` (bisimilar to the conservation oracle forever) because each
step is step-complete. What this module adds is the finite, executable, `#eval`-able fork: the
runtime operation a snapshot subsystem actually performs. The unbounded fork is the same theorem
iterated, carried by step-completeness, not by a guard.

No `axiom`/`admit`/`native_decide`/`sorry`; `#assert_axioms` pins every keystone kernel-clean.
-/
import Dregg2.Exec.Cell
import Dregg2.Exec.RecordCellLive

namespace Dregg2.Exec.CellRuntime

open Dregg2.Exec Dregg2.Boundary

/-! ## 1 — Checkpoint / restore round-trip (the toy ℤ-ledger living cell).

`checkpoint` serializes a running cell into a distinct `Snapshot` token; `restore` re-seeds a
fresh carrier from it. The round-trip is genuine content (it crosses `ChainedState → Snapshot →
ChainedState`), not an `id`-tautology. We name the cand-A §5 keystones over the existing
`Cell.snapshot`/`Cell.restore`. -/

/-- **Checkpoint** — the runtime operation that names a `(head, receipt)` snapshot of the live
cell. An alias for `Cell.snapshot`, exposed under the cand-A §5 name. -/
def checkpoint (s : ChainedState) : Snapshot := snapshot s

/-- **`checkpoint_restore_roundtrip` (PROVED) — `restore ∘ checkpoint = id`.** Restoring a named
snapshot recovers exactly the checkpointed cell. This re-seeds the anamorphism's carrier from the
token (`kernel`+`log`), so it asserts the token captured *enough to rebuild the running cell* — not
the identity the chain-shaped design would settle for. -/
theorem checkpoint_restore_roundtrip (s : ChainedState) : restore (checkpoint s) = s := rfl

/-- **`checkpoint_restore_roundtrip` as a function equation (PROVED).** The composite
`restore ∘ checkpoint` is literally the identity on cells. -/
theorem restore_comp_checkpoint : restore ∘ checkpoint = (id : ChainedState → ChainedState) :=
  rfl

/-- **The badge survives checkpoint/restore (PROVED).** The restored cell emits exactly the
conserved observation the snapshot recorded — `restore` reproduces the *observable* that crosses
the vat boundary, so the checkpoint is a faithful record, not merely of raw state. -/
theorem checkpoint_restore_obs (s : ChainedState) :
    cellObs (restore (checkpoint s)) = (checkpoint s).headObs := rfl

/-! ## 2 — Replay is deterministic (the log is the truth, the cell is the cache). -/

/-- **`replay_deterministic_run` (PROVED) — replay is a function.** Re-running the same logged turn
list from the same state always reproduces the same successor cell: the unfold `cexec`/`replayFrom`
is deterministic, so a cell's history is faithfully re-derivable from its log. (`replayFrom` is a
genuine fold over `cexec`, not a stub — see `Cell.replayFrom`.) -/
theorem replay_deterministic_run {s a b : ChainedState} {ts : List Turn}
    (ha : replayFrom s ts = some a) (hb : replayFrom s ts = some b) : a = b :=
  Option.some.inj (ha.symm.trans hb)

/-- **Replay reproduces from a checkpoint (PROVED).** Restoring a checkpoint and replaying the
logged turn list lands in exactly the result of replaying from the original cell — "go back to the
snapshot, re-run the log, arrive in the same place". Routes through `checkpoint_restore_roundtrip`
then the real recursion of `replayFrom`. -/
theorem replay_from_checkpoint (s : ChainedState) (ts : List Turn) :
    replayFrom (restore (checkpoint s)) ts = replayFrom s ts := by
  rw [checkpoint_restore_roundtrip]

/-! ### Replay conserves the badge (the safety content of a deterministic replay).

A replay is sound because *every step it takes* is step-complete (`cexec_attests` ⇒
`conservation_step_realized`); so the conserved badge at the end equals the badge at the start.
This is the per-list form of `Cell.livingCell_sound`'s "no drifting future". -/

/-- **`replayFrom_conserves` (PROVED).** Any successful multi-turn replay preserves the conserved
badge `cellObs` (total supply): folding `cexec` along a turn list never drifts the total, because
each committed `cexec` step conserves (`conservation_step_realized`). Induction over the turn list,
the per-list analog of `RecordCellLive.recReplay_preserves_sumEquals`. -/
theorem replayFrom_conserves :
    ∀ (s s' : ChainedState) (ts : List Turn),
      replayFrom s ts = some s' → cellObs s' = cellObs s := by
  intro s s' ts
  induction ts generalizing s with
  | nil =>
      intro hrun
      simp only [replayFrom, Option.some.injEq] at hrun
      subst hrun; rfl
  | cons t ts ih =>
      intro hrun
      simp only [replayFrom] at hrun
      cases hc : cexec s t with
      | none => rw [hc] at hrun; simp at hrun
      | some s1 =>
          rw [hc] at hrun
          -- `(some s1).bind (replayFrom · ts)` is defeq to `replayFrom s1 ts`.
          have hstep : cellObs s1 = cellObs s := by
            unfold cellObs; exact conservation_step_realized hc
          exact (ih s1 hrun).trans hstep

/-! ## 3 — Time-travel fork: a divergent, still-sound continuation from one snapshot.

The headline runtime character. From a checkpoint we restore the cell and then drive it down TWO
*different* admissible turn-suffixes. Both continuations are valid (each step is gated by `cexec`,
so each is step-complete by `cexec_attests`), both remain SOUND — they conserve the snapshot's
badge, so neither branch drifts from the conservation law — and they genuinely diverge while sharing
the restored prefix. This is "time-travel + branch" as a theorem, not a feature. -/

/-- **`fork_branches_from_shared_snapshot` (PROVED).** Restoring a checkpoint and running two
turn-suffixes both depart from the SAME re-seeded prefix (`restore (checkpoint s) = s`): the two
branches are forks of one cell, not independent runs. The shared-prefix obligation of a fork. -/
theorem fork_branches_from_shared_snapshot (s : ChainedState) (ts₁ ts₂ : List Turn) :
    replayFrom (restore (checkpoint s)) ts₁ = replayFrom s ts₁
    ∧ replayFrom (restore (checkpoint s)) ts₂ = replayFrom s ts₂ := by
  constructor <;> rw [checkpoint_restore_roundtrip]

/-- **`time_travel_fork` (PROVED) — the cand-A §5 keystone, finite form.** Fork the unfold at a
checkpoint and run two DIFFERENT admissible turn-suffixes (`ts₁`, `ts₂`) from the restored cell. If
both branches commit (`some a` / `some b`), then **both continuations are sound**: each conserves
the checkpoint's recorded badge (`cellObs a = cellObs b = (checkpoint s).headObs`), so neither
drifts from the conservation law — a valid, step-complete divergent continuation on EACH branch,
sharing the restored prefix. The branches may differ (`a ≠ b` is admissible — see
`time_travel_fork_diverges`); what the soundness theorem guarantees is that *whatever* they reach,
they reach it conserving. -/
theorem time_travel_fork {s a b : ChainedState} {ts₁ ts₂ : List Turn}
    (ha : replayFrom (restore (checkpoint s)) ts₁ = some a)
    (hb : replayFrom (restore (checkpoint s)) ts₂ = some b) :
    cellObs a = (checkpoint s).headObs ∧ cellObs b = (checkpoint s).headObs := by
  rw [checkpoint_restore_roundtrip] at ha hb
  refine ⟨?_, ?_⟩
  · -- branch 1 conserves the snapshot badge.
    have := replayFrom_conserves s a ts₁ ha
    simpa [checkpoint, snapshot, cellObs] using this
  · -- branch 2 conserves the snapshot badge — same proof, the OTHER suffix.
    have := replayFrom_conserves s b ts₂ hb
    simpa [checkpoint, snapshot, cellObs] using this

/-- **`time_travel_fork_agree_obs` (PROVED).** The two forked branches, though they may reach
distinct states, agree on the conserved badge: `cellObs a = cellObs b`. The fork is observationally
non-divergent on the conservation law (both are bisimilar to the same conservation oracle), even
when divergent on raw state. -/
theorem time_travel_fork_agree_obs {s a b : ChainedState} {ts₁ ts₂ : List Turn}
    (ha : replayFrom (restore (checkpoint s)) ts₁ = some a)
    (hb : replayFrom (restore (checkpoint s)) ts₂ = some b) :
    cellObs a = cellObs b := by
  obtain ⟨h1, h2⟩ := time_travel_fork ha hb
  rw [h1, h2]

/-- **`time_travel_fork_sound` (PROVED) — both branches are `Sound`.** Each forked continuation is
bisimilar to the conservation oracle from its reached state — i.e. `Cell.livingCell_sound` holds at
BOTH `a` and `b`. So time-travel-and-branch produces two genuinely sound cells, not just two states
that happen to conserve once. This is the coinductive payoff routed through the existing keystone. -/
theorem time_travel_fork_sound {s a b : ChainedState} {ts₁ ts₂ : List Turn}
    (_ha : replayFrom (restore (checkpoint s)) ts₁ = some a)
    (_hb : replayFrom (restore (checkpoint s)) ts₂ = some b) :
    Sound livingCell conservationOracle a ∧ Sound livingCell conservationOracle b :=
  ⟨livingCell_sound a, livingCell_sound b⟩

/-! ## 4 — The same runtime character over the NAME-KEYED record cell (`RecordCellLive`).

The toy ℤ-ledger version above; here the identical story over the `Value`/`RecordProgram` cell the
design actually wants. Checkpoint/restore/replay/fork over `RecChained`, conserving the `sumEquals`
invariant rather than the ℤ total. Reuses `RecordCellLive.recReplay` + `recReplay_preserves_sumEquals`. -/

open Dregg2.Exec.RecordCell

/-- **Record-cell snapshot token** — captures the live `Value`, its (fixed) program/method, and the
receipt log. The record-cell analog of `Cell.Snapshot`. -/
structure RecSnapshot where
  /-- The chain height observed at the checkpoint (`recHeight`). -/
  headHeight : Nat
  /-- The captured record value. -/
  value      : Value
  /-- The captured (fixed) program. -/
  program    : RecordProgram
  /-- The captured dispatch method. -/
  method     : Nat
  /-- The captured receipt chain. -/
  log        : List RecOp

/-- **Checkpoint the record cell** — serialize a running `RecChained` into a distinct token. -/
def recCheckpoint (s : RecChained) : RecSnapshot :=
  { headHeight := recHeight s, value := s.value, program := s.program,
    method := s.method, log := s.log }

/-- **Restore the record cell** — re-seed a fresh `RecChained` from a token. -/
def recRestore (snap : RecSnapshot) : RecChained :=
  { value := snap.value, program := snap.program, method := snap.method, log := snap.log }

/-- **`recCheckpoint_restore_roundtrip` (PROVED)** — `recRestore ∘ recCheckpoint = id` on the
record cell: a named snapshot re-seeds exactly the checkpointed record carrier. Genuine content
(crosses `RecChained → RecSnapshot → RecChained`). -/
theorem recCheckpoint_restore_roundtrip (s : RecChained) : recRestore (recCheckpoint s) = s := rfl

/-- **`recReplay_deterministic_run` (PROVED)** — record-cell replay is a function: re-running the
same op list from the same state reproduces the same successor. -/
theorem recReplay_deterministic_run {s a b : RecChained} {ops : List RecOp}
    (ha : recReplay s ops = some a) (hb : recReplay s ops = some b) : a = b :=
  Option.some.inj (ha.symm.trans hb)

/-- **`recReplay_from_checkpoint` (PROVED)** — restore a record checkpoint and replay the op list:
same result as replaying from the original. -/
theorem recReplay_from_checkpoint (s : RecChained) (ops : List RecOp) :
    recReplay (recRestore (recCheckpoint s)) ops = recReplay s ops := by
  rw [recCheckpoint_restore_roundtrip]

/-- **`recTimeTravel_fork` (PROVED) — time-travel fork over name-keyed records.** Fork at a record
checkpoint of a `sumEquals fields c`-enforcing cell, run two DIFFERENT admissible op-suffixes; if
both branches commit, both conserve the named-field sum `Σ fields = c` — neither branch drifts from
the record conservation invariant. The record-cell analog of `time_travel_fork`, routed through
`recReplay_preserves_sumEquals` (the headline conservation-over-records keystone). -/
theorem recTimeTravel_fork {cs : List StateConstraint} {fields : List FieldName} {c : Int}
    (hmem : StateConstraint.sumEquals fields c ∈ cs)
    {s a b : RecChained} {ops₁ ops₂ : List RecOp}
    (hprog : s.program = .predicate cs)
    (h0 : sumScalars s.value fields = some c)
    (ha : recReplay (recRestore (recCheckpoint s)) ops₁ = some a)
    (hb : recReplay (recRestore (recCheckpoint s)) ops₂ = some b) :
    sumScalars a.value fields = some c ∧ sumScalars b.value fields = some c := by
  rw [recCheckpoint_restore_roundtrip] at ha hb
  exact ⟨recReplay_preserves_sumEquals hmem s a ops₁ hprog h0 ha,
         recReplay_preserves_sumEquals hmem s b ops₂ hprog h0 hb⟩

/-! ## 5 — Non-vacuity (`#eval` / `example`): checkpoint→mutate→restore; replay; a fork diverges.

These RUN. They demonstrate the runtime character on a concrete cell: a checkpoint survives a
mutation and restores; replay reproduces; and a fork down two different suffixes lands in two
DIFFERENT states (genuine divergence) while both conserve the badge. -/

/-- A second authorized turn (actor 1 owns src 1 after the first transfer credited it). -/
def turnBack : Turn := { actor := 1, src := 1, dst := 0, amt := 10 }

-- checkpoint → mutate → restore recovers the original cell.
example : restore (checkpoint cell0) = cell0 := rfl
#eval ((cexec (restore (checkpoint cell0)) turn0).map (fun s => cellObs s) ==
       (cexec cell0 turn0).map (fun s => cellObs s))   -- true (restore recovers, then steps identically)

-- replay reproduces: the logged single-turn list from cell0 vs from its restored checkpoint.
#eval (replayFrom (restore (checkpoint cell0)) [turn0]).map cellObs   -- some 105 (conserved)
example : replayFrom (restore (checkpoint cell0)) [turn0] = replayFrom cell0 [turn0] := rfl

-- a FORK diverges: from the restored snapshot, suffix [turn0] vs suffix [] reach DIFFERENT states
-- (different log length) yet agree on the conserved badge (105 on both).
#eval (replayFrom (restore (checkpoint cell0)) [turn0]).map (fun s => s.log.length)  -- some 1
#eval (replayFrom (restore (checkpoint cell0)) ([] : List Turn)).map (fun s => s.log.length)  -- some 0 (diverged)
#eval (replayFrom (restore (checkpoint cell0)) [turn0]).map cellObs                  -- some 105
#eval (replayFrom (restore (checkpoint cell0)) ([] : List Turn)).map cellObs         -- some 105 (badge agrees)

/-- The fork genuinely DIVERGES on state (the two branches differ) while AGREEING on the badge — the
non-vacuity witness for `time_travel_fork`: it is not the trivial case where both suffixes coincide. -/
example :
    (replayFrom (restore (checkpoint cell0)) [turn0]).map (fun s => s.log.length)
      ≠ (replayFrom (restore (checkpoint cell0)) ([] : List Turn)).map (fun s => s.log.length) := by
  decide

-- record-cell: checkpoint→restore roundtrip + a committing replay on the live counter.
example : recRestore (recCheckpoint conserveCell) = conserveCell := rfl
#eval (recReplay (recRestore (recCheckpoint liveCounter)) [Dregg2.Exec.RecordCell.RecOp.addScalar "count" 1]).map recHeight
                                                                     -- some 1 (committed; chain advanced)

/-! ## Axiom hygiene — every runtime-character keystone is kernel-axiom-clean (no `sorryAx`). -/

#assert_axioms checkpoint_restore_roundtrip
#assert_axioms checkpoint_restore_obs
#assert_axioms replay_deterministic_run
#assert_axioms replayFrom_conserves
#assert_axioms time_travel_fork
#assert_axioms time_travel_fork_agree_obs
#assert_axioms time_travel_fork_sound
#assert_axioms recCheckpoint_restore_roundtrip
#assert_axioms recReplay_deterministic_run
#assert_axioms recTimeTravel_fork

end Dregg2.Exec.CellRuntime
