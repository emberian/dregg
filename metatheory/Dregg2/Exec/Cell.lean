/-
# Dregg2.Exec.Cell — the LIVING coinductive cell (the Mg-Vision keystone).

`REORIENT.md §5`. This is the unification the metatheory was missing: a cell that is
*simultaneously* **executable** (`cexec`, real `Finset` arithmetic), **step-complete**
(`cexec_attests` proves all four `StepInv` conjuncts on the running machine), and
**bisimulation-sound** (it behaves like its golden-oracle reference *forever*, coinductively).

It wires the executable spine (`Exec/StepComplete.lean`) into the coinductive frame
(`Boundary.lean`'s `TurnCoalg`/`Sound`/`IsBisim`), and **recovers `sound_of_step_complete`**
— which was earlier refuted as false-as-stated (free `Spec`, `Spec=Empty`). Per
`pdfs/STUDY-lean4-coinduction.md §3.2`, the well-posed version surfaces the **golden-oracle
bridge** (`oracle`/`h_obs`/`h_step`) and is then provable with the *relational* greatest-fixpoint
encoding — no QPF, no codata datatype, `Later = id` (productivity is carried by step-completeness,
not the guard).

The state here is still the toy `KernelState` (a 2-account ℤ ledger inside `ChainedState`); growing
it to the `Value`/`CellProgram` Preserves cell (`Exec/Value.lean`, `Exec/Program.lean`) is a later
state-refinement that does **not** change this coalgebra/bisimulation story — the honest l4v
sequencing is: get the living cell + soundness right on the proved core first, then grow the state.
-/
import Dregg2.Exec.StepComplete
import Dregg2.Boundary

namespace Dregg2.Exec

open Dregg2.Boundary

/-! ## Step 1 — the living cell as a coalgebra (Moore/DFA shape: observe-then-transition). -/

/-- The cell's externally-visible observation (the "badge") — its conserved total supply. This
is the `Obs` the bisimulation tracks: what crosses a vat boundary. -/
def cellObs (s : ChainedState) : ℤ := total s.kernel

/-- The total successor: run `cexec`; on an **inadmissible** turn the live cell *stays put* (a
Moore machine self-loops on rejected input — fail-closed). Totality ⇒ a clean `TurnCoalg`. -/
def cellNext (s : ChainedState) (t : Turn) : ChainedState := (cexec s t).getD s

/-- **The living cell** as a `Boundary.TurnCoalg`: carrier = `ChainedState` (kernel + receipt
chain), observation = the conserved badge, transition = `cexec` (stay-put on rejection). The
structure map `step : X → Obs × (Turn → X)` **is** the cell's behaviour over unbounded time. -/
def livingCell : TurnCoalg ℤ Turn where
  Carrier := ChainedState
  step s := (cellObs s, cellNext s)

/-! ## Step 2 — the golden-oracle spec (the abstract conservation reference) + the bridge. -/

/-- The reference coalgebra: carrier = the conserved quantity `ℤ`; it observes itself and **never
changes** (an ordinary turn preserves the total). The living cell is SOUND iff its observable
behaviour is bisimilar to this — i.e. it never drifts from conservation over unbounded time (the
"no drifting future" of `decisions.md §2`). -/
def conservationOracle : TurnCoalg ℤ Turn where
  Carrier := ℤ
  step v := (v, fun _ => v)

/-- The decode/replay map into the spec: a cell decodes to its conserved observation. -/
def cellOracle (s : ChainedState) : ℤ := cellObs s

/-! ## Step 3 — the recovered keystone: bisimulation-from-oracle (STUDY-lean4-coinduction §3.2). -/

/-- **`bisim_of_oracle` (PROVED) — the well-posed `sound_of_step_complete`.** If a decode map
`oracle` commutes with observation (`h_obs`) and transition (`h_step`), then `Impl` is **sound**
(bisimilar) relative to `Spec` from every state. The earlier free-`Spec` keystone was refuted
(`Spec=Empty`); surfacing the oracle bridge makes the *genuine* bisimulation provable — relational
greatest-fixpoint, `Later = id`, no missing coinduction machinery. Witness relation: "`y` is the
oracle image of `x`." -/
theorem bisim_of_oracle {Obs : Type} (Impl Spec : TurnCoalg Obs Turn)
    (oracle : Impl.Carrier → Spec.Carrier)
    (h_obs  : ∀ x, Impl.obs x = Spec.obs (oracle x))
    (h_step : ∀ x t, oracle (Impl.next x t) = Spec.next (oracle x) t)
    (x : Impl.Carrier) : Sound Impl Spec x := by
  refine ⟨fun a b => b = oracle a, oracle x, ⟨?_, ?_⟩, rfl⟩
  · -- obs_eq: related states emit equal observations NOW.
    rintro a b rfl; exact h_obs a
  · -- step_rel: successors related LATER (the ▶ guard; `Later = id`).
    rintro a b rfl t; exact (h_step a t).symm

/-! ## The living cell IS sound — bisimilar to the conservation oracle, forever (PROVED). -/

/-- The oracle commutes with observation — definitional. -/
theorem cell_h_obs (s : ChainedState) :
    livingCell.obs s = conservationOracle.obs (cellOracle s) := rfl

/-- The oracle commutes with transition — **this is exactly where step-completeness lands**: the
conserved observation is invariant under `cellNext` because `cexec` conserves (the Conservation
conjunct of `cexec_attests`, as `conservation_step_realized`), and the stay-put self-loop trivially
conserves. PROVED. -/
theorem cell_h_step (s : ChainedState) (t : Turn) :
    cellOracle (livingCell.next s t) = conservationOracle.next (cellOracle s) t := by
  show cellObs (cellNext s t) = cellObs s
  unfold cellNext cellObs
  cases h : cexec s t with
  | some s' => simp only [Option.getD_some]; exact conservation_step_realized h
  | none    => simp only [Option.getD_none]

/-- **`livingCell_sound` (PROVED) — the Mg-Vision keystone, realized.** The executable living cell
is **bisimilar to its conservation oracle from every state**: its observable behaviour never drifts
from the conservation law, over unbounded (coinductive) time. Step-completeness — the Conservation
conjunct of `cexec_attests`, routed through `cell_h_step` — is *exactly* what makes the bisimulation
hold ("no drifting future"). This is `sound_of_step_complete` recovered honestly for a concrete,
executable, step-complete cell. -/
theorem livingCell_sound (s : ChainedState) : Sound livingCell conservationOracle s :=
  bisim_of_oracle livingCell conservationOracle cellOracle cell_h_obs cell_h_step s

/-! ## Step 4 — runtime character as THEOREMS (checkpoint / restore / replay) — cand-A §5.

This section delivers checkpoint/restore/replay as **real theorems about a genuine snapshot
mechanism**, not `id`-tautologies. A `Snapshot` is a *distinct* token type (`headObs` + `log`
+ `kernel`) into which a running cell is serialized; `restore` re-seeds a fresh `ChainedState`
from a token. The round-trip and replay theorems then quantify over the actual `cexec`/`cellObs`
structure, so they say something the type system does not already force.

(Historical note: an earlier version made `checkpoint := id` and proved `restore (checkpoint s) = s`
by `rfl` and `checkpoint_replay := h` — both `id`-identities advertised as the time-travel payoff.
Those were vacuous; the snapshot-token mechanism below replaces them with load-bearing statements.) -/

/-- **A checkpoint token** — the serialized snapshot of a running cell at a point in its unfold.
Distinct type from `ChainedState`: it records the externally-visible badge (`headObs`) alongside
the data needed to re-seed the anamorphism (the `kernel` and the receipt `log`). The `headObs`
field is what a snapshot subsystem would persist/digest; carrying it lets `restore` be checked to
reproduce the *observable*, not merely the raw state. -/
structure Snapshot where
  /-- The conserved badge observed at the moment of the checkpoint (`cellObs s`). -/
  headObs : ℤ
  /-- The kernel state captured (live accounts, balances, caps). -/
  kernel  : KernelState
  /-- The receipt chain captured. -/
  log     : List Turn

/-- **Checkpoint = serialize the running cell into a snapshot token.** Records the head badge and
the data to resume the unfold. This is a *real* snapshot into a distinct type — not the identity. -/
def snapshot (s : ChainedState) : Snapshot :=
  { headObs := cellObs s, kernel := s.kernel, log := s.log }

/-- **Restore = re-seed a fresh cell from a snapshot token** — rebuild the anamorphism's carrier
from the captured `kernel`/`log`. "Going back" is re-seeding, not undoing. -/
def restore (snap : Snapshot) : ChainedState :=
  { kernel := snap.kernel, log := snap.log }

/-- **Round-trip (PROVED) — restore∘checkpoint reproduces the cell.** Serializing a running cell to
a snapshot token and re-seeding from it yields the *same* `ChainedState`. This is genuine content
(it crosses `ChainedState → Snapshot → ChainedState`, asserting the token captured enough to rebuild
the carrier); it is NOT the `id`-tautology the old `checkpoint := id` version stated. -/
theorem restore_snapshot (s : ChainedState) : restore (snapshot s) = s := rfl

/-- **The badge survives the round-trip (PROVED).** The restored cell emits exactly the badge the
snapshot recorded — `restore` reproduces the *observable*, so the snapshot token is a faithful
record of what crosses the vat boundary, not merely of raw state. -/
theorem restore_snapshot_obs (s : ChainedState) :
    cellObs (restore (snapshot s)) = (snapshot s).headObs := rfl

/-- **Replay is deterministic** — re-running a turn from a state always reproduces the same
successor (the unfold is a function), so a cell's history is faithfully re-derivable from the log
("the log is the truth, the DB is the cache"). PROVED. -/
theorem replay_deterministic {s : ChainedState} {t : Turn} {a b : ChainedState}
    (ha : cexec s t = some a) (hb : cexec s t = some b) : a = b :=
  Option.some.inj (ha.symm.trans hb)

/-- **Multi-turn replay from a cell** — fold `cexec` along a list of turns, fail-closed (any
inadmissible turn aborts the whole replay). This is the actual re-derivation engine: "replay the
committed sequence from here". -/
def replayFrom (s : ChainedState) : List Turn → Option ChainedState
  | []      => some s
  | t :: ts => (cexec s t).bind (fun s' => replayFrom s' ts)

/-- **Checkpoint/replay round-trip over a whole turn sequence (PROVED).** Replaying a sequence of
turns from a *restored snapshot* reproduces exactly the result of replaying the same sequence from
the original cell. The proof routes through `restore_snapshot` (`restore (snapshot s) = s`) and then
the genuine recursion of `replayFrom` over `cexec` — this is "checkpoint/restore/replay are theorems"
made literal: time-travel back to a snapshot and re-run the log lands you in the same place. -/
theorem replay_from_snapshot (s : ChainedState) (ts : List Turn) :
    replayFrom (restore (snapshot s)) ts = replayFrom s ts := by
  rw [restore_snapshot]

/-- **Single-turn replay from a snapshot (PROVED).** Replaying one committed turn after restoring a
snapshot reproduces the unique successor of that turn from the original cell. A corollary of
`restore_snapshot`, but stated about the real `cexec` step (not the `id`-identity of the old
`checkpoint_replay`). -/
theorem replay_one_from_snapshot {s s' : ChainedState} {t : Turn} (h : cexec s t = some s') :
    cexec (restore (snapshot s)) t = some s' := by
  rw [restore_snapshot]; exact h

/-- **Time-travel: the badge is conserved across a checkpoint (PROVED).** Restoring to a snapshot
and re-running a turn preserves the conserved observation. Now genuinely about `restore`/`snapshot`
+ conservation (not `checkpoint := id`): the restored cell emits the snapshot's recorded badge, and
the committed turn from it conserves that badge. -/
theorem snapshot_conserves {s s' : ChainedState} {t : Turn}
    (h : cexec (restore (snapshot s)) t = some s') : cellObs s' = (snapshot s).headObs := by
  rw [restore_snapshot] at h
  exact conservation_step_realized h

/-! ## It runs (`#eval`) — a real living cell taking a turn. -/

/-- A chained cell over `Kernel.s0` (cells 0,1 holding 100+5), empty log. -/
def cell0 : ChainedState := { kernel := s0, log := [] }

/-- The authorized transfer turn (actor 0 owns src 0). -/
def turn0 : Turn := t1

#eval cellObs cell0                                   -- 105 (the conserved badge)
#eval (cexec cell0 turn0).map (fun s => cellObs s)    -- some 105 (conserved after the turn)
#eval (cexec cell0 turn0).map (fun s => s.log.length) -- some 1   (the chain advanced — ObsAdvance)
#eval cellObs (cellNext cell0 tBad)                   -- 105 (inadmissible turn ⇒ stay-put, badge unchanged)

end Dregg2.Exec
