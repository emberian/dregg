/-
# Dregg2.Proof.LTS — the operational small-step LTS + forward-simulation square.

**The long pole (Phase iii).** `docs/rebuild/PHASE-CONSTRUCTION.md §3` names the operational
small-step LTS / full forward-simulation diagram as THE gating research item — the single
longest pole, "research, not engineering", gating the coinductive `Boundary` keystone. Today
`Spec/ExecRefinement.lean §4` and `Proof/Refine.lean` leave it explicitly OPEN: they prove the
STATIC PROJECTIONS of the `Exec ⊑ Spec` square (conservation + authority are PRESERVED by a
step), but the bottom edge is the *identity-on-projections* abstraction `absOf`, NOT a genuine
abstract TRANSITION relation `AbsStep`. The residual obligation, verbatim from §4:

  > define `AbsStep : AbstractState → AbstractState → Prop` … and prove
  > `exec k turn = some k' → AbsStep (absOf k) (absOf k')` (forward simulation: every
  > executable step is an abstract step).

This module ATTEMPTS exactly that, on the cleanest concrete target: the content-addressed
record kernel `Exec.RecordKernel.recKExec` (whose `recKExec_conserves` / `recKExec_authorized` /
`recKExec_frame` / `recCexec_attests` are PROVED). The carrier is
`Spec.ExecRefinement.AbstractState = (balanceTotal : ℤ, authGraph : Graph Label ExecRights)` —
the SAME abstract state §3 already uses — and `recAbsOf : RecordKernelState → AbstractState` is
the record-cell analog of `Spec.absOf`.

## What this file establishes (the honest outcome)

**CLOSED — the forward-simulation square for the single-cell record kernel (`recAbsStep_forward`,
axiom-clean).** Every committed record-cell turn IS matched by a genuine abstract small-step
`recAbsStep`. The abstract step is a real transition relation (not the identity, not a vacuous
`True`): it is *indexed by the grounding turn* and bundles the THREE operational facts as one
relation —

  (C) conservation:    `a'.balanceTotal = a.balanceTotal`     (balance-domain `Σδ = 0`)
  (A) authority frame: `a'.authGraph    = a.authGraph`         (the transfer mutates NO edge)
  (G) grounding:       the turn is grounded in `a.authGraph`   (ownership ∨ `Graph.has`)

and (G) is the LOAD-BEARING content that makes `recAbsStep` an *authorized* transition rather
than a bare conservation identity: it consumes `exec_authz_grounds_in_graph`, so the abstract
step witnesses that the move was justified by the authority graph's reachability. The forward
simulation then assembles `recKExec_conserves` (C) + `recKExec_frame` (A) +
`exec_authz_grounds_in_graph` (G) into one `recAbsStep`, and lifts to whole runs
(`recAbsStep_run_forward`). This closes a real fragment of the long pole.

## The SHARP OBSTRUCTION to the §4 sketch's general form (documented, NOT faked)

§4 (and `Spec.Authority`'s headline OPEN) sketches the abstract step as additionally *firing an
authorized `Spec.Authority.AuthStep` / `GenAct` / `RestrictAct` on the graph*. For a **balance
transfer** that is the WRONG abstract semantics, and the gap is genuine, not a missing proof:

  A balance transfer mutates NO authority edge (`recKExec_frame`: `G' = G`). But EVERY
  `AuthStep` constructor (`gen`/`restrict` ⊇ `Introduce`/`Mint`/`Endow`/`Amplify`/`Attenuate`/
  `Revoke`) is, by its `result` field, an `addEdge`/`removeEdge` — a *genuine* graph mutation
  predicated on a held cap. There is **no no-op `AuthStep`**: `AuthStep consents G G` is NOT
  derivable from a transfer, because no constructor yields `G' = G` for an arbitrary `G`
  (`addEdge`/`removeEdge` of a held cap is not the identity unless the graph already had/lacked
  exactly that edge — a coincidence, not a law). We make this precise as
  `transfer_fires_no_authStep`: the transfer's abstract effect on the graph is the IDENTITY, which
  is the EMPTY `AuthStep` family. So the faithful abstract step for a transfer is exactly
  (C)∧(A)∧(G) with the authority graph held FIXED — NOT an `AuthStep` firing. The §4 sketch
  conflated two distinct turn KINDS: a *balance turn* (conservation move, authority FIXED, this
  file) versus an *authority turn* (a delegation/revocation that fires an `AuthStep` and is
  conservation-trivial). The record kernel `recKExec` only emits balance turns; its forward
  simulation is the (C)∧(A)∧(G) square, CLOSED here. The `AuthStep`-firing half of the LTS awaits
  an *authority-mutating executable kernel* (a `recKDelegate`/`recKRevoke` transition that edits
  `caps`), which does not yet exist in `Exec/*` — that is the precise, named residue (see §4 OPEN
  at the foot).

So: the operational forward-simulation square is CLOSED for the (only) turn kind the record
kernel emits; the remaining open is not a proof gap in this square but a MISSING EXECUTABLE
TRANSITION (the authority-mutating kernel) whose abstract image would be the `AuthStep` half.

## Discipline (REORIENT §6)
No `axiom`/`admit`/`native_decide`/`sorry`. `#assert_axioms` on every closed keystone. The OPEN
is PROSE (a named missing executable transition), not a `sorry` declaration — the file is clean.
Imports ONLY existing built modules; modifies NOTHING. Read-only consumer of `RecordKernel`,
`ExecRefinement`, `Authority`.
-/
import Dregg2.Exec.RecordKernel
import Dregg2.Exec.AuthTurn
import Dregg2.Spec.ExecRefinement
import Dregg2.Spec.Authority

namespace Dregg2.Proof.LTS

open Dregg2.Exec
open Dregg2.Spec
open Dregg2.Authority (Caps Label)
open scoped BigOperators

/-! ## §1 — The abstraction function for the record kernel.

`Spec.AbstractState` is the carrier the first square already uses: the conserved balance-domain
total (`ℤ`) plus the reconstructed authority `Graph`. We give the RECORD kernel its abstraction
function `recAbsOf` — the record-cell analog of `Spec.absOf` (which abstracts the scalar kernel).
It reads the `balance`-FIELD measure `recTotal` and reconstructs the SAME authority graph
`execGraph` from the cap table (authority is orthogonal to the state representation, so the same
`execGraph` serves both kernels). -/

/-- The abstract state a record-kernel state denotes: its `recTotal` (the `balance`-field
conserved measure) and its `execGraph` (reconstructed authority graph). The record-cell
abstraction function — the `recKExec` analog of `Spec.absOf`. -/
def recAbsOf (k : RecordKernelState) : AbstractState :=
  { balanceTotal := recTotal k
    authGraph    := execGraph k.caps }

/-! ## §2 — `recAbsStep` — the abstract small-step transition relation (a REAL LTS edge).

This is the missing `AbsStep` of `ExecRefinement §4`, specialized to the record kernel's turn
kind (a balance transfer). It is NOT the identity and NOT `True`: it is a transition relation
*indexed by the grounding turn* `t`, bundling the three operational facts a committed balance
turn establishes. Crucially the grounding conjunct (G) consumes the authority graph as load-
bearing data — the step is `a ⟶[t] a'` only when `t` is grounded in `a`'s authority graph, so
this is an AUTHORIZED conservation transition, the genuine abstract dynamics of a balance move. -/

/-- **`recAbsStep t a a'`** — the abstract small-step LTS edge for a balance turn `t`:

  * (C) conservation — `a'.balanceTotal = a.balanceTotal` (the balance-domain `Σδ = 0`);
  * (A) authority frame — `a'.authGraph = a.authGraph` (a balance turn mutates NO edge);
  * (G) grounding — `t` is authorized w.r.t. `a.authGraph`: either ownership
    (`t.actor = t.src`) or the actor `Graph.has` the source on `a.authGraph`.

(G) is what makes this an abstract *step* of the `Spec.Authority` dynamics rather than a bare
conservation identity: the move is justified by the authority graph's reachability (Granovetter:
"you can move what you can reach"). The turn `t` is an explicit index so the relation records
WHICH authorized action drove the step — exactly the operational content §4 asks for. -/
def recAbsStep (t : Turn) (a a' : AbstractState) : Prop :=
  -- (C) conservation: the balance-domain total is preserved.
  a'.balanceTotal = a.balanceTotal ∧
  -- (A) authority frame: a balance turn leaves the authority graph fixed.
  a'.authGraph = a.authGraph ∧
  -- (G) grounding: the turn is authorized in the authority graph (ownership ∨ reachability).
  (t.actor = t.src ∨ (a.authGraph).has t.actor t.src)

/-- **`AbsStep a a'`** — the abstract LTS edge with the grounding turn EXISTENTIALLY closed (the
`Spec.AbstractState`-level transition relation §4 names, with no turn index). `a ⟶ a'` iff some
authorized balance turn `t` realizes the `recAbsStep`. This is the relation the forward-simulation
square commutes against. -/
def AbsStep (a a' : AbstractState) : Prop :=
  ∃ t : Turn, recAbsStep t a a'

/-! ## §3 — THE FORWARD-SIMULATION SQUARE (CLOSED for the record kernel).

The l4v `Design ⊑ Abstract` operational diagram, for the content-addressed record cell:

```
              recAbsOf
   k  ──────────────────▶  recAbsOf k
   │                          │
   │ recKExec k turn = k'     │ recAbsStep turn   (the abstract LTS edge)
   ▼                          ▼
   k' ─────────────────▶  recAbsOf k'
              recAbsOf
```

Every committed concrete step `recKExec k turn = some k'` is matched by a genuine abstract step
`recAbsStep turn (recAbsOf k) (recAbsOf k')`. This is the forward simulation, not the static
projection-preservation §3 proves — the bottom edge is now a real `AbsStep`. -/

/-- **KEYSTONE — `recAbsStep_forward` (PROVED-clean).** The forward-simulation square for the
single-cell record kernel: every committed record-cell turn is matched by the abstract LTS edge
`recAbsStep`. Assembles the three already-proved kernel facts into ONE abstract transition:

  * (C) ← `recKExec_conserves`  (the `balance`-field total is preserved);
  * (A) ← `recKExec_frame`      (the transfer preserves `caps`, so `execGraph` is unchanged);
  * (G) ← `exec_authz_grounds_in_graph ∘ recKExec_authorized`  (the committed turn is grounded
        in the reconstructed authority graph — ownership or `Graph.has`).

This is the operational refinement the long pole asks for: `recKExec k turn = some k' →
recAbsStep turn (recAbsOf k) (recAbsOf k')`. CLOSED. -/
theorem recAbsStep_forward (k k' : RecordKernelState) (turn : Turn)
    (h : recKExec k turn = some k') :
    recAbsStep turn (recAbsOf k) (recAbsOf k') := by
  refine ⟨?_, ?_, ?_⟩
  · -- (C) conservation: `recTotal k' = recTotal k`.
    simp only [recAbsOf]
    exact recKExec_conserves k k' turn h
  · -- (A) authority frame: `execGraph k'.caps = execGraph k.caps` (caps preserved).
    simp only [recAbsOf]
    rw [(recKExec_frame k k' turn h).2]
  · -- (G) grounding: the committed turn is grounded in `execGraph k.caps`.
    simp only [recAbsOf]
    exact exec_authz_grounds_in_graph k.caps turn (recKExec_authorized k k' turn h)

/-- **`recAbsStep_forward_exists` (PROVED-clean).** The turn-index-closed form: every committed
record step is matched by an `AbsStep` (the `Spec.AbstractState`-level transition §4 names, with
the grounding turn existentially witnessed). This is the bottom edge of the square as a bare
`AbstractState → AbstractState → Prop` relation. -/
theorem recAbsStep_forward_exists (k k' : RecordKernelState) (turn : Turn)
    (h : recKExec k turn = some k') :
    AbsStep (recAbsOf k) (recAbsOf k') :=
  ⟨turn, recAbsStep_forward k k' turn h⟩

/-- **`recAbsStep_refines` (PROVED-clean).** The square in `Refines`-shape, mirroring §3's
`exec_step_refines` but with the bottom edge a GENUINE abstract step: for the canonical
abstraction `a := recAbsOf k`, there is an abstract successor `a' := recAbsOf k'` such that the
abstract LTS steps `recAbsStep turn a a'`. So `exec_step_refines`'s "preserves the two
projections" is STRENGTHENED here to "commutes with a real abstract transition" — for the record
kernel's turn kind, full forward simulation. -/
theorem recAbsStep_refines (k k' : RecordKernelState) (turn : Turn)
    (h : recKExec k turn = some k') :
    ∃ a', a' = recAbsOf k' ∧ recAbsStep turn (recAbsOf k) a' :=
  ⟨recAbsOf k', rfl, recAbsStep_forward k k' turn h⟩

/-! ## §3.1 — Lifting the square to whole runs (the LTS over the userspace-program layer).

The forward simulation is stable under iteration: an entire `recKExec`-run is matched by a chain
of abstract `AbsStep`s. We use the reflexive-transitive `AbsStep`-closure as the run-level
abstract LTS and show every concrete `Run recKernelSystem` maps onto it. -/

/-- The reflexive-transitive closure of `AbsStep` — the run-level abstract LTS (a chain of
authorized balance steps). Head-recursive, mirroring `Execution.Run` (one step PREPENDED to the
tail run), so the concrete-run induction maps onto it directly. -/
inductive AbsRun : AbstractState → AbstractState → Prop where
  | refl (a : AbstractState) : AbsRun a a
  | step {a a' a'' : AbstractState} (s : AbsStep a a') (rest : AbsRun a' a'') : AbsRun a a''

/-- **`recAbsStep_run_forward` (PROVED-clean).** The whole-run forward simulation: every concrete
record-kernel `Run` is matched by an `AbsRun` of abstract steps between the abstractions of its
endpoints. The operational refinement square is stable under iteration — the abstract LTS
simulates the concrete one over unbounded executions (the shape the coinductive `Boundary`
keystone consumes). PROVED by induction on the concrete run. -/
theorem recAbsStep_run_forward {k k' : RecordKernelState}
    (hrun : Execution.Run recKernelSystem k k') :
    AbsRun (recAbsOf k) (recAbsOf k') := by
  -- Induct on the run via its recursor, with the motive reading the endpoints through `recAbsOf`.
  refine Execution.Run.rec
    (motive := fun a b _ => AbsRun (recAbsOf a) (recAbsOf b)) ?_ ?_ hrun
  · intro s; exact AbsRun.refl _
  · intro s t u hstep _ ih
    obtain ⟨turn, hturn⟩ := hstep
    exact AbsRun.step (recAbsStep_forward_exists _ _ turn hturn) ih

/-! ## §4 — The grounding conjunct (G) is LOAD-BEARING — `recAbsStep` is not vacuous.

A guard against the failure mode the rails forbid: an `AbsStep` that is secretly `True` (or the
identity) is a fake close. We pin that `recAbsStep` genuinely CONSTRAINS its arguments — it is
refutable, so it carries content. -/

/-- **`recAbsStep_grounded` (PROVED).** The grounding conjunct can be PROJECTED OUT of any
abstract step: `recAbsStep t a a'` entails `t` is authorized in `a`'s authority graph. This is
the load-bearing fact distinguishing `recAbsStep` from a bare conservation identity — the step
remembers it was authorized. (Used to refute vacuity below.) -/
theorem recAbsStep_grounded {t : Turn} {a a' : AbstractState}
    (h : recAbsStep t a a') :
    t.actor = t.src ∨ (a.authGraph).has t.actor t.src :=
  h.2.2

/-- **`recAbsStep_not_vacuous` (PROVED).** `recAbsStep` is NOT the always-true relation: there
is a turn, and abstract states, for which it FAILS. Concretely, a turn whose actor ≠ src, over an
EMPTY authority graph (no edges), is NOT grounded, so no `recAbsStep` holds for it regardless of
the conservation/frame conjuncts. This refutes "the abstract step is vacuously `True`" — the
grounding conjunct (G) does real work. -/
theorem recAbsStep_not_vacuous :
    ∃ (t : Turn) (a a' : AbstractState), ¬ recAbsStep t a a' := by
  -- actor 0, src 1 (actor ≠ src), over the empty authority graph.
  refine ⟨{ actor := 0, src := 1, dst := 2, amt := 0 },
          { balanceTotal := 0, authGraph := fun _ _ => False },
          { balanceTotal := 0, authGraph := fun _ _ => False }, ?_⟩
  rintro ⟨_, _, hg⟩
  rcases hg with hown | hreach
  · exact absurd hown (by decide)
  · obtain ⟨_, hedge⟩ := hreach
    exact hedge

/-! ## §5 — The SHARP OBSTRUCTION: a balance transfer fires NO `AuthStep`.

The §4 sketch (and `Spec.Authority`'s headline OPEN) imagines the abstract step ALSO firing an
authorized `Spec.Authority.AuthStep`/`GenAct`/`RestrictAct`. For a balance transfer that is the
wrong shape, and we make the gap PRECISE rather than papering over it: the transfer's effect on
the authority graph is the IDENTITY (`recKExec_frame`), and the identity is NOT in the `AuthStep`
family, because every `AuthStep` constructor genuinely mutates the graph via `addEdge`/`removeEdge`.

We exhibit this as a concrete refutation: on a SPECIFIC graph there is NO `AuthStep G G`. That is
the sharp obstruction — not "the proof is hard" but "the abstract object the sketch names does not
EXIST for this turn kind". The honest consequence: the record kernel's faithful abstract step is
exactly the (C)∧(A)∧(G) `recAbsStep` above (authority FIXED), CLOSED; the `AuthStep`-firing half
of the LTS belongs to a DIFFERENT, not-yet-built executable transition (an authority-mutating
kernel), and is named as the residue in the OPEN below. -/

/-- A trivial-rights graph carrier for stating the obstruction concretely (`Unit` rights, the same
`ExecRights` the reconstructed graph uses). -/
abbrev ObsRights := ExecRights

/-- **`transfer_fires_no_authStep` (PROVED) — the obstruction, concretely.** There is an authority
graph `G` (the empty graph) on which NO `AuthStep` `G ⟶ G` exists: an `AuthStep` to the SAME graph
is underivable, because every generative constructor's `result` is `G' = addEdge …` (which, on the
empty graph, makes `G'` hold an edge `G` lacks) and every restrictive constructor first requires a
HELD cap `G holder cap` (impossible on the empty graph). So a balance transfer — whose graph effect
is `G' = G` (`recKExec_frame`) — cannot be an `AuthStep` firing. This is the precise sense in which
the §4 sketch's "fire an `AuthStep`" is the WRONG abstract semantics for a balance turn: the object
does not exist. -/
theorem transfer_fires_no_authStep
    (consents : Label → Prop) :
    ¬ Spec.AuthStep (CellId := Label) (Rights := ObsRights) consents
        (fun _ _ => False) (fun _ _ => False) := by
  -- An `addEdge` post-graph always HOLDS the freshly-added edge (the right disjunct) — so it
  -- cannot equal the empty graph. We package that as a reusable contradiction.
  have hadd : ∀ (G : Spec.Graph Label ObsRights) (h : Label) (c : Cap Label ObsRights),
      (fun _ _ => False) = Spec.addEdge G h c → False := by
    intro G h c hr
    -- evaluate both sides at the added edge `(h, c)`: LHS = False, RHS holds (right disjunct).
    have : (Spec.addEdge G h c) h c := Or.inr ⟨rfl, rfl⟩
    rw [← hr] at this; exact this
  intro hstep
  cases hstep with
  | gen hgen =>
      -- Every generative act adds an edge: its `result` is `G' = addEdge …`; but `G' = False`.
      cases hgen with
      | introduce h => exact hadd _ _ _ h.result
      | amplify h => exact hadd _ _ _ h.result
      | mint h => exact hadd _ _ _ h.result
      | endow h => exact hadd _ _ _ h.result
  | restrict hres =>
      -- Every restrictive act requires a HELD cap on the (empty) pre-graph — impossible.
      cases hres with
      | attenuate h => exact h.holds_cap
      | revoke h => exact h.holds_cap

/-- **`balance_turn_graph_is_fixed` (PROVED)** — restating the frame fact at the LTS level: the
abstract graph component is FIXED across a committed record step (the (A) conjunct of
`recAbsStep`). Together with `transfer_fires_no_authStep`, this is the full obstruction: the
graph does not move (so an `AuthStep` would have to be a no-op), AND no no-op `AuthStep` exists.
Hence the faithful abstract step is `recAbsStep` (authority fixed), NOT an `AuthStep` firing. -/
theorem balance_turn_graph_is_fixed (k k' : RecordKernelState) (turn : Turn)
    (h : recKExec k turn = some k') :
    (recAbsOf k').authGraph = (recAbsOf k).authGraph := by
  simp only [recAbsOf]
  rw [(recKExec_frame k k' turn h).2]

/-! ## §6 — Axiom-hygiene tripwires (the CLOSED keystones).

The forward-simulation square (`recAbsStep_forward`), its run-level lift, the non-vacuity guard,
and the obstruction lemmas are all PROVED-clean — each depends ONLY on the standard kernel axioms
(no `sorryAx`). Pinning them certifies the operational LTS fragment is genuinely closed, not a
`sorry`-alias. -/

#assert_axioms recAbsStep_forward
#assert_axioms recAbsStep_forward_exists
#assert_axioms recAbsStep_refines
#assert_axioms recAbsStep_run_forward
#assert_axioms recAbsStep_grounded
#assert_axioms recAbsStep_not_vacuous
#assert_axioms transfer_fires_no_authStep
#assert_axioms balance_turn_graph_is_fixed

/-! ## §7 — THE AUTHORITY-TURN HALF (now CLOSED) + the UNION = the complete single-cell LTS.

§3 closed the BALANCE-turn forward-simulation square (`recAbsStep`, authority FIXED). §5 PINNED that
the `AuthStep`-firing half is NOT a proof gap in that square but a *missing executable transition* —
an authority-mutating kernel that EDITS `caps`. `Exec/AuthTurn.lean` now BUILDS that transition
(`recKDelegate`, the executable Granovetter generative act) with its DUAL frame
(`recKDelegate_frame`: `recTotal` UNCHANGED — the conservation-trivial mirror of `recKExec_frame`'s
authority-fixed) and the graph-change match (`recKDelegate_execGraph`: the cap-edit IS
`Spec.addEdge`, i.e. `Spec.Endow`'s `result` verbatim, the same `execGraph` reconstruction). Here we
ASSEMBLE the authority-turn forward-simulation square and UNION it with the balance half. -/

/-- **`authAbsStep consents a a'`** — the abstract small-step LTS edge for an AUTHORITY turn (the
DUAL of `recAbsStep`):

  * (C') conservation frame — `a'.balanceTotal = a.balanceTotal` (an authority turn moves NO balance:
    `recKDelegate_frame`, the conservation-trivial dual of a balance turn's authority frame);
  * (A') the REAL authority edge — `Spec.AuthStep consents a.authGraph a'.authGraph`: the graph
    genuinely steps via an authorized `GenAct`/`RestrictAct` (here the generative `Endow`), the
    `AuthStep` firing §5 showed a balance turn could NOT produce.

This is the faithful authority-turn dynamics §4/§5 named: balance FIXED, an `AuthStep` FIRES. The
union of the two `authAbsStep`/`recAbsStep` kinds is the complete single-cell LTS. -/
def authAbsStep (consents : Label → Prop) (a a' : AbstractState) : Prop :=
  -- (C') the balance domain is fixed (an authority turn is conservation-trivial).
  a'.balanceTotal = a.balanceTotal ∧
  -- (A') the authority graph genuinely steps via an authorized `Spec.AuthStep`.
  Spec.AuthStep (CellId := Label) (Rights := ExecRights) consents a.authGraph a'.authGraph

/-- **KEYSTONE — `authAbsStep_forward` (PROVED-clean).** The forward-simulation square for the
AUTHORITY turn: every committed `recKDelegate` is matched by the abstract LTS edge `authAbsStep`,
for ANY `consents` (the `Endow` generative act consults no consent). Assembled from:

  * (C') ← `recKDelegate_frame` (the delegation preserves `recTotal` — balance FIXED);
  * (A') ← a `Spec.Endow` whose `holds_source` is `recKDelegate_grounds` (the delegator holds the
    source edge `delegator ⟶ ⟨t,()⟩`), `nonAmplifying` is `confers_refl` (the conferred edge equals
    the source — `ExecRights = Unit`, no amplification), and `result` is `recKDelegate_execGraph`
    (the cap-edit IS `addEdge … recipient ⟨t,()⟩`), lifted through `GenAct.endow`/`AuthStep.gen`.

This is the authority-half of the operational LTS, CLOSED — a genuine `AuthStep` fires. -/
theorem authAbsStep_forward (consents : Label → Prop)
    (k k' : RecordKernelState) (delegator recipient t : Label)
    (h : Exec.recKDelegate k delegator recipient t = some k') :
    authAbsStep consents (recAbsOf k) (recAbsOf k') := by
  -- The post-state's caps are the granted table; extract that equation.
  have hk' : k' = { k with caps := Exec.grant k.caps recipient (Authority.Cap.node t) } := by
    unfold Exec.recKDelegate at h
    by_cases hg : (k.caps delegator).any (fun cap => Exec.confersEdgeTo t cap) = true
    · rw [if_pos hg] at h; exact (Option.some.injEq _ _ ▸ h).symm
    · rw [if_neg hg] at h; exact absurd h (by simp)
  refine ⟨?_, ?_⟩
  · -- (C') the balance total is fixed (the DUAL frame).
    simp only [recAbsOf]
    exact (Exec.recKDelegate_frame k k' delegator recipient t h).1
  · -- (A') the authority graph fires a genuine `Endow` generative `AuthStep`.
    simp only [recAbsOf]
    -- `execGraph k'.caps = addEdge (execGraph k.caps) recipient ⟨t,()⟩` — the `Endow.result`.
    have hres : execGraph k'.caps
        = Spec.addEdge (execGraph k.caps) recipient (⟨t, ()⟩ : Spec.Cap Label ExecRights) := by
      rw [hk']
      exact Exec.recKDelegate_execGraph k.caps recipient t
    -- Build the `Endow`: parent = delegator, child = recipient, cap = source = ⟨t,()⟩.
    refine Spec.AuthStep.gen (Spec.GenAct.endow (parent := delegator) (child := recipient)
      (cap := ⟨t, ()⟩) (source := ⟨t, ()⟩) ?_)
    exact
      { holds_source := Exec.recKDelegate_grounds k k' delegator recipient t h
        nonAmplifying := Spec.confers_refl _
        result := hres }

/-! ### §7.1 — The UNION: `AbsStep'` = balance turn ∨ authority turn (the COMPLETE single-cell LTS).

The two turn KINDS §5 distinguished — a balance transfer (`recAbsStep`, authority fixed) and a
delegation (`authAbsStep`, an `AuthStep` fires) — union into ONE abstract step relation. This is the
single-cell operational LTS, complete: every executable transition the kernel emits (balance via
`recKExec`, authority via `recKDelegate`) is matched by an `AbsStep'`. -/

/-- **`AbsStep' consents a a'`** — the COMPLETE single-cell abstract LTS edge: EITHER a balance turn
(`AbsStep`, conservation move with authority FIXED) OR an authority turn (`authAbsStep`, an
`AuthStep` FIRES with balance FIXED). The union of the two turn kinds the §5 obstruction analysis
separated — both genuine, non-vacuous, forward-simulating abstract steps. -/
def AbsStep' (consents : Label → Prop) (a a' : AbstractState) : Prop :=
  AbsStep a a' ∨ authAbsStep consents a a'

/-- **KEYSTONE — `absStep'_forward_balance` (PROVED-clean).** A committed BALANCE turn is matched by
the union `AbsStep'` (via the left `AbsStep` disjunct, `recAbsStep_forward`). -/
theorem absStep'_forward_balance (consents : Label → Prop)
    (k k' : RecordKernelState) (turn : Turn) (h : recKExec k turn = some k') :
    AbsStep' consents (recAbsOf k) (recAbsOf k') :=
  Or.inl (recAbsStep_forward_exists k k' turn h)

/-- **KEYSTONE — `absStep'_forward_authority` (PROVED-clean).** A committed AUTHORITY turn is matched
by the union `AbsStep'` (via the right `authAbsStep` disjunct, `authAbsStep_forward`). -/
theorem absStep'_forward_authority (consents : Label → Prop)
    (k k' : RecordKernelState) (delegator recipient t : Label)
    (h : Exec.recKDelegate k delegator recipient t = some k') :
    AbsStep' consents (recAbsOf k) (recAbsOf k') :=
  Or.inr (authAbsStep_forward consents k k' delegator recipient t h)

/-- **`absStep'_forward` (PROVED-clean) — THE COMPLETE SINGLE-CELL OPERATIONAL LTS.** BOTH executable
transition kinds are matched by the union abstract step `AbsStep'`: a balance turn (`recKExec`) by
the `AbsStep` disjunct, an authority turn (`recKDelegate`) by the `authAbsStep` disjunct. Packaged as
one statement over the disjunction of the two executable transitions — every step the single-cell
record kernel can take is a forward-simulating abstract step. This is the single-cell operational
forward-simulation square, COMPLETE (both halves). -/
theorem absStep'_forward (consents : Label → Prop) (k k' : RecordKernelState)
    (h : (∃ turn, recKExec k turn = some k') ∨
         (∃ delegator recipient t, Exec.recKDelegate k delegator recipient t = some k')) :
    AbsStep' consents (recAbsOf k) (recAbsOf k') := by
  rcases h with ⟨turn, hb⟩ | ⟨delegator, recipient, t, ha⟩
  · exact absStep'_forward_balance consents k k' turn hb
  · exact absStep'_forward_authority consents k k' delegator recipient t ha

/-! ### §7.2 — The authority step's graph-change conjunct is LOAD-BEARING (non-vacuity).

The mirror of `recAbsStep_not_vacuous`: a no-op cap-edit must NOT fire a real `AuthStep`. We show
`authAbsStep` genuinely constrains the graph — a `consents`/states triple where the graph does NOT
step (the empty graph cannot `Endow`/`AuthStep` to itself, by `transfer_fires_no_authStep`) FAILS
`authAbsStep`, so the (A') conjunct does real work. -/

/-- **`authAbsStep_graph_steps` (PROVED)** — the authority edge can be PROJECTED OUT: `authAbsStep`
entails the authority graph genuinely steps via an `AuthStep`. The load-bearing fact distinguishing
an authority turn from a no-op. -/
theorem authAbsStep_graph_steps {consents : Label → Prop} {a a' : AbstractState}
    (h : authAbsStep consents a a') :
    Spec.AuthStep (CellId := Label) (Rights := ExecRights) consents a.authGraph a'.authGraph :=
  h.2

/-- **`authAbsStep_not_vacuous` (PROVED)** — `authAbsStep` is NOT always-true: over the EMPTY
authority graph (held fixed), NO `authAbsStep` holds, because no `AuthStep G G` exists on the empty
graph (`transfer_fires_no_authStep` — a no-op cap-edit fires no real `AuthStep`). This refutes "the
authority step is vacuously `True`": the (A') `AuthStep` conjunct is load-bearing, exactly as the
rails demand. -/
theorem authAbsStep_not_vacuous (consents : Label → Prop) :
    ∃ a a' : AbstractState, ¬ authAbsStep consents a a' := by
  refine ⟨{ balanceTotal := 0, authGraph := fun _ _ => False },
          { balanceTotal := 0, authGraph := fun _ _ => False }, ?_⟩
  rintro ⟨_, hstep⟩
  exact transfer_fires_no_authStep consents hstep

/-! ## §7.3 — Axiom-hygiene tripwires (the authority-half + union keystones, all CLEAN). -/

#assert_axioms authAbsStep_forward
#assert_axioms absStep'_forward_balance
#assert_axioms absStep'_forward_authority
#assert_axioms absStep'_forward
#assert_axioms authAbsStep_graph_steps
#assert_axioms authAbsStep_not_vacuous

/-! ## §8 — OUTCOME + the remaining (CROSS-CELL) residue.

The SINGLE-CELL operational LTS is now COMPLETE — both turn kinds closed:

  * BALANCE turn (`recKExec`)     ⟶ `recAbsStep` (authority FIXED, conservation move + grounding);
  * AUTHORITY turn (`recKDelegate`) ⟶ `authAbsStep` (balance FIXED, a genuine `Endow`/`AuthStep` fires);
  * their UNION `AbsStep'` matches BOTH executable transitions (`absStep'_forward`).

Each abstract step is genuine (non-vacuous: `recAbsStep_not_vacuous` / `authAbsStep_not_vacuous`),
axiom-clean (the `#assert_axioms` pins above), and a forward simulation of the concrete transition.

-- OPEN (the genuine remaining LONG-POLE residue, beyond the single cell). The CROSS-CELL /
--   whole-history graph bookkeeping — `Spec.Authority.only_connectivity_begets_connectivity`'s
--   closure over `Reachable` (a chain of `AuthStep`s) — lifted to a MULTI-cell adversary model
--   (concurrent cells, an adversary scheduler). The single-cell square here gives the per-step
--   forward simulation that closure consumes; the multi-cell lift (the coinductive `Boundary`
--   keystone over interleaved cells) is the next pole and is out of scope for THIS single-cell LTS.
--   It is NOT a gap in the single-cell square — that square is complete — but the next layer up.
-/

end Dregg2.Proof.LTS
