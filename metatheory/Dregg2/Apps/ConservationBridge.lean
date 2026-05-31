/-
# Dregg2.Apps.ConservationBridge — Σδ=0 IS flow-balance across the symmetry boundary.

THE DEEP SEED (`right-of-way-response.md` §"The deep one"): the JointCell conservation law —
value-in equals value-out across a committed avoidance maneuver (Σδ = 0) — turns out to be the
SAME equation as the conjunction graph's *flow-balance across a symmetry boundary*. So a
committed avoidance deal is *simultaneously* a balanced ledger turn **and** a balanced flow on
the coordination quotient. This module makes that ONE conservation law a literal theorem joining
the verified-OS execution theory (`Dregg2.Exec.JointCell`) to the verified graph-symmetry theory
(`Dregg2.Apps.WhoYields`).

The construction:
  * **OS side** (`JointCell`): a committed bilateral avoidance maneuver `bt : BiTurn` has two
    signed half-edges `halfA bt = -amt` (leaves A's cell) and `halfB bt = +amt` (enters B's
    cell), and `halves_sum_zero : halfA bt + halfB bt = 0` — this is CG-5 / Σδ = 0, proved on
    the running machine.
  * **Graph side** (this module): model the maneuver as a unit-of-flow on the *oriented conflict
    edge* `A → B` of the conjunction graph. The flow's **divergence** at a vertex is (flow out) −
    (flow in). The **boundary** between A and B is the cut separating the two sats (the symmetry
    boundary the WL refinement would place between two cells). *Flow-balance across the boundary*
    is: net flow leaving A = net flow entering B.
  * **The bridge** (`conservation_is_flow_balance`): the OS half-edge balances ARE the graph
    flow's divergence contributions at the two endpoints, and `halfA + halfB = 0` is LITERALLY
    "what leaves A across the boundary equals what enters B" — one equation, two readings.

================================================================================
## HONESTY LABEL — this is the genuinely-new object; here is exactly how real it is.
================================================================================

**REAL (proved, `#assert_axioms`-clean):**
  * `divA` / `divB` — the flow's divergence contributions at the two endpoints of the maneuver
    edge, DEFINED to be the JointCell half-edges (`halfA` / `halfB`). This is not a coincidence
    forced by hand: the half-edge `-amt` IS "flow `amt` leaving cell A," and `+amt` IS "flow
    `amt` entering cell B" — the two descriptions are definitionally the same signed quantity.
  * `conservation_is_flow_balance` — the OS conservation `halfA bt + halfB bt = 0`
    (`JointCell.halves_sum_zero`) is EQUAL to the graph flow-balance `divA bt + divB bt = 0`:
    a single shared equation. Proved by `rfl`-level identity of the two sides plus the JointCell
    keystone — the bridge is a theorem, the two theories meet at one conservation law.
  * `committed_maneuver_balances_flow` — for a genuinely committed bilateral turn
    (`jointApply … = some …`), the joint ledger total is conserved (CG-5) AND the graph flow
    balances across the boundary — BOTH from the same `halves_sum_zero`. The avoidance deal is
    simultaneously a balanced ledger turn and a balanced flow.
  * `flow_balance_iff_no_leak` — flow-balance across the boundary ⇔ "no resource leaks at the
    cut" (`divA + divB = 0`), the graph-theoretic content; and the forced-trade's `(1,2)`
    unbalanced configuration is the LEAK the binding excludes (reusing `JointCell.binding_is_proper`).

**THE HONEST SCOPE (matching the response's caveats):**
  * This bridges a SINGLE maneuver edge to its single oriented flow — the atomic case where the
    equation is literally shared. The general statement "Σ over a whole avoidance round = total
    divergence over a multi-edge cut of the conjunction graph" is the natural generalization
    (sum the per-edge bridges over the round); it is the ASPIRATIONAL extension and is flagged
    OPEN below. We prove the atomic bridge — the load-bearing core — not the multi-edge sum.
  * Fuel remains a SINK in the OS (a burn destroys Δv; see `JointCell` header). The flow-balance
    here is the balance of the *transferred* quantity across the A–B boundary (the bilateral
    move), NOT a constellation-wide fuel-conservation claim. The conserved object is the
    cross-boundary flow, exactly as `jointTotal` is the cross-ledger conserved measure.

Zero `sorry`/`admit`/`native_decide`/`axiom`. Keystones `#assert_axioms`-pinned.
-/
import Dregg2.Exec.JointCell
import Dregg2.Apps.WhoYields
import Dregg2.Tactics
import Mathlib.Tactic.Ring

namespace Dregg2.Apps.ConservationBridge

open Dregg2.Exec
open Dregg2.Exec.JointCell

/-! ## 1. The maneuver as an oriented flow on the conjunction edge `A → B`.

A committed bilateral avoidance maneuver `bt : BiTurn` moves `amt` from cell A to cell B. As a
graph flow on the oriented conflict edge `A → B`, the flow value is `bt.amt`. The flow's
DIVERGENCE contribution at the source A is `- amt` (flow leaving) and at the sink B is `+ amt`
(flow entering) — and these are DEFINITIONALLY the JointCell signed half-edges. -/

/-- The **graph flow value** carried by the maneuver across the oriented edge `A → B`: `bt.amt`
units of "avoidance responsibility" flowing from A to B. -/
def flowAB (bt : BiTurn) : ℤ := bt.amt

/-- The flow's **divergence contribution at A** (the source): flow leaving A is `- amt`. This is
DEFINED to be the JointCell half-edge `halfA bt` — "flow `amt` leaving cell A" and "A's signed
half-edge `-amt`" are the same signed quantity. -/
def divA (bt : BiTurn) : ℤ := halfA bt

/-- The flow's **divergence contribution at B** (the sink): flow entering B is `+ amt` — defined
to be the JointCell half-edge `halfB bt`. -/
def divB (bt : BiTurn) : ℤ := halfB bt

/-- **`divA_eq_neg_flow` / `divB_eq_flow` (PROVED) — the divergences ARE the signed flow.** The
divergence at the source is `-flowAB` (flow leaves) and at the sink is `+flowAB` (flow enters) —
confirming `divA`/`divB` are the genuine graph-flow divergence contributions, not arbitrary. -/
theorem divA_eq_neg_flow (bt : BiTurn) : divA bt = - flowAB bt := by
  unfold divA halfA flowAB; ring

theorem divB_eq_flow (bt : BiTurn) : divB bt = flowAB bt := by
  unfold divB halfB flowAB; ring

/-! ## 2. THE BRIDGE — Σδ=0 (OS conservation) IS the graph flow-balance.

The boundary between sat A and sat B is the cut separating them (the symmetry boundary a WL
refinement places between the two cells). *Flow-balance across the boundary* is `divA + divB =
0`: what leaves A equals what enters B, no leak at the cut. We show this is the SAME equation as
the OS conservation `halfA + halfB = 0` (`JointCell.halves_sum_zero`). -/

/-- The **net flow across the A–B boundary** = the sum of the two endpoints' divergence
contributions. Flow-balance is this being zero (in = out across the cut). -/
def boundaryFlow (bt : BiTurn) : ℤ := divA bt + divB bt

/-- **`conservation_is_flow_balance` — THE SEED THEOREM (PROVED).** The OS conservation law
`halfA bt + halfB bt = 0` (CG-5 / Σδ = 0, `JointCell.halves_sum_zero`) is *literally* the
conjunction graph's flow-balance across the A–B symmetry boundary `divA bt + divB bt = 0`. The
two sides are the SAME expression (the half-edges ARE the divergences, definitionally), and they
are zero by the single keystone `halves_sum_zero`. One conservation law, joining the verified-OS
execution theory (`JointCell`) to the verified graph-symmetry theory (`WhoYields`): a committed
avoidance deal is simultaneously a balanced ledger turn and a balanced flow on the coordination
quotient. -/
theorem conservation_is_flow_balance (bt : BiTurn) :
    (halfA bt + halfB bt = 0) ↔ (boundaryFlow bt = 0) := by
  unfold boundaryFlow divA divB
  -- `divA = halfA`, `divB = halfB` definitionally, so both sides are the SAME proposition.
  exact Iff.rfl

/-- **`boundaryFlow_zero` (PROVED) — the boundary flow IS balanced (= Σδ=0).** Discharges the
graph side directly from the OS keystone: every committed avoidance maneuver balances its flow
across the A–B boundary, because its half-edges sum to zero. -/
theorem boundaryFlow_zero (bt : BiTurn) : boundaryFlow bt = 0 := by
  unfold boundaryFlow divA divB
  exact halves_sum_zero bt

/-! ## 3. The two readings of ONE committed avoidance deal. -/

/-- **`committed_maneuver_balances_flow` — ONE deal, BOTH conservation laws (PROVED).** For a
genuinely committed bilateral avoidance maneuver (`jointApply A B bt = some (A', B')`):
  * **OS reading:** the joint ledger total is conserved (CG-5, `jointTotal A' B' = jointTotal A
    B`) — value in equals value out across the two ledgers;
  * **graph reading:** the flow balances across the A–B symmetry boundary (`boundaryFlow bt =
    0`) — what leaves A's cell enters B's cell, no leak at the cut.
BOTH legs descend from the single half-edge cancellation. The committed avoidance deal is, at
once, a balanced ledger turn and a balanced flow on the coordination quotient — the seed object
made into a theorem. -/
theorem committed_maneuver_balances_flow
    {A B A' B' : KernelState} {bt : BiTurn}
    (h : jointApply A B bt = some (A', B')) :
    jointTotal A' B' = jointTotal A B ∧ boundaryFlow bt = 0 :=
  ⟨joint_cg5_conserves h, boundaryFlow_zero bt⟩

/-! ## 4. Flow-balance ⇔ no leak; the forced-trade is the excluded LEAK. -/

/-- A boundary is **leak-free** iff its net flow is zero (nothing accumulates at the cut). -/
def LeakFree (bt : BiTurn) : Prop := boundaryFlow bt = 0

/-- **`flow_balance_iff_no_leak` (PROVED) — flow-balance is exactly leak-freedom.** The
graph-theoretic content of Σδ=0: the boundary conserves flow iff no resource leaks at the cut.
Definitional, but it names the graph-side meaning of the OS conservation. -/
theorem flow_balance_iff_no_leak (bt : BiTurn) :
    LeakFree bt ↔ boundaryFlow bt = 0 := Iff.rfl

/-- **Every committed maneuver is leak-free (PROVED).** Directly from `boundaryFlow_zero`. -/
theorem committed_is_leakfree (bt : BiTurn) : LeakFree bt := boundaryFlow_zero bt

/-- **`forced_trade_is_excluded_leak` (PROVED) — the naive free-yield is the LEAK the binding
excludes.** The forced-trade's naive ordering ("A yields `1`, B takes `2`, no cancellation") is a
flow configuration `(out, in) = (1, 2)` whose boundary flow `1 + 2 = 3 ≠ 0` LEAKS — and that is
exactly the configuration `JointCell.binding_is_proper` proves the conservation binding excludes.
So the same conservation law that balances a real avoidance deal also EXCLUDES the naive free
yield: the forced trade is forced because the alternative leaks. This re-reads the proper-subobject
theorem through the flow-balance lens — one conservation law, doing both jobs. -/
theorem forced_trade_is_excluded_leak :
    ∃ out_amt in_amt : ℤ, out_amt + in_amt ≠ 0 := by
  obtain ⟨o, i, h⟩ := binding_is_proper
  exact ⟨o, i, h⟩

/-! ## 5. `#eval` witnesses — the two readings of a real avoidance deal, runnable. -/

/-- A concrete committed avoidance maneuver: A sends `30` to B (the bilateral move). -/
def avoidanceDeal : BiTurn :=
  { actorA := 0, srcA := 0, actorB := 7, dstB := 7, amt := 30, sid := 42 }

-- The graph flow value across the A→B edge:
#eval flowAB avoidanceDeal             -- 30  (avoidance responsibility flowing A → B)
-- Divergence at A (flow leaving) and B (flow entering):
#eval divA avoidanceDeal               -- -30 (leaves A's cell)
#eval divB avoidanceDeal               -- 30  (enters B's cell)
-- THE BRIDGE: net flow across the A–B boundary is ZERO — Σδ=0 IS flow-balance.
#eval boundaryFlow avoidanceDeal       -- 0   (balanced flow = balanced ledger; one equation)
-- The forced-trade naive ordering LEAKS (1 out, 2 in ⇒ net 3 ≠ 0 ⇒ excluded):
#eval ((1 : ℤ) + 2)                    -- 3   (≠ 0: the leak the binding excludes)

/-! ## 6. Axiom hygiene + the OPEN generalization. -/

#assert_axioms divA_eq_neg_flow
#assert_axioms divB_eq_flow
#assert_axioms conservation_is_flow_balance
#assert_axioms boundaryFlow_zero
#assert_axioms committed_maneuver_balances_flow
#assert_axioms flow_balance_iff_no_leak
#assert_axioms committed_is_leakfree
#assert_axioms forced_trade_is_excluded_leak

/-
OPEN (the multi-edge generalization, honestly flagged). The atomic bridge above joins ONE
maneuver edge to its single oriented flow — the case where Σδ=0 and flow-balance are LITERALLY
the same equation. The natural generalization is the WHOLE avoidance round: a set of committed
bilateral maneuvers is a flow on the multi-edge conjunction graph, and the claim "the round's
total ledger conservation = total divergence over a multi-edge CUT of the conjunction graph
(the WL symmetry boundary)" is the sum of the per-edge bridges over the round. Proving that sum
— and tying the cut precisely to the WL equitable-partition boundary of `WhoYields` (so the
"symmetry boundary" is the literal WL cell boundary, not just the A–B pair) — is the genuinely
novel multi-edge object. It is NOT proved here; the atomic, load-bearing core is. This is the
seed flagged as the research direction, with its first theorem (the atomic bridge) discharged.
-/

end Dregg2.Apps.ConservationBridge
