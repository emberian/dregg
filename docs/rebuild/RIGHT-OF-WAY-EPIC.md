# RIGHT-OF-WAY-EPIC — the verified orbital-collision referee, de-toyed.

> **What this is.** The toy "verified collision-avoidance referee"
> (`metatheory/Dregg2/Apps/RightOfWay.lean`) grown into an *as-real-as-we-can* demonstration of
> dregg2's power to reason about **distributed epistemic** problems — for an orbital
> right-of-way / collision-avoidance pitch. Five Lean modules, all build green on the dregg2
> toolchain (`lake build Dregg2`, 3466 jobs), **60 keystones** `#assert_axioms`-pinned to
> `{propext, Classical.choice, Quot.sound}`, **zero** `sorry`/`admit`/`native_decide`/`axiom` in
> any definition.

The discipline (non-negotiable): everything below is labelled **REAL** (a term-proved theorem
with teeth), **MODEL** (an honest modelling choice), or **OPEN/ASPIRATIONAL** (named, not faked).
A smaller real thing beats a bigger fake one — overclaiming would destroy the pitch.

---

## 0. The one-line pitch, discharged

> *Every other team's collision referee is a Python `screen_conjunctions` you take on faith.
> Ours is a machine-checked theorem — and the physics inside it is sound on the **continuous**
> trajectory, the who-yields tie-break is **forced by graph rigidity**, the consensus is a
> **global section** reached with no central cop, and the conservation law of a committed
> avoidance deal is **literally** a balanced flow on the coordination graph.*

Each clause is a compiling Lean theorem. The `file:line` table is §6.

---

## 1. The five modules (the build)

| Module | Role | Headline theorem |
|---|---|---|
| `Dregg2.Apps.OrbitalScreen` | **de-toy #1** — REAL conservative physics | `screen_clear_imp_continuous_clear` |
| `Dregg2.Apps.WhoYields` | **de-toy #2** — graph-symmetry who-yields (ported WL) | `rigid_of_discrete` |
| `Dregg2.Apps.EpistemicSheaf` | **the spine** — sheaf of verifiers (H⁰/H¹ content) | `consensus_on_clearance` / `byzantine_section_does_not_glue` |
| `Dregg2.Apps.ConservationBridge` | **the deep seed** — Σδ=0 = flow-balance | `conservation_is_flow_balance` |
| `Dregg2.Apps.RightOfWay` | **the referee** — seam + the real screen plugged in | `referee_sound` / `referee_sound_physics` |

Build standalone: `export PATH="$HOME/.elan/bin:$PATH"; lake build Dregg2.Apps.RightOfWay`
(and the four siblings). Full root: `lake build Dregg2` (green, 3466 jobs).

---

## 2. de-toy #1 — a CONSERVATIVE, continuous-time-SOUND physics screen (the sharp risk)

**The risk the response flagged:** a "clear" verdict on *sampled* times that misses a
**between-samples closest approach** (discretization error). A referee that only checks sample
instants is unsound on the continuous orbit.

**The fix (REAL).** `OrbitalScreen` models the relative pair's motion over a maneuver step as an
**affine** trajectory `d(t) = d0 + t·v` (the exact structure of linearized Clohessy–Wiltshire /
Hill relative dynamics over a short step; the first-order truth for any C¹ relative motion). The
squared separation `‖d(t)‖²` is then a quadratic in `t` (an upward parabola, `sepSq_eq_quadratic`),
so its **continuous minimum over `[0,T]`** is attained at a *computable* closest-approach time
(`tca` = the parabola vertex clamped into the step). The screen checks the separation **at that
minimum**, so:

> **`screen_clear_imp_continuous_clear` (REAL).** If the screen returns `clear`, then at **every**
> continuous time `t ∈ [0,T]` the separation is ≥ threshold — the screen OVER-APPROXIMATES the
> conjunction set; a `clear` verdict is sound on the continuous trajectory, not just at samples.

**The teeth (REAL).** A crossing pair `d0=(0,10,0), v=(0,-2,0)` is clear at both endpoints
(`sepSq=100` at `t=0` and `t=10`) but collides dead-center at `t=5` (`sepSq=0`). An endpoint
sampler accepts it (`endpoints_look_clear`); our screen **rejects** it (`screen_rejects_crossing`)
because it sees the mid-step closest approach. The continuous screen is genuinely stronger than
"clear at the samples."

**The honest fallback (REAL).** For trajectories only known to be *speed-bounded* (`‖v‖ ≤ vmax`,
true for any nonlinear relative motion over a bounded step), `coarseClear` certifies clearance via
the reverse-triangle bound `sep(0) − vmax·T ≥ thr` (`coarse_clear_imp_lipschitz_clear`) — sound
for **any** speed-bounded continuous trajectory, no affinity assumed.

**Residual (OPEN, flagged in the module):** the curvature term. The true CW solution adds bounded
oscillatory/secular `O(n²t²)` terms over a long horizon; a curvature-aware screen would bound
`sepSq` below by the affine value minus a `½κt²` envelope. We prove EXACT-for-affine +
CONSERVATIVE-for-speed-bounded; the second-order envelope is the next refinement, **not** faked.

---

## 3. de-toy #2 — who-yields from LOCAL data, by a graph-rigidity THEOREM

**The "is multi-agent even the right tool?" answer, Leaned.** `WhoYields` is a computable,
`#eval`-able **port** of graphplay's equitable-partition / 1-WL color-refinement engine
(`~/dev/graphplay/Graphplay/Algorithm/WLRefinement.lean`; Weisfeiler–Leman 1968), with the flat
`ℕ`-hash color encoding graphplay itself recommends (its spectral engine's nested-multiset colors
*stall* `lake build` under `#eval`; ours runs).

- **`rigid_of_discrete` (REAL).** If the conjunction graph is WL-discrete on its edges
  ("asymmetric"), the who-yields role is **forced** for every conflicting pair: distinct roles, a
  unique yielder by the deterministic "lower role yields" rule — **no central authority, no
  negotiation**. The verified, terminating who-yields tie-break "from purely local data." (The
  concrete-graph analog of graphplay's `wlStable_discrete_imp_rigid`.)
- **`symmetric_needs_negotiation` (REAL, the teeth).** If two conflicting sats share a role
  (WL-indistinguishable), the deterministic rule is **silent** — neither is strictly lower — so a
  genuine back-and-forth is required. *Negotiation is load-bearing exactly at the symmetric cells*
  — a theorem about where the deterministic referee runs out.
- **`three_mutual_conflict_needs_three_roles` / `triangle_three_distinct_roles` (REAL, the
  round-cap floor).** Three mutually-conflicting sats (a `K₃` triangle) need ≥3 distinct roles —
  the chromatic-number lower bound that justifies the orchestrator's round-cap.
- **`outOfFuel_breaks_symmetry` (REAL, the forced-trade's SECOND proof).** Tagging one sat
  "out of fuel" is a vertex-color that breaks the symmetry the naive priority-only rule assumed —
  so a rigid assignment exists even on symmetric geometry. The out-of-fuel sat is *what makes B
  the forced yielder.*

**Proof technique note (honest):** rigidity is proved **structurally** (refinement only splits —
`refine_refines`, `roleOf_distinct_of_tag`) so the keystones need NO kernel-reduction of the
`mergeSort`/`dedup` WL machinery; the `#eval`s run the real computation via the compiler.
**Residual:** WL is sound-but-not-complete for asymmetry (Cai–Fürer–Immerman graphs are rigid yet
WL-indistinguishable), so `rigid_of_discrete` is the honest one-directional theorem — exactly as
graphplay states it. We do not claim the converse.

---

## 4. THE SPINE — the constellation as a SHEAF OF VERIFIERS (the distributed-epistemic heart)

The constellation is a **sheaf of verifiers**: each satellite/operator is a *local verifier* with
**partial knowledge** of the orbital picture, mutually distrusting. Consensus on a collision-
avoidance deal is a **global section** (H⁰); a fork/disagreement is the **obstruction** (H¹). The
referee-as-theorem means consensus needs **no trusted central cop**. (`EpistemicSheaf`, built on a
faithful port of `Metatheory/EpistemicConsensus` — Goubault et al., arXiv:2311.01351 — and the
finite-gluing pattern of `docs/rebuild/SHEAF-OF-VERIFIERS.md`.)

- **Consensus = a global section (H⁰ CONTENT, REAL).** `consensus_on_clearance`: if the
  *conservative* screen certifies a pair clear (the REAL physics from §2), then "the maneuver
  clears the conjunction" is **distributed knowledge of the honest operators** at the actual
  orbital world — each operator's own `Verify` settles it; world-independent, so it survives every
  partial-knowledge edge. No central authority. Fork-unforgeable (`no_consensus_on_unscreened`),
  composes under a re-screen (`consensus_composes`).
- **The fork = witnessed NON-gluing (the OBSTRUCTION, REAL).** A 2-operator overlap: each
  operator screens its sub-window and reports a boundary separation; the sections **glue** iff both
  are locally valid AND agree on the overlap (`glued_global_section`). A **Byzantine** operator
  that locally "verifies" (`verdict=true`) but reports a different boundary (`5 ≠ 99`) **fails to
  glue** (`byzantine_section_does_not_glue`) — no global section. The obstruction lives **entirely
  in the overlap disagreement** (`fork_is_genuine`: both individually valid). The exact orbital
  twin of `¬ chainLinked [node0, badNode]`.

**Honesty (matching SHEAF-OF-VERIFIERS exactly):** the **content** (gluing, witnessed non-gluing,
honest distributed knowledge) is REAL and proved. The cohomology **objects** (a Čech complex, `δ⁰`,
an `H⁰`/`H¹` group, a functorial `ρ`, a `Presheaf` instance) are **NOT built** — calling this
"cohomology" would let vocabulary stand in for an absent coboundary. We ship the gluing as a
gluing (REAL) and CITE the "consensus = H⁰, fork = sound H¹ detector" framing as ESTABLISHED in
the lit, POETRY-as-object inside dregg.

---

## 5. THE DEEP SEED — Σδ=0 IS flow-balance across the symmetry boundary

The genuinely novel object (`ConservationBridge`). The JointCell conservation law — value-in =
value-out across a committed avoidance maneuver (**Σδ = 0**, `JointCell.halves_sum_zero`) — is the
**same equation** as the conjunction graph's **flow-balance across a symmetry boundary**.

- Model the maneuver as a unit-of-flow on the oriented conflict edge `A → B`. The flow's
  **divergence** at source A is `-amt` (flow leaving) and at sink B is `+amt` (flow entering) —
  and these are **definitionally** the JointCell half-edges (`divA = halfA`, `divB = halfB`;
  `divA_eq_neg_flow`, `divB_eq_flow`).
- **`conservation_is_flow_balance` (REAL, the seed theorem).** The OS conservation
  `halfA + halfB = 0` **is** the graph flow-balance `boundaryFlow = divA + divB = 0` — the same
  expression, two readings. One conservation law joining the **verified-OS execution theory**
  (`JointCell`) to the **verified graph-symmetry theory** (`WhoYields`).
- **`committed_maneuver_balances_flow` (REAL).** A genuinely committed bilateral maneuver is, at
  once, a **balanced ledger turn** (CG-5, `jointTotal` conserved) AND a **balanced flow** on the
  coordination quotient (`boundaryFlow = 0`) — both from the single half-edge cancellation.
- **`forced_trade_is_excluded_leak` (REAL).** The naive free-yield `(1 out, 2 in)` is a flow that
  **leaks** (`1+2 ≠ 0`) — exactly the configuration `binding_is_proper` excludes. The same
  conservation law that balances a real deal **excludes the naive free yield**: the forced trade
  is forced because the alternative leaks.

**Residual (OPEN):** this is the **atomic** bridge (one edge ↔ one flow, where the equation is
literally shared). The multi-edge generalization — a whole avoidance round's total ledger
conservation = total divergence over a multi-edge **cut** of the conjunction graph, tied precisely
to the WL equitable-partition cell boundary — is the natural sum-over-edges extension, flagged
OPEN. The load-bearing core is proved.

---

## 6. The demo arc (what a judge sees) + the theorem table

**Arc.** (1) Constellation rotating, all green — "these satellites coordinate with no ground
control." (2) Inject a conjunction; A and B flash red. A is out of fuel — naive "low-priority
yields" is **impossible** (`outOfFuel_cannot_burn`, the budget gate). (3) The who-yields role is
**forced by a theorem** (`rigid_of_discrete`) where the geometry is asymmetric, and the out-of-fuel
flag **breaks the symmetry** that forces B to trade (`outOfFuel_breaks_symmetry`) — the forced
trade is a theorem, not an if. (4) B commits a maneuver; the **conservative referee re-screens** —
and the screen is sound on the **whole continuous step** (`referee_sound_physics`), catching a
between-samples conjunction an endpoint sampler would miss (`physReferee_rejects_crossing`). (5)
The honest operators reach **consensus = a global section** with no central cop
(`consensus_on_clearance`); a Byzantine operator's disagreement is a **witnessed fork**
(`byzantine_section_does_not_glue`). (6) Close: *the committed deal is simultaneously a balanced
ledger turn and a balanced flow on the coordination graph* (`conservation_is_flow_balance`) — one
conservation law, the research seed.

**The theorems (all `#assert_axioms`-clean, `{propext, Classical.choice, Quot.sound}`):**

| Beat | Theorem | Location |
|---|---|---|
| referee accepts only safe maneuvers, vs adversary | `referee_sound` | `RightOfWay.lean` |
| committed ⇒ clear on the WHOLE CONTINUOUS step | `referee_sound_physics` | `RightOfWay.lean` |
| the screen is continuous-time sound (the de-toy) | `screen_clear_imp_continuous_clear` | `OrbitalScreen.lean` |
| the screen catches a between-samples crossing | `screen_rejects_crossing` | `OrbitalScreen.lean` |
| conservative referee rejects the sampler's "clear" | `physReferee_rejects_crossing` | `RightOfWay.lean` |
| out-of-fuel sat cannot yield (budget gate) | `outOfFuel_cannot_burn` | `RightOfWay.lean` |
| forced trade = proper subobject | `forced_trade_excludes_naive` | `RightOfWay.lean` |
| who-yields forced by graph rigidity | `rigid_of_discrete` | `WhoYields.lean` |
| negotiation load-bearing at symmetric cells | `symmetric_needs_negotiation` | `WhoYields.lean` |
| ≥3-conflict ⇒ ≥3 roles (round-cap floor) | `three_mutual_conflict_needs_three_roles` | `WhoYields.lean` |
| out-of-fuel breaks symmetry (forced trade, 2nd proof) | `outOfFuel_breaks_symmetry` | `WhoYields.lean` |
| collision-safety must escalate (not I-confluent) | `collisionSafety_must_escalate` | `RightOfWay.lean` |
| consensus = global section (H⁰ content) | `consensus_on_clearance` | `EpistemicSheaf.lean` |
| fork = witnessed obstruction | `byzantine_section_does_not_glue` | `EpistemicSheaf.lean` |
| Σδ=0 IS flow-balance (the seed) | `conservation_is_flow_balance` | `ConservationBridge.lean` |
| committed deal: balanced ledger AND balanced flow | `committed_maneuver_balances_flow` | `ConservationBridge.lean` |

---

## 7. The honesty ledger (one place, no spin)

**REAL (term-proved, axiom-clean, with teeth):** the conservative continuous-time-sound screen
(EXACT for affine, CONSERVATIVE-Lipschitz for speed-bounded); the adversary-proof referee carrying
that real physics; the WL who-yields rigidity + the symmetric-cell teeth + the chromatic round-cap
floor; the budget gate / forced-trade proper-subobject; the escalation classifier; honest
distributed knowledge = consensus as a global section; the witnessed Byzantine non-gluing; the
atomic Σδ=0 ↔ flow-balance bridge.

**MODEL (honest choices):** relative motion is affine-over-a-step (rationals, exact metric);
fuel is a SINK (a burn destroys Δv — no constellation-wide fuel conservation; the conserved object
is the cross-boundary transferred quantity); vertices are `Fin n`, conflict a decidable symmetric
relation; the epistemic frame is the ported `EpistemicConsensus` distributed-knowledge model.

**OPEN / ASPIRATIONAL (named, never faked):** the curvature (`O(n²t²)`) envelope for a fully-
general long-horizon continuous guarantee; the WL converse (rigid ⇏ WL-discrete, CFI); the
cohomology *objects* (Čech complex, `δ⁰`, `H⁰`/`H¹` groups, functorial `ρ`, `Presheaf`) — content
REAL, object POETRY; the multi-edge conservation=flow-balance generalization over a WL cut;
whole-protocol liveness / round-cap convergence (lives in the orchestrator, not a theorem).

( •_•)>⌐■-■  the referee is a theorem; the physics is real; the egg keeps its eyes honest.
