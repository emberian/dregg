/-
# Dregg2.Verify.Catalog — the Hatchery's SHAPE CATALOG (HATCHERY.md Tier 4).

Tier 3 (`Verify/Contract.lean`) made a verified invariant a first-class VALUE (`CellContract`): the
author supplies `(Inv, step_ob)` and gets `forever` / `always` free. But the author still hand-writes
`step_ob`. This module is Tier 4 — the **declarative spec language** (`HATCHERY.md §128–§151`): the
five safety SHAPES we keep re-deriving become *macros*. The author names a FIELD (and the data the
shape needs — a tracked element, an asset, an authority ceiling, two asset classes) and the macro
EXPANDS to a real `CellContract` whose `step_ob` is discharged THROUGH the Tier-1/2 engine
(`exec_frame` / the registered `[Dregg2]` frame lemmas / the per-asset conservation lemma / field
algebra). No hand proof — *this is the smart-contract spec language* (`HATCHERY.md §130`).

## The four shapes shipped (the safety-only `□` fragment — `HATCHERY.md §144`)

| macro                       | property class            | `Inv`                                    | one-step discharge                          |
|-----------------------------|---------------------------|------------------------------------------|---------------------------------------------|
| `monotone_registry% f x`    | grow-only set membership  | `x ∈ ·.kernel.f`                         | `exec_frame` + the registered `f`-grow lemma |
| `conservation% a`           | equality of a measure     | `cellObsA · a = cellObsA s0 a`           | the per-asset `cellObsA_next` (rewrite)     |
| `confinement% U`            | authority ⊆ a ceiling     | `CapsConfined U ·.kernel.caps`           | `cellNextA_confine` (the `[Dregg2]` cap step) |
| `automaton_inv% a b`        | linear relation of fields | `obs·a + obs·b = obs s0 a + obs s0 b`    | `cellObsA_next` ×2 + `omega` (field algebra) |

Each macro produces a REAL `CellContract` (NOT a stub): the `step_ob` field is filled by a tactic that
runs the executor case-split and closes BOTH arms. The GATE (`§5`) shows each macro, applied
to its canonical field, elaborating to a building contract — and `monotone_registry% revoked`
reproducing `Apps.Identity.livingCellA_identity_revoked_forever` as a *one-liner* `.forever` call.

## Liveness shape (`eventually% Goal` — `Verify/LivenessContract.lean`)

`eventually% Goal` names a `LivenessContract` whose `.Goal` is discharged via `just_progress` /
`AF_just` (van Glabbeek justness — NOT naive `◇` over stutter schedules). Kernel witnesses live in
`Proof/Fairness`; production `EventuallyG` on `trajG` is in `LivenessBridge` / `LivenessContract`
(§5b — the public API customers ship against).

Every macro-emitted contract + its `forever`/
`always` payoff is `#assert_axioms`-pinned to the kernel triple `{propext, Classical.choice,
Quot.sound}` at the foot of the file. The macros emit ordinary kernel-checked terms — the catalog
cannot launder a gap into a false "PROVED": if a discharge tactic failed, the elaboration would error.
-/
import Dregg2.Verify.Contract
import Dregg2.Verify.LivenessContract
import Dregg2.Exec.CellConfine

namespace Dregg2.Verify

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (fma0)
open Dregg2.Exec.FullForest
open Dregg2.Authority
open Dregg2.Proof.Temporal (Always)
open Dregg2.Proof.Fairness (Pgoal)
open KernelForest (Contract Sched)
open Production (Contract Sched liftFromKernelForest)

/-! ## §1 — `monotone_registry% f x` — "once `x` is in registry `f`, it stays — forever".

The grow-only registry shape (`HATCHERY.md §133–§135, §147`): the three kernel registries `revoked`
(`#139` revocation root-of-trust), `commitments` (`#121` Pedersen commitment tree), `nullifiers`
(anti-double-spend) are all GROW-ONLY — a committed forest only ever extends them
(`execFullForestA_{revoked,commitments,nullifiers}_grow`, the `⊆`-shaped forest lemmas registered in
the `[Dregg2]` rule-set). So a tracked element `x` that is present stays present.

`monotone_registry% f x` expands to the membership contract `Inv s := x ∈ s.kernel.f` with `shape :=
.membership`. The `step_ob` is the executor case-split (`cellNextA` = commit-on-`some` / stay-put-on-
`none`): on a **commit** the registered `f`-grow lemma `… s s' cf.1 hc` gives `s.kernel.f ⊆ s'.kernel.f`,
APPLIED to the membership hypothesis (`⊆` is `∀ {a}, a ∈ · → a ∈ ·`) to relocate `x` into `s'`; on a
**reject** the stay-put self-loop leaves the state — and so the membership — unchanged. This is exactly
`Contract.revokedPersists`, generalized over the three grow-only registries by the field name. -/

/-- **`monotone_registry% f x`** (`f ∈ {revoked, commitments, nullifiers}`) — the grow-only-registry
contract: `x ∈ ·.kernel.f`, carried by the registered forest-grow lemma. Produces a real
`CellContract` (`shape := .membership`); `.forever` then gives *"`x` stays in `f` at every index of
every adversarial trajectory"* with no hand proof. -/
syntax (name := monotoneRegistryStx) "monotone_registry% " ident ppSpace term:max : term

macro_rules
  | `(monotone_registry% revoked $x:term) =>
    `(({  Inv := fun s => $x ∈ s.kernel.revoked
          step_ob := fun a cf h => by
            show $x ∈ (cellNextA a cf).kernel.revoked
            unfold cellNextA
            cases hc : execFullForestA a cf.1 with
            | some a' => simp only [Option.getD_some]
                         exact Dregg2.Apps.Identity.execFullForestA_revoked_grow a a' cf.1 hc h
            | none    => simp only [Option.getD_none]; exact h
          shape := .membership } : KernelForest.Contract))
  | `(monotone_registry% commitments $x:term) =>
    `(({  Inv := fun s => $x ∈ s.kernel.commitments
          step_ob := fun a cf h => by
            show $x ∈ (cellNextA a cf).kernel.commitments
            unfold cellNextA
            cases hc : execFullForestA a cf.1 with
            | some a' => simp only [Option.getD_some]
                         exact Dregg2.Exec.execFullForestA_commitments_grow a a' cf.1 hc h
            | none    => simp only [Option.getD_none]; exact h
          shape := .membership } : KernelForest.Contract))
  | `(monotone_registry% nullifiers $x:term) =>
    `(({  Inv := fun s => $x ∈ s.kernel.nullifiers
          step_ob := fun a cf h => by
            show $x ∈ (cellNextA a cf).kernel.nullifiers
            unfold cellNextA
            cases hc : execFullForestA a cf.1 with
            | some a' => simp only [Option.getD_some]
                         exact Dregg2.Exec.execFullForestA_nullifiers_grow a a' cf.1 hc h
            | none    => simp only [Option.getD_none]; exact h
          shape := .membership } : KernelForest.Contract))

/-! ## §2 — `conservation% a` — "asset `a`'s supply never drifts from its starting value".

The per-asset conservation shape (`HATCHERY.md §136, §146`): over a `ConservingForest` (per-asset net
delta `0` in every asset) the combined per-asset measure `cellObsA · a = recTotalAsset ·
.kernel a` is INVARIANT. `conservation% a` is parametric in a baseline state `s0`: it expands to the
contract `Inv s := cellObsA s a = cellObsA s0 a` (`shape := .constant`). The `step_ob` is the proved
one-step `cellObsA_next` (commit conserves EVERY asset — `execFullForestA_conserves_per_asset`
discharged by the conserving subtype's `∀ b, Δ = 0`; stay-put trivial), specialized to asset `a` by
`congrFun`. The supply generators (mint/burn) are the disclosed boundary, EXCLUDED from
`ConservingForest` — so this is the genuine *"no hidden inflation"* invariant, per asset. -/

/-- **`conservation% a`** — the per-asset conservation contract (parametric in the baseline `s0`):
`cellObsA · a = cellObsA s0 a`, carried by `cellObsA_next`. Produces a real `CellContract`
(`shape := .constant`); `.forever` gives *"asset `a`'s total supply never drifts, ever"*. Note the
expansion mentions the baseline `s0` (bind it at the use site, e.g. `conservation% (0 : AssetId)`
applied with `s0 := fma0`). -/
syntax (name := conservationStx) "conservation% " term:max : term

macro_rules
  | `(conservation% $a:term) =>
    `((fun (s0 : RecChainedState) =>
        ({  Inv := fun s => cellObsA s $a = cellObsA s0 $a
            step_ob := fun a' cf h => by
              show cellObsA (cellNextA a' cf) $a = cellObsA s0 $a
              rw [congrFun (cellObsA_next a' cf) $a]; exact h
            shape := .constant } : KernelForest.Contract)))

/-! ## §3 — `confinement% U` — "authority never exceeds the ceiling `U`".

The capability-confinement shape (`HATCHERY.md §137, §148`) — the seL4 `PasRefined` object-integrity
upper bound (`Exec/CellConfine.lean`). `confinement% U` expands to a FUNCTION `Auth.control ∈ U →
CellContract`: the carry needs `control ∈ U` (every connectivity grant confers `[control]`, which must
lie under the ceiling), so the macro surfaces that hypothesis EXPLICITLY rather than baking it in
(honest by construction). Applied to a proof `hctrl : Auth.control ∈ U` it yields the contract
`Inv s := CapsConfined U s.kernel.caps` (`shape := .other` — the confinement shape is its own
category) whose `step_ob` is the proved `cellNextA_confine hctrl` (commit: the forest confinement
lemma routes every cap-writing effect — grant/attenuate/revoke — under `U`; reject: caps unchanged).
`.forever` then gives *"caps stay confined by `U` at every index, every schedule"* — capability safety,
forever, the seL4 shape. -/

/-- **`confinement% U`** — the authority-confinement shape: expands to `(control ∈ U) →
CellContract`, the contract being `KConfined U ·.kernel` carried by `cellNextA_kconfine`. F3
STRENGTHENING: the sealed-box channel is DISSOLVED (caps-in-slots, `Apps/CapSlotFactory.lean`), so
the ceiling needs ONLY `control` — the old `grant`/`reply` hypotheses (the seal-pair caps) are GONE
and the contract is strictly stronger. Apply to a proof to get a real `CellContract`. -/
syntax (name := confinementStx) "confinement% " term:max : term

macro_rules
  | `(confinement% $U:term) =>
    `((fun (h : Auth.control ∈ $U) =>
        ({  Inv := fun s => KConfined $U s.kernel
            step_ob := fun a cf hf => cellNextA_kconfine h a cf hf
            shape := .other } : KernelForest.Contract)))

/-! ## §4 — `automaton_inv% a b` — a field-RELATIONAL invariant (linear field algebra).

The field-relational shape (`HATCHERY.md §138, §149`: *"a relation among fields … discharged by
`exec_frame` + `omega`/field algebra"*). The Subscription headline `seq_tail ≤ seq_head` is the
archetype on a self-contained automaton; on the REAL kernel state the analogous *linear relation among
two fields* is the COMBINED two-asset supply: `cellObsA s a + cellObsA s b` is conserved (a single
linear equation relating two ledger columns). It is relational — it constrains a sum of two
distinct fields, NOT either field alone (`obs a = 105`, `obs b = 7`, but the carried datum is their sum
`112`).

`automaton_inv% a b` is parametric in the baseline `s0`: it expands to `Inv s := cellObsA s a +
cellObsA s b = cellObsA s0 a + cellObsA s0 b` (`shape := .other`). The `step_ob` is `exec_frame`-style
(the executor commit/stay-put split), with the commit arm closed by FIELD ALGEBRA: the per-asset
`cellObsA_next` gives `obs(next) a = obs(s) a` AND `obs(next) b = obs(s) b`, and `omega` combines the
two equalities with the baseline. Demonstrates the `automaton_inv%` discharge route (`exec_frame` +
`omega`) on a non-trivial linear relation the per-asset *scalar* invariants cannot state. -/

/-- **`automaton_inv% a b`** — a linear two-field relational invariant (parametric in baseline `s0`):
the combined supply `cellObsA · a + cellObsA · b` is conserved, discharged by `cellObsA_next` ×2 +
`omega`. Produces a real `CellContract` (`shape := .other`); `.forever` gives *"the combined two-asset
supply never drifts"*. The canonical `automaton_inv%` instance: a relation among fields closed by field
algebra, the kernel-state analogue of Subscription's `tail ≤ head`. -/
syntax (name := automatonInvStx) "automaton_inv% " term:max ppSpace term:max : term

macro_rules
  | `(automaton_inv% $a:term $b:term) =>
    `((fun (s0 : RecChainedState) =>
        ({  Inv := fun s => cellObsA s $a + cellObsA s $b = cellObsA s0 $a + cellObsA s0 $b
            step_ob := fun a' cf h => by
              show cellObsA (cellNextA a' cf) $a + cellObsA (cellNextA a' cf) $b
                 = cellObsA s0 $a + cellObsA s0 $b
              have ha : cellObsA (cellNextA a' cf) $a = cellObsA a' $a := congrFun (cellObsA_next a' cf) $a
              have hb : cellObsA (cellNextA a' cf) $b = cellObsA a' $b := congrFun (cellObsA_next a' cf) $b
              omega
            shape := .other } : KernelForest.Contract)))

/-! ## §4b — `affine_rel% terms cmp` / `affine_le% terms` — the general affine-relation shape.

`automaton_inv% a b` conserves the UNIT-coefficient two-column sum `cellObsA · a + cellObsA · b`. But
`cellObsA_next` equates the WHOLE observation vector across a step, so ANY affine functional
`Σ cᵢ · cellObsA · aᵢ` — arbitrary coefficients, arbitrarily many columns — is equal across a step, and
hence ANY comparison `cmp (functional s) (functional s0)` against a fixed baseline is preserved for
`cmp ∈ {=, ≤, ≥, …}`. `affine_rel% terms cmp` / `affine_le% terms` (and `affine_ge%`, `affine_eq%`)
expand to the PRODUCTION `Contract` `affineRel terms cmp`, awaiting the baseline `s0` (mirroring how
`conservation%`/`automaton_inv%` surface `s0`). This is a STRICT generalization of §4:
`automaton_inv% a b` is `affine_eq% [(1, a), (1, b)]`, and the reserve/exposure ceiling
`Σ exposure ≤ reserve` (design doc Theorem 13) is `affine_le%` on the signed exposure/reserve terms. -/

/-- **`affine_rel% terms cmp`** — the general affine-relation contract (production), parametric in the
baseline `s0`: the affine functional `Σ cᵢ · cellObsA · aᵢ` (`terms : List (ℤ × AssetId)`) compared to
its `s0` value by `cmp ∈ {=, ≤, ≥, …}`. Expands to `fun s0 => affineRel terms cmp s0`. -/
syntax (name := affineRelStx) "affine_rel% " term:max ppSpace term:max : term
/-- **`affine_le% terms`** — the reserve/exposure ceiling shape: `Σ cᵢ · cellObsA · aᵢ ≤` its baseline. -/
syntax (name := affineLeStx) "affine_le% " term:max : term
/-- **`affine_ge% terms`** — the floor shape: `Σ cᵢ · cellObsA · aᵢ ≥` its baseline. -/
syntax (name := affineGeStx) "affine_ge% " term:max : term
/-- **`affine_eq% terms`** — the multi-column conservation shape (generalizes `automaton_inv%`). -/
syntax (name := affineEqStx) "affine_eq% " term:max : term

macro_rules
  | `(affine_rel% $terms:term $cmp:term) =>
    `((fun (s0 : RecChainedState) => affineRel $terms $cmp s0))
  | `(affine_le% $terms:term) =>
    `((fun (s0 : RecChainedState) => affineRel $terms (· ≤ ·) s0))
  | `(affine_ge% $terms:term) =>
    `((fun (s0 : RecChainedState) => affineRel $terms (· ≥ ·) s0))
  | `(affine_eq% $terms:term) =>
    `((fun (s0 : RecChainedState) => affineRel $terms (· = ·) s0))

/-! ## §5 — THE GATE: each macro elaborates to a BUILDING `CellContract` at its canonical field.

These `def`s/`example`s force elaboration of each macro and show the contract is real (its `.forever`
delivers the unbounded-time carry). The headline: `monotone_registry% revoked` reproduces the shipped
`Apps.Identity.livingCellA_identity_revoked_forever` as a single `.forever` call. -/

/-- **GATE (1) — `monotone_registry% revoked` builds.** The contract at the revocation registry. -/
noncomputable def gateRevoked (credNul : Nat) : Production.Contract :=
  liftFromKernelForest (monotone_registry% revoked credNul)

/-- **GATE (1, headline) — `monotone_registry% revoked` reproduces the Identity crown as a ONE-LINER.**
`Apps.Identity.livingCellA_identity_revoked_forever`'s statement — *a revoked credential stays revoked
at every index of every adversarial trajectory* — delivered by `(monotone_registry% revoked
credNul).forever`. No hand proof: the macro built the `CellContract`, `.forever` is the free payoff.
THIS is the Tier-4 promise — a verified "revoked ⇒ revoked forever" theorem from a single declaration. -/
example (credNul : Nat) (s : RecChainedState) (hinit : credNul ∈ s.kernel.revoked) (sched : SchedA) :
    ∀ n, credNul ∈ (trajA s sched n).kernel.revoked :=
  (monotone_registry% revoked credNul).forever hinit sched

/-- …and `.always` lifts the SAME one-liner into the LTL `□` modality. -/
example (credNul : Nat) (s : RecChainedState) (hinit : credNul ∈ s.kernel.revoked) (sched : SchedA) :
    Always (fun s' => credNul ∈ s'.kernel.revoked) s sched :=
  KernelForest.always (monotone_registry% revoked credNul) hinit sched

/-- **GATE (1′) — `monotone_registry% commitments` builds + reproduces commitment-persistence.** -/
example (c : Nat) (s : RecChainedState) (hinit : c ∈ s.kernel.commitments) (sched : SchedA) :
    ∀ n, c ∈ (trajA s sched n).kernel.commitments :=
  (monotone_registry% commitments c).forever hinit sched

/-- **GATE (1″) — `monotone_registry% nullifiers` builds + reproduces no-double-spend.** -/
example (n : Nat) (s : RecChainedState) (hinit : n ∈ s.kernel.nullifiers) (sched : SchedA) :
    ∀ m, n ∈ (trajA s sched m).kernel.nullifiers :=
  (monotone_registry% nullifiers n).forever hinit sched

/-- **GATE (2) — `conservation% 0` builds.** The per-asset conservation contract at asset `0`,
baseline `fma0`. -/
noncomputable def gateConserved : Production.Contract :=
  liftFromKernelForest ((conservation% (0 : AssetId)) fma0)

/-- **GATE (2, payoff) — `conservation% 0` reproduces `CellReal.livingCellA_obs_invariant` (asset 0).**
*Asset 0's total supply never drifts from its starting value, at every index of every trajectory.* -/
example (sched : SchedA) :
    ∀ n, cellObsA (trajA fma0 sched n) 0 = cellObsA fma0 0 :=
  ((conservation% (0 : AssetId)) fma0).forever rfl sched

/-- **GATE (3) — `confinement% fullAuthCeiling` builds.** The capability-confinement contract under the
full authority ceiling (which contains `control`, supplied by `by decide`). -/
noncomputable def gateConfined : Production.Contract :=
  liftFromKernelForest ((confinement% fullAuthCeiling) (by decide))

/-- **GATE (3, payoff) — `confinement%` reproduces `CellConfine.livingCellA_confinement`.** `KConfined`
(the c-list ceiling — F3: the ONLY kernel cap surface) stays confined at every index of every
adversarial trajectory — capability safety, forever, under the `control`-only ceiling (STRONGER). -/
example (s : RecChainedState) (hinit : KConfined fullAuthCeiling s.kernel) (sched : SchedA) :
    ∀ n, KConfined fullAuthCeiling (trajA s sched n).kernel :=
  ((confinement% fullAuthCeiling) (by decide)).forever hinit sched

/-- **GATE (4) — `automaton_inv% 0 1` builds.** The combined two-asset supply relational invariant,
baseline `fma0`. -/
noncomputable def gateAutomaton : Production.Contract :=
  liftFromKernelForest ((automaton_inv% (0 : AssetId) (1 : AssetId)) fma0)

/-- **GATE (4, payoff) — `automaton_inv% 0 1`: the combined `asset0 + asset1` supply is conserved
forever.** A linear relation among two ledger fields, carried at every index of every trajectory. -/
example (sched : SchedA) :
    ∀ n, cellObsA (trajA fma0 sched n) 0 + cellObsA (trajA fma0 sched n) 1
       = cellObsA fma0 0 + cellObsA fma0 1 :=
  ((automaton_inv% (0 : AssetId) (1 : AssetId)) fma0).forever rfl sched

/-- **GATE (4b) — `affine_le%` builds.** A 2-term signed affine `≤`-ceiling contract, baseline `fma0`:
`2·obs 0 + 3·obs 1 ≤` its baseline value. The functional is `affineObs_next`-invariant, so `≤` against
its own baseline holds forever — the `Σ exposure ≤ reserve` shape (design doc Theorem 13). -/
noncomputable def gateAffineLe : Production.Contract :=
  (affine_le% [((2 : ℤ), (0 : AssetId)), ((3 : ℤ), (1 : AssetId))]) fma0

/-- **GATE (4b, payoff) — the reserve/exposure `≤` invariant carried forever on `trajG`.** The affine
functional `2·obs 0 + 3·obs 1` never rises above its baseline value at every index of every trajectory
— a `Σ exposure ≤ reserve` reserve ceiling as a one-liner `.forever`. -/
example (sched : SchedG) :
    ∀ n, KernelForest.affineObs [((2 : ℤ), (0 : AssetId)), ((3 : ℤ), (1 : AssetId))] (trajG fma0 sched n)
       ≤ KernelForest.affineObs [((2 : ℤ), (0 : AssetId)), ((3 : ℤ), (1 : AssetId))] fma0 :=
  ((affine_le% [((2 : ℤ), (0 : AssetId)), ((3 : ℤ), (1 : AssetId))]) fma0).forever (le_refl _) sched

/-- **GATE (4b′) — the `≥` floor variant builds + carries forever** (same functional, `affine_ge%`). -/
example (sched : SchedG) :
    ∀ n, KernelForest.affineObs [((2 : ℤ), (0 : AssetId)), ((3 : ℤ), (1 : AssetId))] (trajG fma0 sched n)
       ≥ KernelForest.affineObs [((2 : ℤ), (0 : AssetId)), ((3 : ℤ), (1 : AssetId))] fma0 :=
  ((affine_ge% [((2 : ℤ), (0 : AssetId)), ((3 : ℤ), (1 : AssetId))]) fma0).forever (le_refl _) sched

/-- **GATE (4b″) — the `=` variant reproduces multi-column conservation** (`affine_eq%`, generalizing
`automaton_inv%` to arbitrary coefficients: here `2·obs 0 + 3·obs 1`). -/
example (sched : SchedG) :
    ∀ n, KernelForest.affineObs [((2 : ℤ), (0 : AssetId)), ((3 : ℤ), (1 : AssetId))] (trajG fma0 sched n)
       = KernelForest.affineObs [((2 : ℤ), (0 : AssetId)), ((3 : ℤ), (1 : AssetId))] fma0 :=
  ((affine_eq% [((2 : ℤ), (0 : AssetId)), ((3 : ℤ), (1 : AssetId))]) fma0).forever rfl sched

/-! ## §5b — Production payoffs (`trajG` / `SchedG`): the **public Hatchery API**.

Customers ship against `CellExecutor.production` / `trajG` / `SchedG`. §5 below is kernel-side macro
elaboration regression (`trajA`); treat it as internal QA, not the product surface. -/

example (credNul : Nat) (s : RecChainedState) (hinit : credNul ∈ s.kernel.revoked) (sched : SchedG) :
    ∀ n, credNul ∈ (trajG s sched n).kernel.revoked :=
  (gateRevoked credNul).forever hinit sched

example (sched : SchedG) :
    ∀ n, cellObsA (trajG fma0 sched n) 0 = cellObsA fma0 0 :=
  gateConserved.forever rfl sched

example (s : RecChainedState) (hinit : KConfined fullAuthCeiling s.kernel) (sched : SchedG) :
    ∀ n, KConfined fullAuthCeiling (trajG s sched n).kernel :=
  gateConfined.forever hinit sched

example (sched : SchedG) :
    ∀ n, cellObsA (trajG fma0 sched n) 0 + cellObsA (trajG fma0 sched n) 1
       = cellObsA fma0 0 + cellObsA fma0 1 :=
  gateAutomaton.forever rfl sched

example : EventuallyG gatedLogGoal fma0 logBumpSched :=
  gated_log_eventually

example : EventuallyG Pgoal fma0 transferSchedG :=
  gated_transfer_eventually

syntax (name := eventuallyStx) "eventually% " term:max : term

macro_rules
  | `(eventually% gatedLogGoal) =>
    `(gatedLogContract)
  | `(eventually% Pgoal) =>
    `(refundDemoContract)
  | `(eventually% $goal:term) =>
    `(({ Goal := $goal } : LivenessContract))

noncomputable def eventuallyDischargeGatedLog : EventuallyG gatedLogGoal fma0 logBumpSched :=
  gated_log_eventually

noncomputable def eventuallyDischargeTransfer : EventuallyG Pgoal fma0 transferSchedG :=
  gated_transfer_eventually

/-! ## §6 — Non-vacuity guards — the macro contracts are substantive; the tags vary.

The macro-built contracts carry quantities that GENUINELY MOVE / discriminate (not `x = x`):
* `monotone_registry%` — a real revoked id `42` is present (`true`) while `99` is absent (`false`):
  the registry has TEETH, so `42 ∈ revoked` is a non-trivial fact (`Apps/Identity.lean`'s witness).
* `conservation%` — asset 0's supply is `105`, conserved across a real transfer; the bound is a
  genuine moving quantity (a transfer redistributes `bal` while holding the TOTAL).
* `automaton_inv%` — the combined `obs 0 + obs 1 = 105 + 7 = 112` is RELATIONAL: it differs from
  either field alone (`105`, `7`), so the carried datum combines two fields (not a constant
  re-statement of one).
And the four macros emit three distinct `SafetyShape`s (`.membership`, `.constant`, `.other`). -/

#guard (Dregg2.Apps.Identity.fmaRevoked.kernel.revoked.contains 42)
#guard (Dregg2.Apps.Identity.fmaRevoked.kernel.revoked.contains 99 == false)
#guard (cellObsA fma0 0 == 105)
#guard ((execFullForestA fma0 transferCF.1).map
          (fun s' => decide (cellObsA s' 0 = cellObsA fma0 0)) == some true)
#guard (cellObsA fma0 0 + cellObsA fma0 1 == 112)
#guard (cellObsA fma0 0 + cellObsA fma0 1 ≠ cellObsA fma0 0)
#guard (cellObsA fma0 0 + cellObsA fma0 1 ≠ cellObsA fma0 1)
#guard ((execFullForestA fma0 transferCF.1).map
          (fun s' => decide (cellObsA s' 0 + cellObsA s' 1 = cellObsA fma0 0 + cellObsA fma0 1)) == some true)
#guard ((monotone_registry% revoked 42).shape == SafetyShape.membership)
#guard (((conservation% (0 : AssetId)) fma0).shape == SafetyShape.constant)
#guard (((automaton_inv% (0 : AssetId) (1 : AssetId)) fma0).shape == SafetyShape.other)
#guard ((monotone_registry% revoked 42).shape ≠ ((conservation% (0 : AssetId)) fma0).shape)
-- `affine_le%`: the 2-term functional `2·obs 0 + 3·obs 1 = 2·105 + 3·7 = 231` is a genuine moving
-- combination; a real transfer step preserves it, so `≤`, `≥`, `=` against the baseline all decide `true`.
#guard (KernelForest.affineObs [((2 : ℤ), (0 : AssetId)), ((3 : ℤ), (1 : AssetId))] fma0 == 231)
#guard ((execFullForestA fma0 transferCF.1).map (fun s' => decide
          (KernelForest.affineObs [((2 : ℤ), (0 : AssetId)), ((3 : ℤ), (1 : AssetId))] s'
            ≤ KernelForest.affineObs [((2 : ℤ), (0 : AssetId)), ((3 : ℤ), (1 : AssetId))] fma0)) == some true)
#guard ((execFullForestA fma0 transferCF.1).map (fun s' => decide
          (KernelForest.affineObs [((2 : ℤ), (0 : AssetId)), ((3 : ℤ), (1 : AssetId))] s'
            ≥ KernelForest.affineObs [((2 : ℤ), (0 : AssetId)), ((3 : ℤ), (1 : AssetId))] fma0)) == some true)
#guard ((execFullForestA fma0 transferCF.1).map (fun s' => decide
          (KernelForest.affineObs [((2 : ℤ), (0 : AssetId)), ((3 : ℤ), (1 : AssetId))] s'
            = KernelForest.affineObs [((2 : ℤ), (0 : AssetId)), ((3 : ℤ), (1 : AssetId))] fma0)) == some true)
#guard ((KernelForest.affineRelKF [((1 : ℤ), (0 : AssetId))] (· ≤ ·) fma0).shape == SafetyShape.other)
example : (eventually% gatedLogGoal).Goal = gatedLogGoal := rfl

/-! ## §7 — Axiom hygiene — the macro-emitted contracts + their payoff, kernel-triple clean.

`#assert_axioms` on each GATE `def` pins the macro-EMITTED `CellContract` (Inv + the tactic-discharged
`step_ob`) to `{propext, Classical.choice, Quot.sound}` — certifying the catalog macros produce
ordinary kernel-checked terms. -/

#assert_axioms gateRevoked
#assert_axioms gateConserved
#assert_axioms gateConfined
#assert_axioms gateAutomaton
#assert_axioms gateAffineLe

end Dregg2.Verify
