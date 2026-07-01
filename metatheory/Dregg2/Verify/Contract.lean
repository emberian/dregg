/-
# Dregg2.Verify.Contract — the Hatchery's CONTRACT object (HATCHERY.md Tier 3).

Tiers 1+2 (`Verify/Tactics.lean`, `Verify/Frames.lean`) built the Hatchery ENGINE: the
boilerplate-killing tactics (`carry_forever` / `exec_frame`) and the reusable forest-monotone
combinator (`cellNextA_carries_rel` / `livingCellA_carries_rel`) that collapse the hand-typed
`livingCellA_carries` skeleton every shipped crown re-proves. This module is Tier 3: it packages a
verified app invariant into a FIRST-CLASS OBJECT — a `CellContract` — so a crown becomes a *value*
you can name, store, render, and re-use, not a bespoke theorem buried in an app file.

## What a `CellContract` IS (and why it is the right object)

A `CellContract` bundles the EXACT pair the Hatchery's parametric crown
(`Exec.livingCellA_carries`, `Exec/CellCarry.lean:57`) consumes:

* `Inv : RecChainedState → Prop` — a state predicate on the REAL 46-effect kernel state, and
* `step_ob : ∀ s cf, Inv s → Inv (cellNextA s cf)` — the app's ONE real obligation: that a single
  living-cell step (`cellNextA`, the commit-on-`some` / stay-put-on-`none` real executor step,
  `Exec/CellReal.lean:41`) preserves `Inv`.

That is *all* an app author must supply. `CellContract.forever` then hands back the unbounded-time,
EVERY-schedule carry `∀ n, Inv (trajA s sched n)` for FREE, by feeding `(Inv, step_ob)` straight to
`livingCellA_carries`. `CellContract.always` lifts the SAME contract into the LTL `□` modality of
`Proof/Temporal.lean` (`Always Inv s sched`) via `always_of_step_invariant` — so a contract is
*simultaneously* a forever-trajectory invariant and a temporal-logic `□`-formula, with no extra proof.

The `shape : SafetyShape` field is a REAL, used tag — not decoration: it classifies the safety
property (grow-only `monotone`, set-`membership` persistence, `constant` observation, or `other`) for
the downstream proof-badge / contract-card widget (`Dregg2/Widget/ContractView.lean`, which renders a
card *by category*) and for the §-eval demonstration that the three shipped instances carry GENUINELY
DISTINCT shapes (`logAppendOnly = monotone`, `conserved = constant`, `revokedPersists = membership` —
`#guard`-distinguished below). It gates nothing in the proofs; the proofs stand on `Inv`/`step_ob`.

## What this is NOT

A `CellContract` carries a SINGLE state-predicate invariant along the living cell's `trajA`. It is
NOT a Hoare/WP `{P} cf {Q}` over an arbitrary forest (that is `Proof/WP.lean`'s direction, and is not
yet lifted to the forest executor), NOT a branching/bisimulation property (`CoinductiveAdversary`),
and NOT a liveness/fairness statement (`◇`-progress needs a fairness hypothesis on `SchedA`). It is
exactly the reusable, first-class form of the SAFETY (`□`) crowns the Hatchery mechanizes.

Every keystone (`CellContract.forever`,
`CellContract.always`, the three concrete contracts) is `#assert_axioms`-pinned to the kernel triple
`{propext, Classical.choice, Quot.sound}` at the foot of the file.
-/
import Dregg2.Verify.Tactics
import Dregg2.Exec.CellExecutor
import Dregg2.Proof.Temporal
import Dregg2.Apps.NameService
import Dregg2.Apps.Subscription

namespace Dregg2.Verify

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (fma0)
open Dregg2.Exec.FullForest
open Dregg2.Proof.Temporal (Always always_of_step_invariant)

/-! ## §1 — `SafetyShape`: the (real, used) classification tag for the contract card. -/

/-- **`SafetyShape`** — the qualitative shape of a carried safety property. A REAL tag: it is the
category the downstream contract-card widget (`Widget/ContractView.lean`) renders by, and it carries
distinct information across the shipped instances (`#guard`-distinguished in §4). It gates
NOTHING in the proofs — `CellContract`'s force is entirely in `Inv`/`step_ob` — but it is not
decorative either: it is consumed by the widget layer and by the non-triviality demonstration.

* `monotone`   — a grow-only field (append-only log, grow-only registry): `base R proj`, `R` reflexive-
  transitive, the field only moves forward (e.g. `logAppendOnly`, the registry-grow crowns).
* `membership` — a set-membership persistence (`x ∈ field` stays true): the OS revocation
  root-of-trust shape (`revokedPersists`).
* `constant`   — an observation never drifts (`obs · = obs s`): the per-asset conservation badge
  (`conserved`).
* `other`      — any other state-predicate safety. -/
inductive SafetyShape
  | monotone
  | membership
  | constant
  | other
  deriving DecidableEq, Repr

/-! ## §2 — `CellContract`: the first-class verified-invariant object. -/

/-- **`CellContract E`** — a verified app invariant on executor `E`, packaged as a value. -/
structure CellContract (E : CellExecutor) where
  Inv : RecChainedState → Prop
  step_ob : ∀ s c, Inv s → Inv (E.next s c)
  shape : SafetyShape := .other

/-- Lift a contract along a one-step preservation implication. -/
def CellContract.lift {E E' : CellExecutor} (C : CellContract E)
    (lift_pres : ∀ s c, C.Inv s → C.Inv (E'.next s c)) : CellContract E' where
  Inv := C.Inv
  step_ob := lift_pres
  shape := C.shape

namespace CellContract

/-- Conjunction of two contracts on the same executor: both invariants hold at every step. -/
def and {E : CellExecutor} (C₁ C₂ : CellContract E) : CellContract E where
  Inv s := C₁.Inv s ∧ C₂.Inv s
  step_ob s c h := And.intro (C₁.step_ob s c h.1) (C₂.step_ob s c h.2)
  shape := .other

/-- **`composeContracts`** — the composability hook: contract conjunction as a named combinator.
Apps compose by intersecting invariants; `.forever` on the composed contract carries BOTH along
`trajG` (or any `CellCarries` executor) with a single initial hypothesis pair. -/
def composeContracts {E : CellExecutor} (C₁ C₂ : CellContract E) : CellContract E :=
  and C₁ C₂

/-- Forever carry — parametric over any `CellExecutor` with a `CellCarries` instance. -/
theorem forever {E : CellExecutor} [CellCarries E] (C : CellContract E) {s : RecChainedState}
    (h : C.Inv s) (sched : E.TurnSched) :
    ∀ n, C.Inv (E.traj s sched n) :=
  CellCarries.carries C.Inv C.step_ob s h sched

/-- Composed forever carry — both conjuncts hold at every trajectory index. -/
theorem forever_compose {E : CellExecutor} [CellCarries E] (C₁ C₂ : CellContract E)
    {s : RecChainedState} (h₁ : C₁.Inv s) (h₂ : C₂.Inv s) (sched : E.TurnSched) :
    ∀ n, C₁.Inv (E.traj s sched n) ∧ C₂.Inv (E.traj s sched n) :=
  (composeContracts C₁ C₂).forever (And.intro h₁ h₂) sched

end CellContract

export CellContract (and composeContracts forever_compose)

namespace Production

noncomputable abbrev Executor := CellExecutor.production
abbrev Sched := SchedG
abbrev Contract := CellContract Executor

theorem always (C : Contract) {s : RecChainedState} (h : C.Inv s) (sched : Sched) :
    AlwaysG C.Inv s sched :=
  alwaysG_of_step_invariant C.Inv C.step_ob s h sched

/-- Lift a kernel-forest contract to production via the commit-path erasure bridge. -/
noncomputable def liftFromKernelForest (C : CellContract CellExecutor.kernelForest) : Contract :=
  C.lift fun s cg h =>
    CellExecutor.production_erases_kernelForest C.Inv
      (fun s' cf h' => by simpa [CellExecutor.kernelForest_next_eq] using C.step_ob s' cf h') s cg h

end Production

/-! Internal: contracts whose `step_ob` is discharged on the auth-stripped kernel forest.
Used only by catalog macro elaboration and the Regression suite's bidirectional witnesses against
legacy `trajA` crowns — NOT the public Hatchery API. -/

namespace KernelForest

noncomputable abbrev Executor := CellExecutor.kernelForest
abbrev Sched := SchedA
abbrev Contract := CellContract Executor

theorem always (C : Contract) {s : RecChainedState} (h : C.Inv s) (sched : Sched) :
    Always C.Inv s sched :=
  always_of_step_invariant C.Inv
    (fun a cf h' => by simpa [CellExecutor.kernelForest_next_eq] using C.step_ob a cf h')
    s h sched

def logAppendOnly (s0 : RecChainedState) : Contract where
  Inv s := s0.log.length ≤ s.log.length
  step_ob s cf h := by
    rw [CellExecutor.kernelForest_next_eq]
    simp only [cellNextA]
    rcases hc : execFullForestA s cf.1 with _ | s'
    · simp only [Option.getD_none]; exact h
    · simp only [Option.getD_some]
      exact le_trans h (execFullForestA_logMono s s' cf.1 hc)
  shape := .monotone

def conserved (s0 : RecChainedState) : Contract where
  Inv s := cellObsA s = cellObsA s0
  step_ob a cf h := by
    rw [CellExecutor.kernelForest_next_eq, cellObsA_next]
    exact h
  shape := .constant

/-- Per-asset conservation (`conservation% a` shape, without importing `Catalog`). -/
def assetConservedKF (s0 : RecChainedState) (a : AssetId) : Contract where
  Inv s := cellObsA s a = cellObsA s0 a
  step_ob a' cf h := by
    rw [CellExecutor.kernelForest_next_eq]
    rw [congrFun (cellObsA_next a' cf) a]
    exact h
  shape := .constant

/-! ### Affine-relation contracts — the general `⋈ ∈ {=, ≤, ≥}` generalization of `assetConservedKF`.

`assetConservedKF` pins a SINGLE ledger column (`cellObsA · a = cellObsA s0 a`). But `cellObsA_next`
gives equality of the WHOLE per-asset observation vector across a living-cell step, so ANY affine
functional `Σ cᵢ · cellObsA · aᵢ` is equal across a step too. `affineRelKF` packages that: a list of
`(coefficient, asset)` terms defines the functional `affineObs`, and — because the functional is
step-invariant — a comparison `cmp (affineObs terms s) (affineObs terms s0)` against its FIXED baseline
value is preserved for ANY `cmp`. So `cmp := (· = ·)` recovers a multi-column conservation law,
`cmp := (· ≤ ·)` gives a reserve/exposure ceiling `Σ exposure ≤ reserve` as an instance
(design doc Theorem 13), and `cmp := (· ≥ ·)` a floor — all discharged by the SAME `affineObs_next`
rewrite. (This is strictly cleaner than the per-term `congrFun (cellObsA_next ..) aᵢ` + `omega` route of
`automaton_inv%`: since the WHOLE column vector is fixed across a step, the whole functional — hence the
whole comparison — is fixed, so the carried hypothesis discharges the step directly.) -/

/-- **`affineObs terms s`** — the affine functional `Σ (cᵢ · cellObsA s aᵢ)` over the tracked ledger
columns, `terms : List (coefficient × asset)`. `affineObs [(1, a)] s = cellObsA s a`; `affineObs
[(1, a), (1, b)] s = cellObsA s a + cellObsA s b` (the `automaton_inv%` two-field sum). -/
def affineObs (terms : List (ℤ × AssetId)) (s : RecChainedState) : ℤ :=
  (terms.map (fun p => p.1 * cellObsA s p.2)).sum

/-- One-step invariance of EVERY affine functional: `cellObsA_next` equates the whole observation
vector across a living-cell step, so any `Σ cᵢ · cellObsA · aᵢ` is equal across the step too. This is
the one lemma the affine-relation `step_ob` reuses (the `cellObsA_next` generalization of `congrFun`). -/
theorem affineObs_next (terms : List (ℤ × AssetId)) (s : RecChainedState) (cf : ConservingForest) :
    affineObs terms (cellNextA s cf) = affineObs terms s := by
  simp only [affineObs, cellObsA_next]

/-- **`affineRelKF terms cmp s0` — the general affine-relation contract** (the `⋈ ∈ {=, ≤, ≥}`
generalization). `Inv s := cmp (affineObs terms s) (affineObs terms s0)`: the affine functional at `s`,
compared against its fixed baseline value at `s0` by ANY relation `cmp`. `step_ob` rewrites the
functional across the step (`affineObs_next`), reducing the goal to the SAME comparison at the
predecessor — closed by the carried hypothesis, for every `cmp` uniformly. `assetConservedKF s0 a` is
the instance `affineRelKF [(1, a)] (· = ·) s0`; a reserve invariant `Σ exposure ≤ reserve` is
`affineRelKF signedTerms (· ≤ ·) s0`. -/
def affineRelKF (terms : List (ℤ × AssetId)) (cmp : ℤ → ℤ → Prop) (s0 : RecChainedState)
    (shape : SafetyShape := .other) : Contract where
  Inv s := cmp (affineObs terms s) (affineObs terms s0)
  step_ob a' cf h := by
    rw [CellExecutor.kernelForest_next_eq, affineObs_next]
    exact h
  shape := shape

def revokedPersists (x : Nat) : Contract where
  Inv s := x ∈ s.kernel.revoked
  step_ob a cf h := by
    rw [CellExecutor.kernelForest_next_eq]
    unfold cellNextA
    cases hc : execFullForestA a cf.1 with
    | some a' => simp only [Option.getD_some]
                 exact Dregg2.Apps.Identity.execFullForestA_revoked_grow a a' cf.1 hc h
    | none    => simp only [Option.getD_none]; exact h
  shape := .membership

def nullifierPersists (nf : Nat) : Contract where
  Inv s := nf ∈ s.kernel.nullifiers
  step_ob a cf h := by
    rw [CellExecutor.kernelForest_next_eq]
    unfold cellNextA
    cases hc : execFullForestA a cf.1 with
    | some a' => simp only [Option.getD_some]
                 exact (execFullForestA_nullifiers_grow a a' cf.1 hc) h
    | none    => simp only [Option.getD_none]; exact h
  shape := .membership

def nameRegisteredContract (name owner : Dregg2.Apps.NameService.Name) : Contract where
  Inv s := Dregg2.Apps.NameService.isRegistered s name owner = true
  step_ob a cf h := by
    rw [CellExecutor.kernelForest_next_eq]
    unfold cellNextA
    cases hc : execFullForestA a cf.1 with
    | some a' => simp only [Option.getD_some]
                 exact Dregg2.Apps.NameService.nameservice_step_preserves a a' cf.1 name owner hc h
    | none    => simp only [Option.getD_none]; exact h
  shape := .membership

-- F2b: `subWFContract` (the Subscription living-cell capacity invariant over the kernel `queues`
-- side-table) died with the queue verb family — the living-cell queue safety is the factory story
-- (`Apps/QueueFactory.lean` relational-caveat keystones).



/-- **`subsetNullifiersContract base` — the `⊆`-shaped grow-only nullifier contract.** -/
def subsetNullifiersContract (base : List Nat) : Contract where
  Inv s := base ⊆ s.kernel.nullifiers
  step_ob a cf h := by
    rw [CellExecutor.kernelForest_next_eq]
    unfold cellNextA
    cases hc : execFullForestA a cf.1 with
    | some a' => simp only [Option.getD_some]
                 exact List.Subset.trans h (execFullForestA_nullifiers_grow a a' cf.1 hc)
    | none    => simp only [Option.getD_none]; exact h
  shape := .membership

/-- **`subsetCommitmentsContract base` — the `⊆`-shaped grow-only commitment contract.** -/
def subsetCommitmentsContract (base : List Nat) : Contract where
  Inv s := base ⊆ s.kernel.commitments
  step_ob a cf h := by
    rw [CellExecutor.kernelForest_next_eq]
    unfold cellNextA
    cases hc : execFullForestA a cf.1 with
    | some a' => simp only [Option.getD_some]
                 exact List.Subset.trans h (execFullForestA_commitments_grow a a' cf.1 hc)
    | none    => simp only [Option.getD_none]; exact h
  shape := .membership

end KernelForest

open Production (Contract Sched liftFromKernelForest)

/-! ## §3 — Production contracts (lifted from kernel-forest proofs via erasure). -/

noncomputable def logAppendOnly (s0 : RecChainedState) : Contract :=
  liftFromKernelForest (KernelForest.logAppendOnly s0)

noncomputable def conserved (s0 : RecChainedState) : Contract :=
  liftFromKernelForest (KernelForest.conserved s0)

noncomputable def assetConserved (s0 : RecChainedState) (a : AssetId) : Contract :=
  liftFromKernelForest (KernelForest.assetConservedKF s0 a)

/-- **`affineRel terms cmp s0`** — the production lift of `KernelForest.affineRelKF`: an affine
functional `Σ cᵢ · cellObsA · aᵢ` compared to its baseline value at `s0` by `cmp ∈ {=, ≤, ≥, …}`,
carried along `trajG`. Strictly generalizes `assetConserved` (which is `affineRel [(1, a)] (· = ·) s0`)
to arbitrary linear combinations AND to the `≤`/`≥` reserve/exposure relations (design doc Theorem 13). -/
noncomputable def affineRel (terms : List (ℤ × AssetId)) (cmp : ℤ → ℤ → Prop) (s0 : RecChainedState)
    (shape : SafetyShape := .other) : Contract :=
  liftFromKernelForest (KernelForest.affineRelKF terms cmp s0 shape)

noncomputable def revokedPersists (x : Nat) : Contract :=
  liftFromKernelForest (KernelForest.revokedPersists x)

noncomputable def nullifierPersists (nf : Nat) : Contract :=
  liftFromKernelForest (KernelForest.nullifierPersists nf)

noncomputable def nameRegisteredContract (name owner : Dregg2.Apps.NameService.Name) : Contract :=
  liftFromKernelForest (KernelForest.nameRegisteredContract name owner)

-- F2b: the production `subWFContract` lift died with the kernel queue side-table (factory story).

noncomputable def subsetNullifiersContract (base : List Nat) : Contract :=
  liftFromKernelForest (KernelForest.subsetNullifiersContract base)

noncomputable def subsetCommitmentsContract (base : List Nat) : Contract :=
  liftFromKernelForest (KernelForest.subsetCommitmentsContract base)

/-! ## §3a — The three standing apps, re-expressed as first-class `CellContract`s (HATCHERY.md H3 gate).

`HATCHERY.md`'s H3 gate (`§202`) is *"the 3 apps re-expressed as `CellContract`s, same theorems"* — the
three shipped userspace cell-programs (`Apps/Identity.lean`, `Apps/NameService.lean`,
`Apps/Subscription.lean`), each a hand-written `livingCellA_carries` crown, recovered as a `CellContract`
whose `.forever` reproduces the crown VERBATIM. **Identity** is already covered: it is `revokedPersists`
(`x ∈ ·.kernel.revoked` — the revocation root-of-trust), with its reproduction example in §3′ below. The
other two carry app-specific invariants the bare shape catalog does NOT template (a `commitments.contains`
BOOLEAN; a `∀ q ∈ queues` capacity bound), so each is packaged here as a `CellContract` whose `step_ob`
is the APP'S OWN proved one-step lemma — Tier 3 absorbing an app invariant while still handing back
`forever` for free. NONE is faked: every `step_ob` is a real proof term over the shipped
`execFullForestA`. These two defs are the single source of truth; `Verify/Regression.lean §4–§5` reuses
them for the rigorous BOTH-DIRECTIONS defeq witness against the shipped crowns. -/

/-- **NameService — `.forever` on production trajectories.** The ascribed type IS the
shipped crown's type, so this example witnesses statement-level regression-equality (a registered binding
stays registered at every index of every trajectory), with NO hand temporal proof. -/
example (s : RecChainedState) (name owner : Dregg2.Apps.NameService.Name)
    (hinit : Dregg2.Apps.NameService.isRegistered s name owner = true) (sched : SchedG) :
    ∀ n, Dregg2.Apps.NameService.isRegistered (trajG s sched n) name owner = true :=
  (nameRegisteredContract name owner).forever hinit sched


/-! ## §3′ — Using a contract: `forever` / `always` are method calls, not re-proofs.

The contract's whole point. Naming a contract and calling `.forever` / `.always` reproduces — with
NO bespoke proof — the shipped hand crowns. These `example`s are build-checked regressions: the
contract object delivers the SAME forever / `□` statements as `CellCarry`, `CellReal`, `Identity`. -/

/-- A contract delivers the hand crown `Exec.livingCellA_logMono`'s statement via `.forever`. -/
example (s : RecChainedState) (sched : SchedG) :
    ∀ n, s.log.length ≤ (trajG s sched n).log.length :=
  (logAppendOnly s).forever (le_refl _) sched

example (s : RecChainedState) (sched : SchedG) :
    AlwaysG (fun s' => s.log.length ≤ s'.log.length) s sched :=
  Production.always (logAppendOnly s) (le_refl _) sched

example (s : RecChainedState) (sched : SchedG) :
    ∀ n, cellObsA (trajG s sched n) = cellObsA s :=
  (conserved s).forever rfl sched

example (x : Nat) (s : RecChainedState) (hinit : x ∈ s.kernel.revoked) (sched : SchedG) :
    ∀ n, x ∈ (trajG s sched n).kernel.revoked :=
  (revokedPersists x).forever hinit sched

/-- Named production crown for widgets / regression (the `revokedPersists` contract's `.forever`). -/
theorem identity_revoked_forever_production (x : Nat) (s : RecChainedState)
    (hinit : x ∈ s.kernel.revoked) (sched : SchedG) :
    ∀ n, x ∈ (trajG s sched n).kernel.revoked :=
  (revokedPersists x).forever hinit sched

theorem spent_note_never_respent_production (nf : Nat) (s : RecChainedState)
    (hinit : nf ∈ s.kernel.nullifiers) (sched : SchedG) :
    ∀ n, nf ∈ (trajG s sched n).kernel.nullifiers :=
  (nullifierPersists nf).forever hinit sched

theorem no_double_spend_production (nul0 : List Nat) (s : RecChainedState)
    (hinit : nul0 ⊆ s.kernel.nullifiers) (sched : SchedG) :
    ∀ n, nul0 ⊆ (trajG s sched n).kernel.nullifiers :=
  (subsetNullifiersContract nul0).forever hinit sched

theorem commitments_persist_production (com0 : List Nat) (s : RecChainedState)
    (hinit : com0 ⊆ s.kernel.commitments) (sched : SchedG) :
    ∀ n, com0 ⊆ (trajG s sched n).kernel.commitments :=
  (subsetCommitmentsContract com0).forever hinit sched

theorem nameservice_registration_forever_production (s : RecChainedState)
    (name owner : Dregg2.Apps.NameService.Name)
    (hinit : Dregg2.Apps.NameService.isRegistered s name owner = true) (sched : SchedG) :
    ∀ n, Dregg2.Apps.NameService.isRegistered (trajG s sched n) name owner = true :=
  (nameRegisteredContract name owner).forever hinit sched


theorem asset_conserved_forever_production (s0 : RecChainedState) (a : AssetId) (sched : SchedG) :
    ∀ n, cellObsA (trajG s0 sched n) a = cellObsA s0 a :=
  (assetConserved s0 a).forever rfl sched

/-- **`affine_le_forever_production` — the reserve/exposure `≤` crown (design doc Theorem 13).** A
signed affine functional `Σ cᵢ · cellObsA · aᵢ` stays `≤` its baseline value at every `trajG` index —
the `Σ exposure ≤ reserve` reserve invariant as a production crown. Since the functional is
step-invariant, `le_refl` at the baseline seeds the entire adversarial trajectory. -/
theorem affine_le_forever_production (terms : List (ℤ × AssetId)) (s0 : RecChainedState) (sched : SchedG) :
    ∀ n, KernelForest.affineObs terms (trajG s0 sched n) ≤ KernelForest.affineObs terms s0 :=
  (affineRel terms (· ≤ ·) s0).forever (le_refl _) sched

/-- **`affine_ge_forever_production`** — the mirror `≥` (floor) crown; same functional, opposite
comparator, same `affineObs_next` discharge (`≥`-reflexivity seeds it). -/
theorem affine_ge_forever_production (terms : List (ℤ × AssetId)) (s0 : RecChainedState) (sched : SchedG) :
    ∀ n, KernelForest.affineObs terms (trajG s0 sched n) ≥ KernelForest.affineObs terms s0 :=
  (affineRel terms (· ≥ ·) s0).forever (le_refl _) sched

theorem log_mono_forever_production (s : RecChainedState) (sched : SchedG) :
    ∀ n, s.log.length ≤ (trajG s sched n).log.length :=
  (logAppendOnly s).forever (le_refl _) sched

/-! ## §3b — Composability: contract conjunction + composed forever crowns.

`CellContract.composeContracts` intersects two verified invariants. The payoff is a SINGLE
`.forever` / production crown certifying BOTH properties along `trajG` — the Hatchery pattern for
multi-app / multi-shape assurance without re-proving the carry skeleton. -/

open CellContract (composeContracts forever_compose)

/-- **Identity revocation ∩ per-asset conservation** — the composed safety contract behind a gated
market whose payment supply must stay fixed while revoked credentials stay in the committed registry
(`Apps/IdentityGated` + `Apps/ComputeExchangeGated` headline shapes, packaged as one object). -/
noncomputable def revokedPaySafety (credNul : Nat) (s0 : RecChainedState) (payAsset : AssetId) : Contract :=
  composeContracts (revokedPersists credNul) (assetConserved s0 payAsset)

/-- **`revoked_pay_safety_forever` — COMPOSED PRODUCTION CROWN.** Revoked credentials persist in the
registry AND the payment asset's combined supply never drifts — one composed contract, one `.forever`. -/
theorem revoked_pay_safety_forever (credNul : Nat) (s0 : RecChainedState) (payAsset : AssetId)
    (s : RecChainedState) (hrev : credNul ∈ s.kernel.revoked)
    (hpay : cellObsA s payAsset = cellObsA s0 payAsset) (sched : SchedG) :
    ∀ n, credNul ∈ (trajG s sched n).kernel.revoked ∧
         cellObsA (trajG s sched n) payAsset = cellObsA s0 payAsset :=
  (revokedPaySafety credNul s0 payAsset).forever (And.intro hrev hpay) sched

/-- **Note-commitment persistence ∩ revocation persistence** — a composed-contract example over two
side-table shapes (replacing the F2b-retired subscription composition; same `composeContracts`
mechanism, both conjuncts real). -/
noncomputable def commitmentsAndRevoked (com0 : List Nat) (credNul : Nat) : Contract :=
  composeContracts (subsetCommitmentsContract com0) (revokedPersists credNul)

/-- **`commitments_and_revoked_forever` — COMPOSED PRODUCTION CROWN.** From an initially-held
commitment set AND an initially-revoked credential, BOTH invariants hold at every `trajG` index. -/
theorem commitments_and_revoked_forever (com0 : List Nat) (credNul : Nat) (s : RecChainedState)
    (hcom : com0 ⊆ s.kernel.commitments) (hrev : credNul ∈ s.kernel.revoked)
    (sched : SchedG) :
    ∀ n, com0 ⊆ (trajG s sched n).kernel.commitments ∧
         credNul ∈ (trajG s sched n).kernel.revoked :=
  (commitmentsAndRevoked com0 credNul).forever (And.intro hcom hrev) sched

/-! ## §4 — Non-vacuity guards — the contracts are substantive and the tag carries distinct info.

`logAppendOnly`'s `Inv` bounds a STRICTLY-GROWING quantity: a real committed transfer (`transferCF`,
actor 0 transfers 30 of asset 0 from cell 0 to cell 1) grows the audit log `0 → 1`, so the carried `≤`
is a bound on a quantity that moves — not a trivially-true `x = x`. And the three shipped
contracts carry three DISTINCT `SafetyShape`s, so the tag is real classifying data, not a constant. -/

#guard (fma0.log.length == 0)
#guard ((execFullForestA fma0 transferCF.1).map (fun s' => s'.log.length) == some 1)
#guard ((execFullForestA fma0 transferCF.1).map
          (fun s' => decide (fma0.log.length < s'.log.length)) == some true)
#guard ((execFullForestA fma0 transferCF.1).map
          (fun s' => decide (fma0.log.length ≤ s'.log.length)) == some true)
#guard ((KernelForest.logAppendOnly fma0).shape == SafetyShape.monotone)
#guard ((KernelForest.conserved fma0).shape == SafetyShape.constant)
#guard ((KernelForest.revokedPersists 42).shape == SafetyShape.membership)
#guard ((KernelForest.logAppendOnly fma0).shape ≠ (KernelForest.conserved fma0).shape)
#guard ((KernelForest.conserved fma0).shape ≠ (KernelForest.revokedPersists 42).shape)
#guard (Dregg2.Apps.NameService.isRegistered fma0
          Dregg2.Apps.NameService.aliceName Dregg2.Apps.NameService.aliceOwner == false)
#guard (Dregg2.Apps.NameService.afterRegister.map (fun s => Dregg2.Apps.NameService.isRegistered s
          Dregg2.Apps.NameService.aliceName Dregg2.Apps.NameService.aliceOwner) == some true)
#guard ((KernelForest.nameRegisteredContract Dregg2.Apps.NameService.aliceName
          Dregg2.Apps.NameService.aliceOwner).shape == SafetyShape.membership)

/-! ## §5 — Axiom hygiene — the contract object + its methods + the instances, kernel-triple clean. -/

#assert_axioms CellContract.and
#assert_axioms CellContract.composeContracts
#assert_axioms CellContract.forever
#assert_axioms CellContract.forever_compose
#assert_axioms Production.always
#assert_axioms Production.liftFromKernelForest
#assert_axioms logAppendOnly
#assert_axioms conserved
#assert_axioms KernelForest.affineObs_next
#assert_axioms KernelForest.affineRelKF
#assert_axioms affineRel
#assert_axioms affine_le_forever_production
#assert_axioms affine_ge_forever_production
#assert_axioms revokedPersists
#assert_axioms nullifierPersists
#assert_axioms nameRegisteredContract
#assert_axioms identity_revoked_forever_production
#assert_axioms spent_note_never_respent_production
#assert_axioms no_double_spend_production
#assert_axioms commitments_persist_production
#assert_axioms nameservice_registration_forever_production
#assert_axioms log_mono_forever_production
#assert_axioms revokedPaySafety
#assert_axioms revoked_pay_safety_forever
#assert_axioms commitmentsAndRevoked
#assert_axioms commitments_and_revoked_forever

end Dregg2.Verify
