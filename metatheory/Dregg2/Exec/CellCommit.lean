/-
# Dregg2.Exec.CellCommit — the COMMITMENT-PERSISTENCE crown: a published note commitment is never retracted.

`Exec/CellReal.lean` crowned the SHIPPED per-asset executor `execFullForestA` (the 46-effect, auth-gated
tree) with the coinductive **living cell** `livingCellA`, and `Exec/CellCarry.lean` distilled the
PARAMETRIC crown `livingCellA_carries`: ANY *state* predicate `Good` preserved by ONE living-cell step
holds along the ENTIRE unbounded adversarial trajectory `trajA`, under EVERY schedule. Conservation
(`livingCellA_obs_invariant'`) and the append-only audit log (`livingCellA_logMono`) are its first two
instances. This module adds the third headline of the **private-note layer**:

> **The note-commitment set is GROW-ONLY, FOREVER.** A commitment that has ever been published
> (`com0 ⊆ s.kernel.commitments`) is contained in `commitments` at EVERY index of the unbounded
> adversarial trajectory: it is never retracted, dropped, or rewritten. This is the **anti-equivocation /
> auditability** invariant of the off-ledger commitment tree — the grow-only DUAL of the nullifier set's
> no-double-spend (`META-FILL C`, closing `#121`) — now COINDUCTIVE on the real executor.

The proof is the same parametric shape as `livingCellA_logMono`, with the load-bearing per-step content
being a **registry frame lemma**: across ONE real `execFullA` step, `s.kernel.commitments` is *grown-only*
— `noteCreate` conses a fresh commitment onto it (`noteCreateCommitment`), and EVERY OTHER effect frames
it UNCHANGED (each kernel mutator is a `{ k with <non-commitments fields> := … }` structure update). So
`s.kernel.commitments ⊆ s'.kernel.commitments` for a committed `execFullA`, lifted to the forest and then
carried forever by `livingCellA_carries`.

Together with the nullifier-persistence crown this is the audit/anti-double-spend pair of the private-note
layer: the spent-set never loses a nullifier (no double-spend), the commitment-set never loses a
commitment (no equivocation) — both as `∀ n, Good (trajA …)` temporal νF invariants on the real machine.

Three theorems, ascending:
* **`execFullA_commitments_grow`** — the per-step registry frame: a committed `execFullA` step only GROWS
  `commitments` (`s.kernel.commitments ⊆ s'.kernel.commitments`), by case analysis on the 46-effect kind
  (noteCreate conses; all others frame). This is the executor-level content the crown stands on.
* **`execFullForestA_commitments_grow`** — the forest/turn lift: a committed full-FOREST only grows
  `commitments`, by induction on the lowered action list through the pre-order bridge.
* **`livingCellA_commitments_persist`** — THE CROWN: `com0 ⊆ s.kernel.commitments → ∀ n, com0 ⊆
  (trajA s sched n).kernel.commitments`. The grow-only set carried along the whole unbounded trajectory by
  `livingCellA_carries` with `Good := (com0 ⊆ ·.kernel.commitments)` — a NON-conservation safety,
  discharged from the registry frame on a commit + the stay-put self-loop on a reject.
-/
import Dregg2.Exec.CellCarry

namespace Dregg2.Exec

open Dregg2.Boundary
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Exec.EffectsState
open Dregg2.Authority
open Dregg2.Tactics

/-- **`subset_of_commitments_eq`** — a tiny bridge: when a step left the commitment set LITERALLY
unchanged (`k'.commitments = k.commitments`), the grow-only `⊆` holds by reflexivity. The uniform
closer the framing arms of `execFullA_commitments_grow` use (the non-`noteCreate` effects). -/
theorem subset_of_commitments_eq {k k' : RecordKernelState} (h : k'.commitments = k.commitments) :
    k.commitments ⊆ k'.commitments := by rw [h]

/-! ## Step 0 — per-mutator COMMITMENTS frames: each kernel mutator leaves `commitments` UNCHANGED.

Every `execFullA` arm's kernel mutator is a `{ k with <fields> := … }` structure update whose `<fields>`
NEVER includes `commitments` — except `noteCreateCommitment`, which conses onto it. We pin the "unchanged"
half here as tiny per-mutator frames (each: unfold, split the admissibility gate, `subst`, `rfl`), so the
master step lemma is a thin dispatch rather than 40 inline gate-peels. The `none` (rejected) branch is
discharged by the master lemma; these speak only to a committed `some k'`. -/

/-- Per-asset transfer leaves `commitments` unchanged (it edits only `bal`). -/
theorem recKExecAsset_commitments {k k' : RecordKernelState} {turn : Turn} {a : AssetId}
    (h : recKExecAsset k turn a = some k') : k'.commitments = k.commitments := by
  unfold recKExecAsset at h; split at h
  · obtain ⟨rfl⟩ := h; rfl
  · exact absurd h (by simp)

/-- Per-asset mint leaves `commitments` unchanged (edits only `bal`). -/
theorem recKMintAsset_commitments {k k' : RecordKernelState} {actor cell : CellId} {a : AssetId} {amt : ℤ}
    (h : recKMintAsset k actor cell a amt = some k') : k'.commitments = k.commitments := by
  unfold recKMintAsset at h; split at h
  · obtain ⟨rfl⟩ := h; rfl
  · exact absurd h (by simp)

/-- Per-asset burn leaves `commitments` unchanged (edits only `bal`). -/
theorem recKBurnAsset_commitments {k k' : RecordKernelState} {actor cell : CellId} {a : AssetId} {amt : ℤ}
    (h : recKBurnAsset k actor cell a amt = some k') : k'.commitments = k.commitments := by
  unfold recKBurnAsset at h; split at h
  · obtain ⟨rfl⟩ := h; rfl
  · exact absurd h (by simp)

/-- Delegate leaves `commitments` unchanged (edits only `caps`). -/
theorem recKDelegate_commitments {k k' : RecordKernelState} {del rec t : CellId}
    (h : recKDelegate k del rec t = some k') : k'.commitments = k.commitments := by
  unfold recKDelegate at h; split at h
  · obtain ⟨rfl⟩ := h; rfl
  · exact absurd h (by simp)

/-- Rights-carrying delegate leaves `commitments` unchanged (edits only `caps`). -/
theorem recKDelegateAtten_commitments {k k' : RecordKernelState} {del rec t : CellId} {keep : List Auth}
    (h : recKDelegateAtten k del rec t keep = some k') : k'.commitments = k.commitments := by
  unfold recKDelegateAtten at h; split at h
  · obtain ⟨rfl⟩ := h; rfl
  · exact absurd h (by simp)

/-- Target-revocation is total and leaves `commitments` unchanged (edits only `caps`). -/
theorem recKRevokeTarget_commitments (k : RecordKernelState) (holder t : CellId) :
    (recKRevokeTarget k holder t).commitments = k.commitments := rfl

/-- A field write leaves `commitments` unchanged (edits only `cell`). -/
theorem writeField_commitments (k : RecordKernelState) (f : FieldName) (target : CellId) (v : Value) :
    (writeField k f target v).commitments = k.commitments := rfl

/-- The make-sovereign rebind leaves `commitments` unchanged (edits only `cell`). -/
theorem makeSovereignKernel_commitments (k : RecordKernelState) (target : CellId) :
    (makeSovereignKernel k target).commitments = k.commitments := rfl

/-- A fresh-cell insert leaves `commitments` unchanged (edits only `accounts`/`bal`). -/
theorem createCellIntoAsset_commitments (k : RecordKernelState) (newCell : CellId) :
    (createCellIntoAsset k newCell).commitments = k.commitments := rfl

/-- Note-SPEND leaves `commitments` unchanged (grows `nullifiers`, the orthogonal set). -/
theorem noteSpendNullifier_commitments {k k' : RecordKernelState} {nf : Nat}
    (h : noteSpendNullifier k nf = some k') : k'.commitments = k.commitments := by
  unfold noteSpendNullifier at h; split at h
  · exact absurd h (by simp)
  · obtain ⟨rfl⟩ := h; rfl

-- (F2b: the queue-family `_commitments` frame helpers died with the queue verb family.)

/-! ## Step 1 — `execFullA_commitments_grow`: the PER-STEP registry frame (grow-only across one step). -/

mutual
/-- **`execFullA_commitments_grow` — THE per-step registry frame.** A committed real `execFullA`
step only GROWS the note-commitment set: `s.kernel.commitments ⊆ s'.kernel.commitments`. By case analysis
on the effect kind — `noteCreate` conses a fresh commitment (`noteCreateCommitment`, so the old set is a
sublist hence subset), and EVERY OTHER effect leaves `commitments` literally UNCHANGED (each via its
per-mutator frame above; the chained `stateStep`/`emit`/`attenuate`/`exercise`/`spawn`/`createCell`
wrappers edit `cell`/`caps`/`accounts`/`bal`/`escrows`/`queues`/`swiss`, never `commitments`); `exerciseA`
RECURSES (mutual `execInnerA_commitments_grow`). This is the META-FILL-C grow-only DUAL of the nullifier
registry, on the SHIPPED executor — the load-bearing one-step content of the commitment-persistence crown. -/
theorem execFullA_commitments_grow (s s' : RecChainedState) (fa : FullActionA)
    (h : execFullA s fa = some s') : s.kernel.commitments ⊆ s'.kernel.commitments := by
  -- A uniform "the kernel mutator left `commitments` fixed" closer for the framing arms:
  -- expose `s' = { kernel := k', … }`, rewrite `commitments` by the per-mutator frame, `subset_refl`.
  -- `exerciseA` RECURSES — its inner fold can only GROW the set (mutual `execInnerA_commitments_grow`).
  cases fa with
  | balanceA t a =>
      obtain ⟨_, ⟨k', hk, h'⟩⟩ := recCexecAsset_factors t a (by simpa only [execFullA] using h)
      subst h'; exact subset_of_commitments_eq (recKExecAsset_commitments hk)
  | delegate del rec t =>
      simp only [execFullA, recCDelegate] at h
      cases hk : recKDelegate s.kernel del rec t with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => commit_subst h hk; exact subset_of_commitments_eq (recKDelegate_commitments hk)
  | revoke holder t =>
      simp only [execFullA, recCRevoke, Option.some.injEq] at h; subst h
      exact subset_of_commitments_eq (recKRevokeTarget_commitments _ _ _)
  | mintA actor cell a amt =>
      simp only [execFullA, recCMintAsset] at h
      cases hk : recKMintAsset s.kernel actor cell a amt with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => commit_subst h hk; exact subset_of_commitments_eq (recKMintAsset_commitments hk)
  | burnA actor cell a amt =>
      simp only [execFullA, recCBurnAsset] at h
      cases hk : recKBurnAsset s.kernel actor cell a amt with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => commit_subst h hk; exact subset_of_commitments_eq (recKBurnAsset_commitments hk)
  | setFieldA actor cell f v =>
      -- §SLOT-CAVEAT: `setFieldA` runs the caveat-gated write; peel it to the `stateStep` post-state.
      simp only [execFullA] at h; obtain ⟨_, hs'⟩ := stateStep_factors (stateStepGuarded_eq (stateStepDev_eq h)); subst hs'
      exact subset_of_commitments_eq (writeField_commitments _ _ _ _)
  | emitEventA actor cell topic data =>
      -- §EMIT-LIVE: `emitStep` is now live-cell guarded — peel the `cell ∈ accounts` gate, then the
      -- log-only post-state frames `commitments` (kernel unchanged).
      simp only [execFullA] at h
      by_cases hlive : cell ∈ s.kernel.accounts ∧ acceptsEffects s.kernel cell = true
      · rw [if_pos hlive] at h
        simp only [emitStep, Option.some.injEq] at h; subst h
        exact List.Subset.refl _
      · rw [if_neg hlive] at h; exact absurd h (by simp)
  | incrementNonceA actor cell n =>
      simp only [execFullA] at h; obtain ⟨_, hs'⟩ := stateStep_factors (incrementNonceStep_eq h); subst hs'
      exact subset_of_commitments_eq (writeField_commitments _ _ _ _)
  | setPermissionsA actor cell p =>
      simp only [execFullA] at h; obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'
      exact subset_of_commitments_eq (writeField_commitments _ _ _ _)
  | setVKA actor cell vk =>
      simp only [execFullA] at h; obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'
      exact subset_of_commitments_eq (writeField_commitments _ _ _ _)
  | setProgramA actor cell prog =>
      simp only [execFullA] at h; obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'
      exact subset_of_commitments_eq (writeField_commitments _ _ _ _)
  | introduceA intro rec t =>
      simp only [execFullA, recCDelegate] at h
      cases hk : recKDelegate s.kernel intro rec t with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => commit_subst h hk; exact subset_of_commitments_eq (recKDelegate_commitments hk)
  | delegateAttenA del rec t keep =>
      simp only [execFullA, recCDelegateAtten] at h
      cases hk : recKDelegateAtten s.kernel del rec t keep with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => commit_subst h hk; exact subset_of_commitments_eq (recKDelegateAtten_commitments hk)
  | attenuateA actor idx keep =>
      obtain ⟨_, rfl⟩ := attenuateA_factors h
      simp only [attenuateStepA]; exact List.Subset.refl _
  | revokeDelegationA holder t =>
      simp only [execFullA, recCRevokeDelegationFull, Option.some.injEq] at h; subst h
      -- the FAITHFUL full step edits only `caps` + the three epoch/snapshot registries — `commitments`
      -- is untouched (the epoch legs touch no `commitments`).
      exact subset_of_commitments_eq
        (by rfl : (recKRevokeDelegationFull s.kernel holder t).commitments = s.kernel.commitments)
  | exerciseA actor t inner =>
      simp only [execFullA] at h
      by_cases hf : innerFacetsAdmittedA s actor t inner = true
      · rw [if_pos hf] at h
        cases hg : exerciseStepA s actor t with
        | none => rw [hg] at h; exact absurd h (by simp)
        | some s1 =>
            rw [hg] at h
            obtain ⟨_, hs1⟩ := exerciseStepA_factors hg
            have hk : s1.kernel.commitments = s.kernel.commitments := by rw [hs1]
            exact hk ▸ execInnerA_commitments_grow s1 s' inner h
      · rw [if_neg hf] at h; exact absurd h (by simp)
  | createCellA actor newCell =>
      simp only [execFullA] at h
      obtain ⟨_, _, hs'⟩ := createCellChainA_factors h; subst hs'
      exact subset_of_commitments_eq (createCellIntoAsset_commitments _ _)
  | createCellFromFactoryA actor newCell vk =>
      -- §MA-factory: the factory install leaves `commitments` UNTOUCHED (frame lemma).
      simp only [execFullA] at h
      exact subset_of_commitments_eq (createCellFromFactoryChainA_sideTables h).1
  | spawnA actor child target =>
      simp only [execFullA] at h
      -- §SPAWN-FACTOR: new 4-tuple shape — `⟨s1, ⟨held-edge, target∈accounts⟩, createCellChainA=…, s'=…⟩`.
      obtain ⟨s1, _, hc, hs'⟩ := spawnChainA_factors h; subst hs'
      obtain ⟨_, _, hc'⟩ := createCellChainA_factors hc; subst hc'
      -- post = `{ createCell-state with caps/delegate/delegations := … }`: every edit frames `commitments`.
      exact List.Subset.refl _
  | bridgeMintA actor cell a value =>
      simp only [execFullA, recCMintAsset] at h
      cases hk : recKMintAsset s.kernel actor cell a value with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => commit_subst h hk; exact subset_of_commitments_eq (recKMintAsset_commitments hk)
  | noteSpendA nf actor spendProof =>
      simp only [execFullA, noteSpendChainA] at h
      by_cases hp : spendProof = true
      · rw [if_pos hp] at h
        cases hk : noteSpendNullifier s.kernel nf with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => commit_subst h hk; exact subset_of_commitments_eq (noteSpendNullifier_commitments hk)
      · rw [if_neg hp] at h; exact absurd h (by simp)
  | noteCreateA cm actor =>
      -- THE grow arm: noteCreate conses `cm` onto `commitments` (`noteCreateCommitment`).
      simp only [execFullA, noteCreateChainA, Option.some.injEq] at h; subst h
      show s.kernel.commitments ⊆ (noteCreateCommitment s.kernel cm).commitments
      unfold noteCreateCommitment
      exact List.subset_cons_self cm s.kernel.commitments
  | makeSovereignA actor cell =>
      simp only [execFullA] at h; obtain ⟨_, hs'⟩ := makeSovereignStep_factors h; subst hs'
      exact subset_of_commitments_eq (makeSovereignKernel_commitments _ _)
  | refusalA actor cell =>
      simp only [execFullA] at h; obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'
      exact subset_of_commitments_eq (writeField_commitments _ _ _ _)
  | receiptArchiveA actor cell =>
      simp only [execFullA] at h; obtain ⟨_, hs'⟩ := receiptArchiveChainA_factors h; subst hs'
      exact subset_of_commitments_eq rfl
  | pipelinedSendA actor =>
      simp only [execFullA, Option.some.injEq] at h; subst h; exact subset_of_commitments_eq rfl
  -- §lifecycle (Wave-3) — seal/unseal/destroy edit `lifecycle`/`deathCert`; refresh edits `delegations`
  -- — none touch `commitments` (frame: `rfl`).
  | cellSealA actor cell =>
      simp only [execFullA] at h; obtain ⟨_, hs'⟩ := cellSealChainA_factors h; subst hs'
      exact subset_of_commitments_eq rfl
  | cellUnsealA actor cell =>
      simp only [execFullA] at h; obtain ⟨_, hs'⟩ := cellUnsealChainA_factors h; subst hs'
      exact subset_of_commitments_eq rfl
  | cellDestroyA actor cell ch =>
      simp only [execFullA] at h; obtain ⟨_, hs'⟩ := cellDestroyChainA_factors h; subst hs'
      exact subset_of_commitments_eq rfl
  | refreshDelegationA actor child =>
      simp only [execFullA] at h; obtain ⟨_, hs'⟩ := refreshDelegationChainA_factors h; subst hs'
      exact subset_of_commitments_eq rfl
  | heapWriteA actor target addr v newRoot =>
      -- §MA-heap: the guarded `heap_root` write + `heaps` splice never touches `commitments`.
      simp only [execFullA] at h
      obtain ⟨s₁, hw, hs'⟩ := Dregg2.Substrate.HeapKernel.heapStepGuardedW_factors h
      obtain ⟨-, hs₁⟩ := stateStep_factors (stateStepGuarded_eq hw)
      subst hs'; subst hs₁
      exact subset_of_commitments_eq rfl

/-- **`execInnerA_commitments_grow`** — the inner-effect fold an `exerciseA` recurses through never
shrinks the commitment set. Mutual with `execFullA_commitments_grow`; chains `List.Subset.trans`. -/
theorem execInnerA_commitments_grow (s s' : RecChainedState) (inner : List FullActionA)
    (h : execInnerA s inner = some s') : s.kernel.commitments ⊆ s'.kernel.commitments := by
  cases inner with
  | nil => simp only [execInnerA, Option.some.injEq] at h; subst h; exact List.Subset.refl _
  | cons a rest =>
      simp only [execInnerA] at h
      cases ha : execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          exact List.Subset.trans
            (execFullA_commitments_grow s s1 a ha)
            (execInnerA_commitments_grow s1 s' rest h)
end

/-! ## Step 2 — the turn/forest lift: a committed full-FOREST only grows `commitments`. -/

/-- **`execFullTurnA_commitments_grow`.** A committed per-asset full-TURN (a list of
`FullActionA`) only grows `commitments`: `s.kernel.commitments ⊆ s'.kernel.commitments`. By induction on
the action list — each committed `execFullA` head step grows the set (`execFullA_commitments_grow`); the
empty turn is `subset_refl`; the inductive step chains by `List.Subset.trans`. -/
theorem execFullTurnA_commitments_grow :
    ∀ (s s' : RecChainedState) (tt : List FullActionA),
      execFullTurnA s tt = some s' → s.kernel.commitments ⊆ s'.kernel.commitments
  | s, s', [], h => by
      simp only [execFullTurnA, Option.some.injEq] at h; subst h; exact List.Subset.refl _
  | s, s', a :: rest, h => by
      simp only [execFullTurnA] at h
      cases ha : execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          exact List.Subset.trans (execFullA_commitments_grow s s1 a ha)
            (execFullTurnA_commitments_grow s1 s' rest h)

/-- **`execFullForestA_commitments_grow`.** A committed full-FOREST only grows `commitments`. Read
straight through the pre-order bridge `execFullForestA_eq_execFullTurnA` into `execFullTurnA_commitments_grow`.
This is the forest-level META-FILL-C grow-only registry fact — the one-step obligation of the crown. -/
theorem execFullForestA_commitments_grow (s s' : RecChainedState) (f : FullForestA)
    (h : execFullForestA s f = some s') : s.kernel.commitments ⊆ s'.kernel.commitments := by
  rw [execFullForestA_eq_execFullTurnA] at h
  exact execFullTurnA_commitments_grow s s' (lowerForestA f) h

/-! ## Step 3 — THE CROWN: a published commitment persists along the whole unbounded trajectory. -/

/-- **`livingCellA_commitments_persist` — THE COMMITMENT-PERSISTENCE CROWN.** Fix any baseline set
`com0` of published note commitments contained in the initial state's commitment set. Then `com0` is
contained in `commitments` at EVERY index of the unbounded adversarial trajectory `trajA s sched`, under
EVERY schedule: a published commitment is NEVER retracted, dropped, or rewritten. This is the
anti-equivocation / auditability invariant of the off-ledger commitment tree — the **grow-only DUAL** of the
nullifier set's no-double-spend (`META-FILL C`), now COINDUCTIVE on the SHIPPED executor.

It is carried by `livingCellA_carries` with `Good := (com0 ⊆ ·.kernel.commitments)`, a
NON-conservation safety. Its one-step obligation is discharged from the registry frame on a COMMIT
(`execFullForestA_commitments_grow` grows the set, chained by `List.Subset.trans`) and the **stay-put
self-loop** on a REJECT (`cellNextA` leaves the state — and thus `commitments` — UNCHANGED). With
`livingCellA_logMono` (audit-log append-only) this completes the audit/anti-double-spend pair of the
private-note layer as temporal νF invariants on the real machine. -/
theorem livingCellA_commitments_persist (com0 : List Nat) (s : RecChainedState) (sched : SchedA)
    (hinit : com0 ⊆ s.kernel.commitments) :
    ∀ n, com0 ⊆ (trajA s sched n).kernel.commitments :=
  livingCellA_carries (fun s' => com0 ⊆ s'.kernel.commitments)
    (fun a cf h => by
      -- One-step preservation. `cellNextA a cf = (execFullForestA a cf.1).getD a`: on a COMMIT the forest
      -- registry-frame grows `commitments` (chain by `Subset.trans`); on a REJECT the state is the
      -- UNCHANGED `a`, so the `⊆` is preserved trivially.
      show com0 ⊆ (cellNextA a cf).kernel.commitments
      unfold cellNextA
      cases hc : execFullForestA a cf.1 with
      | some a' => simp only [Option.getD_some]
                   exact List.Subset.trans h (execFullForestA_commitments_grow a a' cf.1 hc)
      | none    => simp only [Option.getD_none]; exact h)
    s hinit sched

/-! ## It runs (`#eval`) — a real `noteCreate` GROWS the commitment set (non-vacuity).

The persistence invariant would be vacuous if no turn ever grew `commitments`. A `noteCreateA cm`
forest commits and conses `cm` onto the set: the length goes `0 → 1` and `cm` is present afterward. So
`livingCellA_commitments_persist` bounds a strictly-growing quantity (a baseline already-present
commitment stays present even as new ones are added), and the crown is exercised by a property that
moves. -/

/-- A real single-`noteCreateA` forest: actor 9 publishes commitment `42`. It commits (a fresh
commitment cannot conflict) and grows `commitments` by one. -/
def noteCreateFA : FullForestA := ⟨.noteCreateA 42 9, []⟩

#guard ((execFullForestA fma0 noteCreateFA).map (fun s' => s'.kernel.commitments)) == some [42]  --  some [42] (grew from [])
#guard (fma0.kernel.commitments.length) == 0  --  0   (BEFORE — strictly less)
#guard ((execFullForestA fma0 noteCreateFA).map (fun s' => decide (42 ∈ s'.kernel.commitments))) == some true  --  some true
-- The carried predicate at a published baseline `[42]` holds AFTER the create (and would FAIL on `∅`-state):
#guard ((execFullForestA fma0 noteCreateFA).map (fun s' => decide (([42] : List Nat) ⊆ s'.kernel.commitments))) == some true  --  some true

/-! ## Axiom hygiene — the persistence crown + the registry frame pinned to the kernel triple (NO extra axiom). -/

#assert_axioms execFullA_commitments_grow
#assert_axioms execFullTurnA_commitments_grow
#assert_axioms execFullForestA_commitments_grow
#assert_axioms livingCellA_commitments_persist

end Dregg2.Exec
