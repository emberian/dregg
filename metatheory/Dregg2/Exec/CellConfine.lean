/-
# Dregg2.Exec.CellConfine — cap-safety / no-amplification carried FOREVER.

`livingCellA_confinement` is the coinductive lift of `Authority/Positional.confinement_preserved`
(the lift of l4v `call_kernel_pas_refined`): fix an authority ceiling `U` with `control ∈ U`; if
the initial kernel's caps are *confined by `U`* — every authority conferred by every held cap lies
in `U` — they stay confined along the entire unbounded adversarial trajectory `trajA`, under every
schedule. *Only connectivity begets connectivity, never beyond the ceiling.*

The one-step obligation `cellNextA_confine` is discharged by how `execFullForestA` moves `caps`:
most effects frame `caps`; `revoke`/`dropRef`/`revokeDelegation` filter a slot; `attenuateCapability`
narrows in place; `delegateAtten` grants `attenuate keep (heldCapTo …)` (conferred ⊆ held ⊆ `U`);
`delegate`/`introduce`/`validateHandoff` copy an already-held witness cap; `spawn` grants a disclosed
`Cap.node` conferring `[control] ⊆ U`.
-/
import Dregg2.Exec.CellCarry
import Dregg2.Exec.AuthTurn

namespace Dregg2.Exec

open Dregg2.Boundary
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Authority
open Dregg2.Exec.EffectsState (state_caps_unchanged stateAuthB stateStepGuarded_eq stateStep_factors stateStepDev_eq incrementNonceStep_eq)

/-! ## Step 1 — `CapsConfined`: the seL4 `PasRefined` upper-bound shape, as a flat ceiling. -/

/-- **`CapsConfined U caps`** — every authority conferred by every held cap, in every slot, lies within
the fixed ceiling `U`. This is `Authority.PasRefined`'s `state_objs_in_policy` clause (`auth ⊆ policy`)
with the per-edge policy collapsed to a single authority ceiling: the policy is an upper bound on
conferred authority, never exceeded. The state predicate whose coinductive carry is confinement. -/
def CapsConfined (U : List Auth) (caps : Caps) : Prop :=
  ∀ (l : Label) (c : Cap) (a : Auth), c ∈ caps l → a ∈ capAuthConferred c → a ∈ U

/-- **`KConfined U k`** — the kernel confinement invariant. F3 STRENGTHENING: with the sealed-box
holding-store DISSOLVED (stored caps are caps-in-slots factory values, `Apps/CapSlotFactory.lean`),
the c-list is the ONLY kernel cap surface — `KConfined` IS `CapsConfined`, and the old box-payload
conjunct (plus its `grant`/`reply` ceiling hypotheses) is gone with the channel it bounded. -/
def KConfined (U : List Auth) (k : RecordKernelState) : Prop :=
  CapsConfined U k.caps

/-- **`CapsConfined.of_caps_eq` — the frame closure.** If `caps' = caps`, confinement transfers verbatim. -/
theorem CapsConfined.of_caps_eq {U : List Auth} {caps caps' : Caps}
    (heq : caps' = caps) (h : CapsConfined U caps) : CapsConfined U caps' := by
  subst heq; exact h

/-- **`CapsConfined.mono` — the subset closure (revocation / filtering).** If every slot of
`caps'` is a sublist of `caps` (authority only shrank — `revoke`, `dropRef`, `revokeDelegation`),
confinement is preserved: a cap held in `caps'` was held in `caps`, hence bounded. -/
theorem CapsConfined.mono {U : List Auth} {caps caps' : Caps}
    (hsub : ∀ l, caps' l ⊆ caps l) (h : CapsConfined U caps) : CapsConfined U caps' :=
  fun l c a hc ha => h l c a (hsub l hc) ha

/-- **`mem_modify_cases` — the `List.modify` membership dichotomy.** Every member of
`l.modify n f` is either a member of `l` (untouched) or `f d` for some member `d` of `l` (the one
replaced at index `n`). The list-level fact behind the in-place attenuation closure. -/
theorem mem_modify_cases {α : Type _} (f : α → α) :
    ∀ (n : Nat) (l : List α) (c : α), c ∈ l.modify n f → c ∈ l ∨ ∃ d ∈ l, c = f d
  | _,     [],      c, hc => by
      rw [List.modify_nil] at hc; exact absurd hc (by simp)
  | 0,     a :: l,  c, hc => by
      rw [show (a :: l).modify 0 f = f a :: l from rfl, List.mem_cons] at hc
      rcases hc with hca | hcl
      · exact Or.inr ⟨a, List.mem_cons_self, hca⟩
      · exact Or.inl (List.mem_cons.mpr (Or.inr hcl))
  | n+1,   a :: l,  c, hc => by
      rw [List.modify_succ_cons, List.mem_cons] at hc
      rcases hc with hca | hcl
      · exact Or.inl (List.mem_cons.mpr (Or.inl hca))
      · rcases mem_modify_cases f n l c hcl with h1 | ⟨d, hd, hcd⟩
        · exact Or.inl (List.mem_cons.mpr (Or.inr h1))
        · exact Or.inr ⟨d, List.mem_cons.mpr (Or.inr hd), hcd⟩

/-- **`CapsConfined.grant` — the grant closure.** Prepending a cap `c` to `holder`'s slot
preserves confinement provided `c`'s own conferred authority lies within `U`. Covers every authority
grant: ordinary delegation, validate-handoff, and spawn copy a confined held cap; `delegateAtten` grants
an attenuation of a held cap; seal-pair creation grants fresh seal caps under the explicit ceiling. -/
theorem CapsConfined.grant {U : List Auth} {caps : Caps} {holder : Label} {c : Cap}
    (hc : ∀ a ∈ capAuthConferred c, a ∈ U) (h : CapsConfined U caps) :
    CapsConfined U (Dregg2.Exec.grant caps holder c) := by
  intro l d a hd ha
  unfold Dregg2.Exec.grant at hd
  by_cases hl : l = holder
  · rw [if_pos hl] at hd
    rcases List.mem_cons.mp hd with hdc | hdrest
    · subst hdc; exact hc a ha          -- the freshly-granted cap: bounded by hypothesis.
    · exact h l d a hdrest ha            -- an already-held cap: bounded by confinement.
  · rw [if_neg hl] at hd; exact h l d a hd ha

/-- **`CapsConfined.attenuateSlot` — the in-place narrow closure (`AttenuateCapability`).**
Replacing the `idx`-th cap of `actor` with its `keep`-attenuation (`List.modify idx (attenuate keep)`)
preserves confinement: a surviving cap is either an untouched old cap (bounded) or `attenuate keep d`
for the old cap `d` at `idx` (conferred ⊆ `d`'s ⊆ `U`, via `attenuate_subset`). -/
theorem CapsConfined.attenuateSlot {U : List Auth} {caps : Caps} {actor : Label} {idx : Nat}
    {keep : List Auth} (h : CapsConfined U caps) :
    CapsConfined U (attenuateSlotF caps actor idx keep) := by
  intro l c a hc ha
  unfold attenuateSlotF at hc
  by_cases hl : l = actor
  · rw [if_pos hl] at hc
    -- `c ∈ (caps actor).modify idx (attenuate keep)`. `List.modify` replaces ONE element; every member
    -- is either an unchanged member of `caps actor` or `attenuate keep` of one.
    rcases mem_modify_cases (attenuate keep) idx (caps l) c hc with hmem | ⟨d, hdmem, hcd⟩
    · exact h l c a hmem ha
    · -- `c = attenuate keep d` with `d ∈ caps actor`: conferred ⊆ `d`'s conferred ⊆ U.
      subst hcd
      exact h l d a hdmem (attenuate_subset keep d ha)
  · rw [if_neg hl] at hc; exact h l c a hc ha

/-! ## Step 2 — the per-primitive confinement steps (the 5 cap-writing chained ops). -/

/-- `recCRevoke` (the `revoke`/`dropRef`/`revokeDelegation` body) only FILTERS the holder's slot, so the
post-state caps are slot-wise ⊆ the pre-state caps — confinement is preserved by `CapsConfined.mono`. -/
theorem recCRevoke_confine {U : List Auth} {s : RecChainedState} {holder t : CellId}
    (h : CapsConfined U s.kernel.caps) : CapsConfined U (recCRevoke s holder t).kernel.caps := by
  refine CapsConfined.mono (fun l => ?_) h
  -- `(recCRevoke s holder t).kernel.caps = recKRevokeTarget s.kernel holder t |>.caps`.
  show (recKRevokeTarget s.kernel holder t).caps l ⊆ s.kernel.caps l
  simp only [recKRevokeTarget]
  by_cases hl : l = holder
  · subst hl; rw [if_pos rfl]; intro d hd; exact List.mem_of_mem_filter hd
  · rw [if_neg hl]

/-- A committed `createCellChainA` resets the fresh id's cap slot to `[]` and frames every other slot. -/
theorem createCellChainA_caps_frame {s s' : RecChainedState} {actor newCell : CellId}
    (h : createCellChainA s actor newCell = some s') :
    (∀ l, l ≠ newCell → s'.kernel.caps l = s.kernel.caps l)
    ∧ s'.kernel.caps newCell = [] := by
  obtain ⟨_, _, hs'⟩ := createCellChainA_factors h
  subst hs'
  dsimp [createCellIntoAsset, bornEmptyCellSlots]
  constructor
  · intro l hl; simp only [if_neg hl]
  · simp only [if_pos]

/-- **`CapsConfined` survives born-empty cap reset** at one fresh label. -/
theorem CapsConfined.of_fresh_slot {U : List Auth} {caps caps' : Caps} {fresh : Label}
    (hpre : CapsConfined U caps) (hempty : caps' fresh = [])
    (hframe : ∀ l, l ≠ fresh → caps' l = caps l) :
    CapsConfined U caps' := by
  intro holder cap auth hmem hconf
  by_cases hh : holder = fresh
  · subst hh; simpa [hempty] using hmem
  · exact hpre holder cap auth (by simpa [hframe holder hh] using hmem) hconf

/-- **`CapsConfined.of_fresh_singleton` — install one confined cap at a born-empty fresh slot.** -/
theorem CapsConfined.of_fresh_singleton {U : List Auth} {caps caps' : Caps} {fresh : Label} {c : Cap}
    (hpre : CapsConfined U caps) (hempty : caps fresh = [])
    (hframe : ∀ l, l ≠ fresh → caps' l = caps l) (hsingleton : caps' fresh = [c])
    (hc : ∀ a ∈ capAuthConferred c, a ∈ U) :
    CapsConfined U caps' := by
  intro holder cap auth hmem hconf
  by_cases hh : holder = fresh
  · subst hh
    rw [hsingleton] at hmem
    rcases List.mem_singleton.mp hmem with rfl
    exact hc auth hconf
  · exact hpre holder cap auth (by simpa [hframe holder hh] using hmem) hconf

/-- **`CapsConfined` survives `createCellChainA`.** -/
theorem CapsConfined.of_createCell {U : List Auth} {s s' : RecChainedState} {actor newCell : CellId}
    (hpre : CapsConfined U s.kernel.caps) (h : createCellChainA s actor newCell = some s') :
    CapsConfined U s'.kernel.caps := by
  have ⟨hframe, hempty⟩ := createCellChainA_caps_frame h
  exact CapsConfined.of_fresh_slot hpre hempty hframe

/-! ### The kernel-function caps-frame lemmas: every NON-authority kernel transition FRAMES `caps`.

Each `RecordKernel`/supply transition writes a NON-`caps` field (`bal`/`swiss`/
`nullifiers`/`commitments`/`cell`) via a record update `{ k with field := … }`, so the cap table is
literally unchanged on every committed branch. Proved by the uniform `unfold; split; subst; rfl` shape
(the raw helpers unfold to record-update literals whose `.caps` projection is `rfl`). These are the
discharge for the ~30 FRAME effects of `execFullA_confine`. -/

theorem recKExecAsset_caps {k k' : RecordKernelState} {t : Turn} {a : AssetId}
    (h : recKExecAsset k t a = some k') : k'.caps = k.caps := by
  unfold recKExecAsset at h; split at h
  · option_inj at h; rcases h with ⟨rfl⟩; rfl
  · exact absurd h (by simp)

theorem recKMintAsset_caps {k k' : RecordKernelState} {actor cell : CellId} {a : AssetId} {amt : ℤ}
    (h : recKMintAsset k actor cell a amt = some k') : k'.caps = k.caps := by
  unfold recKMintAsset at h; split at h
  · option_inj at h; rcases h with ⟨rfl⟩; rfl
  · exact absurd h (by simp)

theorem recKBurnAsset_caps {k k' : RecordKernelState} {actor cell : CellId} {a : AssetId} {amt : ℤ}
    (h : recKBurnAsset k actor cell a amt = some k') : k'.caps = k.caps := by
  unfold recKBurnAsset at h; split at h
  · option_inj at h; rcases h with ⟨rfl⟩; rfl
  · exact absurd h (by simp)

theorem noteSpendNullifier_caps {k k' : RecordKernelState} {nf : Nat}
    (h : noteSpendNullifier k nf = some k') : k'.caps = k.caps := by
  unfold noteSpendNullifier at h; split at h
  · exact absurd h (by simp)
  · option_inj at h; rcases h with ⟨rfl⟩; rfl

/-! ## Step 3 — `execFullA_confine`: one full-action step preserves confinement (the CORE case split). -/

mutual
/-- **`execFullA_confine` — the per-action confinement step.** Under a ceiling `U` admitting the
whole self-cap (`nodeFacets ⊆ U`), every committed `FullActionA` preserves `CapsConfined U`. The ~40
non-authority effects frame `caps` (`*_caps_unchanged`/`rfl`); `revoke`/`dropRef`/`revokeDelegation`
filter (`mono`); `attenuate` narrows in place (`attenuateSlot`); `delegate`/`introduce`/
`validateHandoff` copy an already-held cap ON THE CROSS PATH; `delegateAtten` grants
`attenuate keep (delegatedCapTo …)` whose conferred authority is ⊆ the delegated parent cap;
`spawn` copies a held parent cap. `exerciseA` RECURSES (mutual `execInnerA_confine`, same ceiling).
This is `confinement_preserved` discharged on the executor, per effect.

⚑ **THE CEILING PREMISE GREW ON 2026-07-31, and this is the honest place to read why.** It used to be
`Auth.control ∈ U`. The kernel cutover gave `recKDelegate` its owner disjunct, and on the SELF path a
delegation deposits the implicit self-cap `Cap.node t`, which confers ALL EIGHT `nodeFacets`. So under
a ceiling missing any single facet the conclusion is FALSE, and the old premise was no longer enough.

The new premise is STRICTLY STRONGER (`nodeFacets ⊆ U` gives `Auth.control ∈ U` by `decide`), so no
conclusion weakened and no consumer lost a guarantee — but the theorem now applies to FEWER ceilings,
and that cost is real. `self_grant_needs_the_full_ceiling` below exhibits a ceiling where the old
statement would now be false, so this is a measured requirement, not a defensive over-assumption. -/
theorem execFullA_confine {U : List Auth} (hctrl : ∀ a ∈ nodeFacets, a ∈ U)
    (s s' : RecChainedState) (fa : FullActionA)
    (h : execFullA s fa = some s') (hpre : CapsConfined U s.kernel.caps) :
    CapsConfined U s'.kernel.caps := by
  cases fa with
  -- ===== balance / supply / state / swiss / note / bridge: FRAME `caps`. =====
  | balanceA t a =>
      refine CapsConfined.of_caps_eq ?_ hpre
      obtain ⟨_, ⟨k', hk, hs'⟩⟩ := recCexecAsset_factors t a (by simpa only [execFullA] using h)
      subst hs'
      exact recKExecAsset_caps hk
  | mintA actor cell a amt =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, recCMintAsset] at h
      cases hm : recKMintAsset s.kernel actor cell a amt with
      | none => rw [hm] at h; exact absurd h (by simp)
      | some k' => rw [hm] at h; option_inj at h; rcases h with ⟨rfl⟩
                   exact recKMintAsset_caps hm
  | burnA actor cell a amt =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, recCBurnAsset] at h
      cases hm : recKBurnAsset s.kernel actor cell a amt with
      | none => rw [hm] at h; exact absurd h (by simp)
      | some k' => rw [hm] at h; option_inj at h; rcases h with ⟨rfl⟩
                   exact recKBurnAsset_caps hm
  | setFieldA actor cell f v =>
      -- §SLOT-CAVEAT: peel the caveat gate (`stateStepGuarded_eq`); the field write never edits `caps`.
      exact CapsConfined.of_caps_eq
        (state_caps_unchanged (stateStepGuarded_eq (stateStepDev_eq (by simpa only [execFullA] using h)))) hpre
  | emitEventA actor cell topic data =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA] at h
      by_cases hlive : cell ∈ s.kernel.accounts ∧ acceptsEffects s.kernel cell = true
      · rw [if_pos hlive] at h
        simp only [Option.some.injEq] at h
        subst h
        rfl
      · rw [if_neg hlive] at h
        exact absurd h (by simp)
  | incrementNonceA actor cell n =>
      exact CapsConfined.of_caps_eq (state_caps_unchanged (incrementNonceStep_eq (by simpa only [execFullA] using h))) hpre
  | setPermissionsA actor cell p =>
      exact CapsConfined.of_caps_eq (state_caps_unchanged (by simpa only [execFullA] using h)) hpre
  | setVKA actor cell vk =>
      exact CapsConfined.of_caps_eq (state_caps_unchanged (by simpa only [execFullA] using h)) hpre
  | setProgramA actor cell prog =>
      exact CapsConfined.of_caps_eq (state_caps_unchanged (by simpa only [execFullA] using h)) hpre
  -- ===== AUTHORITY effects: the cap-writing arms. =====
  | introduceA intro rec t =>
      -- grants the held witness cap; confinement follows because that cap was already confined.
      simp only [execFullA, recCDelegate] at h
      cases hd : recKDelegate s.kernel intro rec t with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some k' =>
          rw [hd] at h; option_inj at h; rcases h with ⟨rfl⟩
          show CapsConfined U k'.caps
          unfold recKDelegate at hd
          by_cases hg : t = intro ∨ (s.kernel.caps intro).any (fun cap => confersEdgeTo t cap) = true
          · rw [if_pos hg] at hd; simp only [Option.some.injEq] at hd; subst hd
            show CapsConfined U (Dregg2.Exec.grant s.kernel.caps rec (delegatedCapTo s.kernel.caps intro t))
            refine CapsConfined.grant (fun a ha => ?_) hpre
            -- ⚑ TWO PATHS as of the 2026-07-31 cutover. CROSS: the granted cap is one the delegator
            -- already HELD, so confinement carries from `hpre`. SELF: the granted cap is the implicit
            -- `Cap.node t`, conferring ALL of `nodeFacets` — bounded only by the CEILING, which is
            -- why `hctrl` had to grow from `control ∈ U` to `nodeFacets ⊆ U`.
            unfold delegatedCapTo at ha
            by_cases hself : t = intro
            · rw [if_pos hself] at ha; exact hctrl a ha
            · rw [if_neg hself] at ha
              exact hpre intro (heldCapTo s.kernel.caps intro t) a
                (heldCapTo_mem s.kernel.caps intro t (hg.resolve_left hself)).1 ha
          · rw [if_neg hg] at hd; exact absurd hd (by simp)
  | delegate del rec t =>
      simp only [execFullA, recCDelegate] at h
      cases hd : recKDelegate s.kernel del rec t with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some k' =>
          rw [hd] at h; option_inj at h; rcases h with ⟨rfl⟩
          show CapsConfined U k'.caps
          unfold recKDelegate at hd
          by_cases hg : t = del ∨ (s.kernel.caps del).any (fun cap => confersEdgeTo t cap) = true
          · rw [if_pos hg] at hd; simp only [Option.some.injEq] at hd; subst hd
            show CapsConfined U (Dregg2.Exec.grant s.kernel.caps rec (delegatedCapTo s.kernel.caps del t))
            refine CapsConfined.grant (fun a ha => ?_) hpre
            -- ⚑ TWO PATHS as of the 2026-07-31 cutover. CROSS: the granted cap is one the delegator
            -- already HELD, so confinement carries from `hpre`. SELF: the granted cap is the implicit
            -- `Cap.node t`, conferring ALL of `nodeFacets` — bounded only by the CEILING, which is
            -- why `hctrl` had to grow from `control ∈ U` to `nodeFacets ⊆ U`.
            unfold delegatedCapTo at ha
            by_cases hself : t = del
            · rw [if_pos hself] at ha; exact hctrl a ha
            · rw [if_neg hself] at ha
              exact hpre del (heldCapTo s.kernel.caps del t) a
                (heldCapTo_mem s.kernel.caps del t (hg.resolve_left hself)).1 ha
          · rw [if_neg hg] at hd; exact absurd hd (by simp)
  | delegateAttenA del rec t keep =>
      -- grants `attenuate keep (heldCapTo s.kernel.caps del t)`; conferred ⊆ the held parent cap ⊆ U.
      simp only [execFullA, recCDelegateAtten] at h
      -- Reduce the chained delegate to its kernel; peel the connectivity gate ONCE.
      cases hd : recKDelegateAtten s.kernel del rec t keep with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some k' =>
          rw [hd] at h; option_inj at h; rcases h with ⟨rfl⟩
          show CapsConfined U k'.caps
          -- On commit the gate fired, and `k'.caps` is the grant of `delegatedAttenCapTo`.
          unfold recKDelegateAtten at hd
          split at hd
          · rename_i hgate
            simp only [Option.some.injEq] at hd; subst hd
            show CapsConfined U
              (Dregg2.Exec.grant s.kernel.caps rec (delegatedAttenCapTo s.kernel.caps del t keep))
            refine CapsConfined.grant (fun a ha => ?_) hpre
            -- The granted cap is an ATTENUATION of the delegated parent, so its conferred authority
            -- is ⊆ the parent's (`attenuate_subset`). The parent is a HELD cap on the cross path
            -- (bounded by `hpre`) and the implicit `Cap.node t` self-cap on the SELF path (bounded
            -- only by the ceiling `hctrl`) — the same two-path split as the unattenuated arm.
            unfold delegatedAttenCapTo delegatedCapTo at ha
            have ha' := attenuate_subset keep _ ha
            by_cases hself : t = del
            · rw [if_pos hself] at ha'; exact hctrl a ha'
            · rw [if_neg hself] at ha'
              exact hpre del (heldCapTo s.kernel.caps del t) a
                (heldCapTo_mem s.kernel.caps del t (hgate.resolve_left hself)).1 ha'
          · exact absurd hd (by simp)
  | attenuateA actor idx keep =>
      obtain ⟨_, rfl⟩ := attenuateA_factors h
      simp only [attenuateStepA]; exact CapsConfined.attenuateSlot hpre
  | revokeDelegationA holder t =>
      simp only [execFullA] at h; option_inj at h; rcases h with ⟨rfl⟩
      exact recCRevoke_confine hpre
  | revoke holder t =>
      simp only [execFullA] at h; option_inj at h; rcases h with ⟨rfl⟩
      exact recCRevoke_confine hpre
  | exerciseA actor t inner =>
      -- exercise's hold-gate READS the c-list (caps framed); then the inner fold RECURSES, preserving
      -- confinement at each step (mutual `execInnerA_confine`, with the SAME `control ∈ U` ceiling).
      simp only [execFullA] at h
      by_cases hf : innerFacetsAdmittedA s actor t inner = true
      · rw [if_pos hf] at h
        cases hg : exerciseStepA s actor t with
        | none => rw [hg] at h; exact absurd h (by simp)
        | some s1 =>
            rw [hg] at h
            obtain ⟨_, hs1⟩ := exerciseStepA_factors hg
            have hpre1 : CapsConfined U s1.kernel.caps :=
              CapsConfined.of_caps_eq (by rw [hs1]) hpre
            exact execInnerA_confine hctrl s1 s' inner h hpre1
      · rw [if_neg hf] at h; exact absurd h (by simp)
  -- ===== supply: createCell FRAMEs caps; spawn copies a held parent cap plus metadata. =====
  | createCellA actor newCell =>
      exact CapsConfined.of_createCell hpre (by simpa only [execFullA] using h)
  | createCellFromFactoryA actor newCell vk =>
      have hcap := createCellFromFactoryChainA_caps_frame (by simpa only [execFullA] using h)
      exact CapsConfined.of_fresh_slot hpre hcap.2 hcap.1
  | spawnA actor child target =>
      simp only [execFullA] at h
      obtain ⟨s1, hground, hc1, hs'⟩ := spawnChainA_factors h
      subst hs'
      have hpre1 : CapsConfined U s1.kernel.caps := CapsConfined.of_createCell hpre hc1
      have hempty : s1.kernel.caps child = [] := (createCellChainA_caps_frame hc1).2
      have hframe := (createCellChainA_caps_frame hc1).1
      exact CapsConfined.of_fresh_singleton (caps := s1.kernel.caps)
        (caps' := fun l => if l = child then [heldCapTo s.kernel.caps actor target] else s.kernel.caps l)
        (fresh := child) (c := heldCapTo s.kernel.caps actor target) hpre1 hempty
        (fun l hl => by simp [if_neg hl, hframe l hl])
        (by simp)
        (fun a ha => hpre actor (heldCapTo s.kernel.caps actor target) a
          (heldCapTo_mem s.kernel.caps actor target hground.1).1 ha)
  | bridgeMintA actor cell a value =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, recCMintAsset] at h
      cases hm : recKMintAsset s.kernel actor cell a value with
      | none => rw [hm] at h; exact absurd h (by simp)
      | some k' => rw [hm] at h; option_inj at h; rcases h with ⟨rfl⟩
                   exact recKMintAsset_caps hm
  | noteSpendA nf actor spendProof =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, noteSpendChainA] at h
      by_cases hp : spendProof = true
      · rw [if_pos hp] at h
        cases hk : noteSpendNullifier s.kernel nf with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => rw [hk] at h; option_inj at h; rcases h with ⟨rfl⟩; exact noteSpendNullifier_caps hk
      · rw [if_neg hp] at h; exact absurd h (by simp)
  | noteCreateA cm actor =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, noteCreateChainA] at h; option_inj at h; rcases h with ⟨rfl⟩; rfl
  | makeSovereignA actor cell =>
      refine CapsConfined.of_caps_eq ?_ hpre
      obtain ⟨_, hs'⟩ := makeSovereignStep_factors (by simpa only [execFullA] using h)
      subst hs'; rfl
  | refusalA actor cell =>
      exact CapsConfined.of_caps_eq (state_caps_unchanged (by simpa only [execFullA] using h)) hpre
  | receiptArchiveA actor cell =>
      obtain ⟨_, hs'⟩ := receiptArchiveChainA_factors (by simpa only [execFullA] using h)
      exact CapsConfined.of_caps_eq (by rw [hs']; rfl) hpre
  | pipelinedSendA actor =>
      refine CapsConfined.of_caps_eq ?_ hpre
      simp only [execFullA, Option.some.injEq] at h; subst h; rfl
  -- ===== swiss: FRAME caps (gated by `if stateAuthB …`; peel + kernel caps lemma). =====
  -- ===== lifecycle (Wave-3): seal/unseal/destroy edit `lifecycle`/`deathCert`; refresh edits
  -- `delegations` — all FRAME `caps`. =====
  | cellSealA actor cell =>
      obtain ⟨_, hs'⟩ := cellSealChainA_factors (by simpa only [execFullA] using h)
      exact CapsConfined.of_caps_eq (by rw [hs']; rfl) hpre
  | cellUnsealA actor cell =>
      obtain ⟨_, hs'⟩ := cellUnsealChainA_factors (by simpa only [execFullA] using h)
      exact CapsConfined.of_caps_eq (by rw [hs']; rfl) hpre
  | cellDestroyA actor cell ch =>
      obtain ⟨_, hs'⟩ := cellDestroyChainA_factors (by simpa only [execFullA] using h)
      exact CapsConfined.of_caps_eq (by rw [hs']; rfl) hpre
  | refreshDelegationA actor child =>
      obtain ⟨_, hs'⟩ := refreshDelegationChainA_factors (by simpa only [execFullA] using h)
      exact CapsConfined.of_caps_eq (by rw [hs']) hpre
  | heapWriteA actor target addr v newRoot =>
      -- §MA-heap: the guarded `heap_root` write + `heaps` splice never touches `caps`.
      obtain ⟨s₁, hw, hs'⟩ := Dregg2.Substrate.HeapKernel.heapStepGuardedW_factors
        (by simpa only [execFullA] using h)
      obtain ⟨-, hs₁⟩ := stateStep_factors (stateStepGuarded_eq hw)
      subst hs'; subst hs₁
      exact CapsConfined.of_caps_eq rfl hpre

/-- **`execInnerA_confine`** — the inner-effect fold an `exerciseA` recurses through preserves
confinement under the SAME `control ∈ U` ceiling (+ the Wave-3 `grant`/`reply`/box hypotheses for the
seal cluster). Mutual with `execFullA_confine`; induction on the inner list, threading the per-step
confinement AND the box-confinement carry (each step preserves `BoxesConfined`, via the dedicated
`execFullA_boxesConfine` below). -/
theorem execInnerA_confine {U : List Auth} (hctrl : ∀ a ∈ nodeFacets, a ∈ U)
    (s s' : RecChainedState) (inner : List FullActionA)
    (h : execInnerA s inner = some s') (hpre : CapsConfined U s.kernel.caps) :
    CapsConfined U s'.kernel.caps := by
  cases inner with
  | nil => simp only [execInnerA, Option.some.injEq] at h; subst h; exact hpre
  | cons a rest =>
      simp only [execInnerA] at h
      cases ha : execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          exact execInnerA_confine hctrl s1 s' rest h
            (execFullA_confine hctrl s s1 a ha hpre)

end

/-! ## Step 4 — lift to the forest turn, then the full forest (the executed cell step). -/

/-- **`execFullTurnA_kconfine` (Wave-3)** — a committed full turn preserves the COMBINED invariant
`KConfined U` (caps AND sealed-box payloads): induction on the action list, chaining both halves
(`execFullA_confine` + `execFullA_boxesConfine`). -/
theorem execFullTurnA_kconfine {U : List Auth} (hctrl : ∀ a ∈ nodeFacets, a ∈ U) :
    ∀ (s s' : RecChainedState) (tt : List FullActionA),
      execFullTurnA s tt = some s' → KConfined U s.kernel → KConfined U s'.kernel
  | s, s', [], h, hpre => by
      simp only [execFullTurnA, Option.some.injEq] at h; subst h; exact hpre
  | s, s', a :: rest, h, hpre => by
      simp only [execFullTurnA] at h
      cases ha : execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          exact execFullTurnA_kconfine hctrl s1 s' rest h
            (execFullA_confine hctrl s s1 a ha hpre)

/-- **`execFullTurnA_confine`** — the caps-half corollary (the headline confinement crown): a committed
full turn preserves `CapsConfined U`, given the initial kernel is fully `KConfined` (caps + boxes). -/
theorem execFullTurnA_confine {U : List Auth} (hctrl : ∀ a ∈ nodeFacets, a ∈ U)
    (s s' : RecChainedState) (tt : List FullActionA)
    (h : execFullTurnA s tt = some s') (hpre : KConfined U s.kernel) :
    CapsConfined U s'.kernel.caps :=
  execFullTurnA_kconfine hctrl s s' tt h hpre

/-- **`execFullForestA_kconfine`** — a committed full forest preserves `KConfined U`. Routes through
the pre-order bridge `execFullForestA_eq_execFullTurnA` into `execFullTurnA_kconfine`. -/
theorem execFullForestA_kconfine {U : List Auth} (hctrl : ∀ a ∈ nodeFacets, a ∈ U)
    (s s' : RecChainedState) (f : FullForestA)
    (h : execFullForestA s f = some s') (hpre : KConfined U s.kernel) :
    KConfined U s'.kernel := by
  rw [execFullForestA_eq_execFullTurnA] at h
  exact execFullTurnA_kconfine hctrl s s' (lowerForestA f) h hpre

/-- **`cellNextA_kconfine` — the one-step obligation.** A single living-cell step preserves `KConfined U`:
on a commit the forest confinement lemma applies; on a reject the state is unchanged. -/
theorem cellNextA_kconfine {U : List Auth} (hctrl : ∀ a ∈ nodeFacets, a ∈ U)
    (s : RecChainedState) (cf : ConservingForest) (hpre : KConfined U s.kernel) :
    KConfined U (cellNextA s cf).kernel := by
  unfold cellNextA
  cases hc : execFullForestA s cf.1 with
  | some s' => simp only [Option.getD_some]; exact execFullForestA_kconfine hctrl s s' cf.1 hc hpre
  | none    => simp only [Option.getD_none]; exact hpre

/-! ## Step 5 — `livingCellA_confinement`: confinement carried FOREVER. -/

/-! ### Step 4.CEILING — WHY the ceiling premise is `nodeFacets ⊆ U` and not `control ∈ U`. -/

/-- The post-`caps` of cell `0`'s FIRST self-grant to cell `1`, out of the faucet-minted `rs0` (every
cap slot EMPTY). The cutover admits this turn; it deposits the implicit `Cap.node 0` self-cap. -/
def selfGrantPostCaps : Caps := ((recKDelegate rs0 0 1 0).getD rs0).caps

-- The self-grant commits and lands the full self-cap (the object the ceiling has to bound).
#guard (recKDelegate rs0 0 1 0).isSome
#guard (selfGrantPostCaps 1) == [Cap.node 0]

/-- **`self_grant_needs_the_full_ceiling` — THE MEASUREMENT BEHIND THE GROWN PREMISE.** Over the
ceiling `U = [control]`:

  * the OLD premise `Auth.control ∈ U` HOLDS;
  * the pre-state `rs0` IS confined by `U` (every slot empty);
  * cell `0`'s first self-grant COMMITS (the cutover);
  * and the post-state is **NOT** confined by `U` — the deposited `Cap.node 0` confers `read`, which
    is not in `U`.

So `execFullA_confine` stated with the old premise would be FALSE after the cutover. This is why the
premise grew to `nodeFacets ⊆ U`, and it is stated as a refutation rather than asserted in prose: if
someone weakens the premise back, this theorem is what contradicts them. It also shows the growth is
NOT over-assumption — `read ∉ [control]` is the actual witness. -/
theorem self_grant_needs_the_full_ceiling :
    Auth.control ∈ ([Auth.control] : List Auth)
    ∧ CapsConfined [Auth.control] rs0.caps
    ∧ (recKDelegate rs0 0 1 0).isSome
    ∧ ¬ CapsConfined [Auth.control] selfGrantPostCaps := by
  refine ⟨by decide, ?_, recKDelegate_admits_self rs0 0 1, ?_⟩
  · -- every slot of `rs0` is empty, so confinement is vacuous at the pre-state.
    intro l c a hc _
    simp only [rs0] at hc
    exact absurd hc (by simp)
  · -- the granted `Cap.node 0` confers `read`, and `read ∉ [control]`.
    intro hcon
    exact absurd (hcon 1 (Cap.node 0) Auth.read (by decide) (by decide)) (by decide)

#assert_axioms self_grant_needs_the_full_ceiling

/-- **`livingCellA_confinement`** — Fix an authority ceiling `U` admitting the whole self-cap
(`nodeFacets ⊆ U`; strictly stronger than the pre-cutover `control ∈ U`, and necessary —
`self_grant_needs_the_full_ceiling`). If the initial
kernel's caps are confined by `U` (every authority conferred by every held cap lies in `U`), they stay
confined at every index of the unbounded adversarial trajectory `trajA s sched`, under every schedule:

  `∀ n, CapsConfined U (trajA s sched n).kernel.caps`.

This is the seL4 object-integrity confinement (`Authority/Positional.confinement_preserved`, lifted from
l4v `call_kernel_pas_refined`: a turn never grows authority beyond the policy upper bound) carried
coinductively: held-cap copies (ordinary delegation, handoff, spawn), attenuating delegation edges, and
fresh seal caps never push conferred authority past the fixed ceiling, for all time.
`cellNextA_confine` is the one-step obligation; `livingCellA_carries` carries it over the entire
adversarial future. -/
theorem livingCellA_confinement {U : List Auth} (hctrl : ∀ a ∈ nodeFacets, a ∈ U)
    (s : RecChainedState) (hinit : KConfined U s.kernel) (sched : SchedA) :
    ∀ n, CapsConfined U (trajA s sched n).kernel.caps :=
  -- F3 STRENGTHENING: the ceiling needs ONLY `control` — the seal-cluster `grant`/`reply`
  -- hypotheses died with the sealed-box channel. Carry `KConfined` forever.
  fun n => livingCellA_carries (fun s' => KConfined U s'.kernel)
    (fun a cf h => cellNextA_kconfine hctrl a cf h) s hinit sched n

/-! ## It runs (`#eval`) — confinement is non-vacuous on a real grant + a real ceiling.

A real cap table where cell 0 holds an `endpoint 7 [read, write]` cap. The ceiling `U = full Auth`
(all 7 kinds) confines it; a ceiling missing the relevant authority would fail on the grant, so the
bound has teeth. -/

/-- The full authority enumeration — the most permissive ceiling, containing `control` (and now
`notify`, the 8th IPC authority — so the ceiling stays "all kinds"). -/
def fullAuthCeiling : List Auth :=
  [Auth.read, Auth.write, Auth.grant, Auth.call, Auth.reply, Auth.reset, Auth.control, Auth.notify]

#guard (decide (Auth.control ∈ fullAuthCeiling))  --  true (the carry hypothesis holds)
-- `[read]` is confined by the full ceiling; `[grant]`-only ceiling does NOT contain `control`:
#guard (decide (∀ a ∈ capAuthConferred (Cap.endpoint 7 [Auth.read]), a ∈ fullAuthCeiling))  --  true
#guard (decide (Auth.control ∈ [Auth.grant])) == false  --  false (a too-tight ceiling rejects connectivity grants)
#guard (decide (∀ a ∈ capAuthConferred (Cap.node 7), a ∈ fullAuthCeiling))  --  true (nodeFacets ⊆ full)

/-! ## Axiom hygiene — confinement + one-step obligation pinned to the kernel triple. -/

#assert_axioms CapsConfined.grant
#assert_axioms CapsConfined.attenuateSlot
#assert_axioms execFullA_confine
#assert_axioms execFullForestA_kconfine
#assert_axioms cellNextA_kconfine
#assert_axioms livingCellA_confinement

end Dregg2.Exec
