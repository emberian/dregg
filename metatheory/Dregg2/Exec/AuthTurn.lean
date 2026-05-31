/-
# Dregg2.Exec.AuthTurn — the AUTHORITY-mutating executable kernel transition (the DUAL turn).

`Exec/RecordKernel.lean`'s `recKExec` is a BALANCE turn: it rewrites the `balance` field and
PRESERVES `caps` (`recKExec_frame`), so its abstract image holds the authority graph FIXED — the
`(C)∧(A)∧(G)` square `Proof/LTS.lean §3` closes. `Proof/LTS.lean §5,§7` then PINS the precise
residue: the `Spec.Authority.AuthStep`-firing half of the operational LTS is NOT a proof gap in
that square but a **missing executable transition** — an authority-mutating kernel that EDITS
`caps` (a Granovetter delegate / a revoke) rather than the balance field. This module BUILDS that
missing transition, its DUAL frame lemma (`recTotal` UNCHANGED — an authority turn is
conservation-trivial, the mirror of `recKExec_frame`'s authority-fixed), and the graph-change
lemma mapping the executable cap-edit onto `Spec.Authority`'s `Introduce`/`Revoke` `result`
(`G' = addEdge/removeEdge …`). `Proof/LTS.lean §7` then assembles the authority-turn
forward-simulation square and UNIONs the two halves into the complete single-cell LTS.

## Why the `result` predicates syntactically match `execGraph` (the load-bearing fact)

`Spec.ExecRefinement.execGraph` reconstructs the Spec authority graph from the executable cap
table, with rights abstracted to `ExecRights = Unit` (the connectivity skeleton): `h` holds a Spec
edge to `t` iff, in `caps`, `h` holds a `node t` cap or an `endpoint t`-with-`write` cap. Because
the rights carrier is `Unit`, a Spec `Cap Label ExecRights` is DETERMINED BY ITS TARGET
(`c.rights : Unit` is always `()`), so `c = ⟨t, ()⟩ ↔ c.target = t`. Hence the Spec-graph edge set
"reachable from `h` to `t`" is exactly the cap-edit's effect:

  * GRANTing `recipient` a `node t` cap makes `execGraph` hold the edge `recipient ⟶ ⟨t,()⟩` and
    NOTHING else new — `execGraph (grant …) = addEdge (execGraph …) recipient ⟨t,()⟩`, i.e.
    `Spec.Introduce.result` VERBATIM;
  * REVOKEing every `h ⟶ t`-conferring cap from `holder` removes EXACTLY the edge `holder ⟶ ⟨t,()⟩`
    — `execGraph (revokeTarget …) = removeEdge (execGraph …) holder ⟨t,()⟩`, i.e.
    `Spec.Revoke.result` VERBATIM.

These two equalities (`recKDelegate_execGraph` / `recKRevokeTarget_execGraph`) are what let the
cap-edit's abstract image BE a `Spec.AuthStep`, closing the half `Proof/LTS.lean` left as the named
missing transition.

## Discipline (REORIENT §6)
No `axiom`/`admit`/`native_decide`/`sorry`. `#assert_axioms` on every keystone. Pure, computable,
`#eval`-able. Reuses `Exec/Caps.lean`'s `grant`/`revoke` ops + `Spec.Authority`'s `addEdge`/
`removeEdge` + `Spec.ExecRefinement.execGraph`; edits nothing.
-/
import Dregg2.Exec.RecordKernel
import Dregg2.Exec.Caps
import Dregg2.Spec.ExecRefinement
import Dregg2.Spec.Authority

namespace Dregg2.Exec

open Dregg2.Authority (Caps Cap Auth Label)
open Dregg2.Spec (execGraph ExecRights addEdge removeEdge)

/-! ## §1 — The per-cap edge predicate `execGraph` reads, named.

`execGraph caps h c` is `(caps h).any (confersEdgeTo c.target) = true`. We name the per-cap
predicate so the cap-edit and the graph-change proof read against the SAME function `execGraph`
folds — this is the syntactic match the plan relies on. -/

/-- **`confersEdgeTo t cap`** — does `cap` confer (in `execGraph`'s sense) a connectivity edge to
target `t`? Exactly `execGraph`'s `.any` body with `c.target := t`: a `node t` cap, or an
`endpoint t`-carrying-`write` cap. This is the decidable per-cap test the reconstructed graph reads. -/
def confersEdgeTo (t : Label) (cap : Cap) : Bool :=
  (cap == Cap.node t) ||
  (match cap with
   | .endpoint t' rights => (t' == t) && rights.contains Auth.write
   | _ => false)

/-- `execGraph` unfolded through `confersEdgeTo`: the Spec edge `h ⟶ c` is present iff some cap in
`h`'s slot `confersEdgeTo c.target`. (A `rfl`-bridge so the graph-change proofs can rewrite against
this named predicate instead of the inlined `.any` body.) -/
theorem execGraph_eq_any (caps : Caps) (h : Label) (c : Spec.Cap Label ExecRights) :
    execGraph caps h c = ((caps h).any (fun cap => confersEdgeTo c.target cap) = true) := rfl

/-! ## §2 — `ExecRights = Unit`: a Spec cap is DETERMINED BY ITS TARGET.

The graph carrier abstracts rights to `Unit`, so `⟨t, ()⟩` is the UNIQUE Spec cap to `t`. This is
what collapses `c = ⟨t,()⟩` to `c.target = t` and makes the cap-edit's all-edges-to-`t` effect
coincide with `addEdge`/`removeEdge` of the single Spec edge `⟨t,()⟩`. -/

/-- A Spec edge over `ExecRights` is its target: `c = ⟨t, ()⟩ ↔ c.target = t` (the rights component
is `Unit`, hence always `()`). The collapse that makes `addEdge … ⟨t,()⟩` = "every edge to `t`". -/
theorem specCap_eq_iff_target (c : Spec.Cap Label ExecRights) (t : Label) :
    c = ⟨t, ()⟩ ↔ c.target = t := by
  constructor
  · intro h; rw [h]
  · intro h
    obtain ⟨ct, cr⟩ := c
    cases cr
    simp only at h
    subst h
    rfl

/-! ## §3 — `recKDelegate` — the executable GRANOVETTER DELEGATION (an authority turn).

The dual of `recKExec`: it EDITS `caps` (grants `recipient` a fresh `node t` cap — the executable
Granovetter introduce) and leaves the `cell`/balance state UNTOUCHED. Fail-closed: it gates on the
delegator already holding connectivity to `t` (`authorizedB`-style: the delegator owns `t` or holds
a cap to it), the executable form of `Introduce`'s `connected`/`holds_parent` premise — "only
connectivity begets connectivity". -/

/-- **`recKDelegate k delegator recipient t`** — the executable authority turn: the `delegator`
hands `recipient` a `node t` cap, growing the cap graph. Commits only when the delegator can already
reach `t` (owns it, or holds a `t`-conferring cap — the Granovetter connectivity premise, the same
`confersEdgeTo` test `execGraph` reads); on commit it rewrites ONLY `caps` via `Caps.grant`, leaving
every cell's record (hence every balance) intact. The conservation-trivial DUAL of `recKExec`. -/
def recKDelegate (k : RecordKernelState) (delegator recipient t : Label) :
    Option RecordKernelState :=
  -- The Granovetter connectivity premise, exactly: the delegator must already HOLD a cap conferring
  -- an edge to `t` (`execGraph caps delegator ⟨t,()⟩`). This is `Spec.Endow.holds_source` verbatim,
  -- so the committed delegation's abstract image is a genuine authorized generative act.
  if (k.caps delegator).any (fun cap => confersEdgeTo t cap) = true then
    some { k with caps := grant k.caps recipient (Cap.node t) }
  else
    none

/-! ### §3.RIGHTS — The RIGHTS-CARRYING delegation (the genuine `is_attenuation` mirror).

`recKDelegate` above grants a `node t` connectivity cap — faithful to the connectivity skeleton
but rights-blind. dregg1's `apply_introduce` does more: it looks up the introducer's HELD cap to
the target (`lookup_by_target`), checks `is_attenuation(held.permissions, granted)`
(`apply.rs:2829`, i.e. `granted ⊆ held`), and grants the recipient an attenuated copy
(`grant_with_expiry(target, permissions)`). We mirror THAT: locate the introducer's held cap to
`t`, attenuate it to `keep`, and grant the recipient the attenuated `endpoint` cap. The granted
cap's REAL conferred rights are then `⊆` the held cap's — `attenuate_confRights_le`, the genuine
`granted.rights ≤ held.rights` over the `ExecAuth` lattice, NOT a `()≤()` collapse. -/

/-- **`heldCapTo caps h t`** — the introducer's HELD cap conferring an edge to `t` (the executable
`lookup_by_target`): the first cap in `h`'s slot that `confersEdgeTo t`, or `Cap.null` if none.
This is the cap whose rights `is_attenuation` bounds the grant against. -/
def heldCapTo (caps : Caps) (h t : Label) : Cap :=
  ((caps h).find? (fun cap => confersEdgeTo t cap)).getD Cap.null

/-- **`recKDelegateAtten k delegator recipient t keep`** — the RIGHTS-CARRYING Granovetter
delegation (the faithful `apply_introduce`): on commit (the delegator holds a cap to `t`), grant
`recipient` the delegator's held cap to `t` ATTENUATED to `keep` (`attenuate keep (heldCapTo …)`).
The granted cap carries REAL rights `⊆` the held cap's (`attenuate_confRights_le`) — the executable
`is_attenuation(held, granted)`. Fail-closed: no held cap to `t` ⇒ no delegation. -/
def recKDelegateAtten (k : RecordKernelState) (delegator recipient t : Label) (keep : List Auth) :
    Option RecordKernelState :=
  if (k.caps delegator).any (fun cap => confersEdgeTo t cap) = true then
    some { k with caps := grant k.caps recipient (attenuate keep (heldCapTo k.caps delegator t)) }
  else
    none

/-- **`recKRevokeTarget k holder t`** — the executable revocation authority turn: the `holder`
drops EVERY cap conferring an edge to `t` (so its `execGraph` edge to `t` is gone — matching the
abstract single-edge `removeEdge`). Always commits (revocation needs no further authority — it only
subtracts); rewrites ONLY `caps`, leaving balances intact. -/
def recKRevokeTarget (k : RecordKernelState) (holder t : Label) : RecordKernelState :=
  { k with caps := fun l => if l = holder then (k.caps l).filter (fun cap => ¬ confersEdgeTo t cap)
                            else k.caps l }

/-! ## §4 — THE DUAL FRAME LEMMA: an authority turn preserves `recTotal` (the balance domain is FIXED).

The mirror of `recKExec_frame`'s "authority fixed": where a balance turn holds the cap table fixed,
an authority turn holds the BALANCE domain fixed. Both proved by the cap-edit touching only `caps`
(the `cell` field — hence `balOf` per cell, hence `recTotal` — is literally unchanged). -/

/-- **`recKDelegate_frame` (PROVED) — the DUAL frame.** A committed delegation preserves `recTotal`
AND `accounts` (it edits only `caps`). The balance-domain mirror of `recKExec_frame`'s authority
frame: the conserved measure is FIXED across an authority turn. -/
theorem recKDelegate_frame (k k' : RecordKernelState) (delegator recipient t : Label)
    (h : recKDelegate k delegator recipient t = some k') :
    recTotal k' = recTotal k ∧ k'.accounts = k.accounts ∧ k'.cell = k.cell := by
  unfold recKDelegate at h
  by_cases hg : (k.caps delegator).any (fun cap => confersEdgeTo t cap) = true
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨?_, rfl, rfl⟩
    -- `recTotal` reads only `accounts` and `cell`, both unchanged by the `caps`-only edit.
    rfl
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`recKRevokeTarget_frame` (PROVED) — the DUAL frame for revocation.** A target-revocation
preserves `recTotal` and `accounts` (it edits only `caps`). -/
theorem recKRevokeTarget_frame (k : RecordKernelState) (holder t : Label) :
    recTotal (recKRevokeTarget k holder t) = recTotal k ∧
      (recKRevokeTarget k holder t).accounts = k.accounts ∧
      (recKRevokeTarget k holder t).cell = k.cell := by
  -- `recKRevokeTarget` edits only `caps`; `recTotal`/`accounts`/`cell` are untouched.
  refine ⟨rfl, rfl, rfl⟩

/-- A single cap confers an edge to AT MOST ONE target: if `cap` confers an edge to both `a` and
`t`, then `a = t`. (A `node`/`endpoint` cap names exactly one target.) Used to show the revoke
filter removes precisely the edge to `t`. -/
theorem confersEdgeTo_unique (cap : Cap) (a t : Label)
    (ha : confersEdgeTo a cap = true) (ht : confersEdgeTo t cap = true) : a = t := by
  unfold confersEdgeTo at ha ht
  rw [Bool.or_eq_true] at ha ht
  cases cap with
  | null => simp at ha
  | node tn =>
      simp only [beq_iff_eq, Cap.node.injEq, reduceCtorEq, or_false] at ha ht
      rw [← ha, ← ht]
  | endpoint te re =>
      simp only [reduceCtorEq, false_or, Bool.and_eq_true, beq_iff_eq] at ha ht
      rw [← ha.1, ← ht.1]

/-! ## §5 — THE GRAPH-CHANGE LEMMA: the cap-edit IS the abstract `addEdge`/`removeEdge`.

The load-bearing match. `execGraph` of the post-state equals the abstract `Spec.addEdge`/
`Spec.removeEdge` of the SINGLE Spec edge `⟨t,()⟩` applied to `execGraph` of the pre-state. Proved
by `funext`/`propext` reducing `.any` over the edited slot, using §2's target-collapse. These are
exactly `Spec.Introduce.result` / `Spec.Revoke.result`. -/

/-- **`recKDelegate_execGraph` (PROVED) — the grant-edit IS `Spec.addEdge`.** After delegating a
`node t` cap to `recipient`, the reconstructed graph is the pre-graph with the single Spec edge
`recipient ⟶ ⟨t,()⟩` added — `Spec.Introduce`'s `result : G' = addEdge G recipient cap` VERBATIM.
The grant adds exactly the edges to target `t` from `recipient`, which (rights = `Unit`) is the one
Spec edge `⟨t,()⟩`. -/
theorem recKDelegate_execGraph (caps : Caps) (recipient t : Label) :
    execGraph (grant caps recipient (Cap.node t))
      = addEdge (execGraph caps) recipient (⟨t, ()⟩ : Spec.Cap Label ExecRights) := by
  funext h c
  -- Unfold both sides to a `Prop` equality and prove by `propext`.
  show ((grant caps recipient (Cap.node t) h).any (fun cap => confersEdgeTo c.target cap) = true)
      = (execGraph caps h c ∨ (h = recipient ∧ c = ⟨t, ()⟩))
  apply propext
  unfold grant
  by_cases hh : h = recipient
  · subst hh
    -- the edited slot: `grant` prepends `node t`; the `.any` gains the disjunct.
    rw [if_pos rfl]
    rw [execGraph_eq_any]
    simp only [List.any_cons, Bool.or_eq_true]
    constructor
    · rintro (hnode | hrest)
      · -- the new `node t` cap confers an edge iff `c.target = t`, i.e. `c = ⟨t,()⟩`.
        refine Or.inr ⟨by trivial, ?_⟩
        have ht : c.target = t := by
          have : (Cap.node t == Cap.node c.target) = true := by
            simpa [confersEdgeTo] using hnode
          have := (beq_iff_eq (a := Cap.node t) (b := Cap.node c.target)).mp this
          exact (Cap.node.injEq t c.target ▸ this).symm
        exact (specCap_eq_iff_target c t).mpr ht
      · exact Or.inl hrest
    · rintro (hpre | ⟨_, hc⟩)
      · exact Or.inr hpre
      · -- `c = ⟨t,()⟩` ⟹ `c.target = t` ⟹ the `node t` cap confers the edge.
        have ht : c.target = t := (specCap_eq_iff_target c t).mp hc
        exact Or.inl (by simp [confersEdgeTo, ht])
  · -- an untouched slot: the graph is unchanged and the added-edge disjunct is false.
    rw [if_neg hh, execGraph_eq_any]
    constructor
    · intro hpre; exact Or.inl hpre
    · rintro (hpre | ⟨heq, _⟩)
      · exact hpre
      · exact absurd heq hh

/-- **`recKRevokeTarget_execGraph` (PROVED) — the target-revoke-edit IS `Spec.removeEdge`.** After
revoking every `t`-conferring cap from `holder`, the reconstructed graph is the pre-graph with the
single Spec edge `holder ⟶ ⟨t,()⟩` removed — `Spec.Revoke`'s `result : G' = removeEdge G holder cap`
VERBATIM. The filter drops exactly the caps conferring an edge to `t`, which (rights = `Unit`) is
the one Spec edge `⟨t,()⟩`. -/
theorem recKRevokeTarget_execGraph (caps : Caps) (holder t : Label) :
    execGraph (fun l => if l = holder then (caps l).filter (fun cap => ¬ confersEdgeTo t cap)
                        else caps l)
      = removeEdge (execGraph caps) holder (⟨t, ()⟩ : Spec.Cap Label ExecRights) := by
  funext h c
  show ((if h = holder then (caps h).filter (fun cap => ¬ confersEdgeTo t cap) else caps h).any
          (fun cap => confersEdgeTo c.target cap) = true)
      = (execGraph caps h c ∧ ¬ (h = holder ∧ c = ⟨t, ()⟩))
  apply propext
  by_cases hh : h = holder
  · subst hh
    rw [if_pos rfl, execGraph_eq_any]
    -- the `.any` over the filtered list: a surviving cap confers `c.target` iff it did before AND
    -- it is not a `t`-conferring cap; but a cap conferring `c.target` is `t`-conferring iff `c.target = t`.
    constructor
    · intro hany
      -- some cap survives the filter and confers `c.target`.
      rw [List.any_eq_true] at hany
      obtain ⟨cap, hmem, hconf⟩ := hany
      rw [List.mem_filter] at hmem
      obtain ⟨hmem, hnotT⟩ := hmem
      simp only [decide_not, Bool.not_eq_true', decide_eq_false_iff_not] at hnotT
      refine ⟨?_, ?_⟩
      · -- the edge is present in the pre-graph (this surviving cap witnesses it).
        rw [List.any_eq_true]; exact ⟨cap, hmem, hconf⟩
      · -- `c ≠ ⟨t,()⟩`: else `c.target = t`, so the cap conferring `c.target` is `t`-conferring,
        -- contradicting that it survived the `¬ confersEdgeTo t` filter.
        rintro ⟨_, hc⟩
        have htc : c.target = t := (specCap_eq_iff_target c t).mp hc
        rw [htc] at hconf
        exact hnotT hconf
    · rintro ⟨hpre, hne⟩
      -- the edge is present in the pre-graph and `c.target ≠ t`.
      rw [List.any_eq_true] at hpre ⊢
      obtain ⟨cap, hmem, hconf⟩ := hpre
      refine ⟨cap, ?_, hconf⟩
      rw [List.mem_filter]
      refine ⟨hmem, ?_⟩
      -- the conferring cap is NOT `t`-conferring: else `c.target = t`, contradicting `hne`.
      simp only [decide_not, Bool.not_eq_true', decide_eq_false_iff_not]
      intro hcontra
      have htgt : c.target = t := confersEdgeTo_unique cap c.target t hconf hcontra
      exact hne ⟨rfl, (specCap_eq_iff_target c t).mpr htgt⟩
  · rw [if_neg hh, execGraph_eq_any]
    constructor
    · intro hpre; exact ⟨hpre, fun heq => absurd heq.1 hh⟩
    · intro hpre; exact hpre.1

/-! ## §6 — Granovetter grounding: the delegation gate witnesses the abstract `connected` premise.

The executable `recKDelegate` gate (the delegator holds a `t`-conferring cap) refines
`Spec.Endow`'s `holds_source` premise EXACTLY: on commit, the delegator HOLDS the Spec source edge
`delegator ⟶ ⟨t,()⟩` in `execGraph`. This is the authority-turn analog of
`exec_authz_grounds_in_graph`, and the load-bearing content ("only connectivity begets
connectivity") that makes the delegation an AUTHORIZED generative act. -/

/-- **`recKDelegate_grounds` (PROVED)** — a committed delegation HOLDS the abstract source edge: the
delegator holds the Spec edge `delegator ⟶ ⟨t,()⟩` on `execGraph`. This is exactly
`Spec.Endow.holds_source` (and witnesses `Graph.has delegator t`). The executable Granovetter
connectivity premise, refined onto the Spec graph. -/
theorem recKDelegate_grounds (k k' : RecordKernelState) (delegator recipient t : Label)
    (h : recKDelegate k delegator recipient t = some k') :
    execGraph k.caps delegator (⟨t, ()⟩ : Spec.Cap Label ExecRights) := by
  unfold recKDelegate at h
  by_cases hg : (k.caps delegator).any (fun cap => confersEdgeTo t cap) = true
  · -- a held `t`-conferring cap IS the Spec source edge `delegator ⟶ ⟨t,()⟩`.
    rw [execGraph_eq_any]; exact hg
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ### §6.RIGHTS — the rights-delegation grounds in a GENUINELY-HELD cap, and ATTENUATES it.

The faithful `apply_introduce` content: when `recKDelegateAtten` commits, (a) the held cap
`heldCapTo` it attenuates against is genuinely IN the delegator's slot and confers an edge to `t`
(the executable `lookup_by_target` succeeds), and (b) the granted cap's REAL conferred rights are
`⊆` that held cap's — `is_attenuation(held, granted)` over the `ExecAuth` lattice. This is the
de-vacuified non-amplification: granted-vs-HELD (two different caps), not a cap vs itself. -/

/-- **`heldCapTo_mem` (PROVED)** — when the delegator holds *some* cap conferring an edge to `t`,
`heldCapTo` returns an actual member of its slot that `confersEdgeTo t`. The executable
`lookup_by_target` succeeds and names a genuinely-held cap (the introducer's own authority to the
target — the `held_cap` of `apply.rs:2817`). -/
theorem heldCapTo_mem (caps : Caps) (delegator t : Label)
    (hg : (caps delegator).any (fun cap => confersEdgeTo t cap) = true) :
    heldCapTo caps delegator t ∈ caps delegator
      ∧ confersEdgeTo t (heldCapTo caps delegator t) = true := by
  unfold heldCapTo
  rw [List.any_eq_true] at hg
  obtain ⟨c, hmem, hconf⟩ := hg
  -- `find?` with a satisfied predicate returns `some`, and the result satisfies the predicate.
  cases hfind : (caps delegator).find? (fun cap => confersEdgeTo t cap) with
  | none =>
      -- impossible: `c` satisfies the predicate, so `find?` cannot be `none`.
      rw [List.find?_eq_none] at hfind
      exact absurd hconf (by simpa using hfind c hmem)
  | some d =>
      simp only [Option.getD_some]
      exact ⟨List.mem_of_find?_eq_some hfind, List.find?_some hfind⟩

/-- **`recKDelegateAtten_non_amplifying` (PROVED) — THE de-vacuified HEADLINE.** A committed
rights-delegation grants `recipient` a cap whose REAL conferred authority is `⊆` the introducer's
HELD cap to the target: `confRights granted ≤ confRights held`, where `granted := attenuate keep
(heldCapTo …)` is the recipient's NEW cap and `held := heldCapTo …` is the introducer's EXISTING
cap. This is `is_attenuation(held, granted)` (`apply.rs:2829`) over the `ExecAuth` lattice — the
genuine granted-vs-held inequality, proved via `attenuate_confRights_le`, NOT `le_refl` self-vs-self.
The recipient cannot exert any authority the introducer could not. -/
theorem recKDelegateAtten_non_amplifying (caps : Caps) (delegator t : Label) (keep : List Auth) :
    confRights (attenuate keep (heldCapTo caps delegator t))
      ≤ confRights (heldCapTo caps delegator t) :=
  attenuate_confRights_le keep (heldCapTo caps delegator t)

/-- **`recKDelegateAtten_grants` (PROVED)** — on commit, the recipient genuinely HOLDS the granted
(attenuated) cap in its slot, and the granted cap is exactly `attenuate keep` of the held cap. The
executable `grant_with_expiry` landed the attenuated permission. -/
theorem recKDelegateAtten_grants (k k' : RecordKernelState) (delegator recipient t : Label)
    (keep : List Auth) (h : recKDelegateAtten k delegator recipient t keep = some k') :
    attenuate keep (heldCapTo k.caps delegator t) ∈ k'.caps recipient := by
  unfold recKDelegateAtten at h
  by_cases hg : (k.caps delegator).any (fun cap => confersEdgeTo t cap) = true
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
    exact grant_adds k.caps recipient (attenuate keep (heldCapTo k.caps delegator t))
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`recKDelegateAtten_frame` (PROVED)** — the rights-delegation is conservation-trivial: it edits
only `caps`, so `recTotal`/`accounts`/`cell` are FIXED (the dual frame, mirroring
`recKDelegate_frame`). -/
theorem recKDelegateAtten_frame (k k' : RecordKernelState) (delegator recipient t : Label)
    (keep : List Auth) (h : recKDelegateAtten k delegator recipient t keep = some k') :
    recTotal k' = recTotal k ∧ k'.accounts = k.accounts ∧ k'.cell = k.cell := by
  unfold recKDelegateAtten at h
  by_cases hg : (k.caps delegator).any (fun cap => confersEdgeTo t cap) = true
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, rfl⟩
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`recKDelegateAtten_grounds` (PROVED)** — a committed rights-delegation HOLDS the abstract
source edge (`delegator ⟶ ⟨t,()⟩` on the connectivity `execGraph`): the introducer could already
reach `t`. The Granovetter connectivity premise, unchanged by the rights refinement. -/
theorem recKDelegateAtten_grounds (k k' : RecordKernelState) (delegator recipient t : Label)
    (keep : List Auth) (h : recKDelegateAtten k delegator recipient t keep = some k') :
    execGraph k.caps delegator (⟨t, ()⟩ : Spec.Cap Label ExecRights) := by
  unfold recKDelegateAtten at h
  by_cases hg : (k.caps delegator).any (fun cap => confersEdgeTo t cap) = true
  · rw [execGraph_eq_any]; exact hg
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## §7 — Axiom-hygiene tripwires (the CLOSED keystones).

The dual frame, the graph-change `addEdge`/`removeEdge` matches, and the grounding lemma are all
PROVED-clean. Pinning certifies the authority-mutating executable transition exists and its abstract
image IS a `Spec.AuthStep` edit — closing the named missing transition `Proof/LTS.lean §7` flagged. -/

#assert_axioms recKDelegate_frame
#assert_axioms recKRevokeTarget_frame
#assert_axioms recKDelegate_execGraph
#assert_axioms recKRevokeTarget_execGraph
#assert_axioms recKDelegate_grounds
#assert_axioms confersEdgeTo_unique
#assert_axioms specCap_eq_iff_target
#assert_axioms heldCapTo_mem
#assert_axioms recKDelegateAtten_non_amplifying
#assert_axioms recKDelegateAtten_grants
#assert_axioms recKDelegateAtten_frame
#assert_axioms recKDelegateAtten_grounds

/-! ## §8 — It runs (`#eval`). -/

/-- A record state where delegator 0 HOLDS a `node 7` cap (so it can delegate connectivity to 7). -/
def rsCap : RecordKernelState :=
  { rs0 with caps := fun l => if l = 0 then [Cap.node 7] else [] }

-- Delegator 0 holds a cap to target 7; delegates connectivity to 7 to recipient 1. Commits.
#eval (recKDelegate rsCap 0 1 7).isSome   -- true (delegator 0 holds a `node 7` cap)
-- A delegator with no connectivity to the target cannot delegate it:
#eval (recKDelegate rsCap 5 1 9).isSome   -- false (5 holds no cap conferring an edge to 9)
-- After delegation, recipient 1 holds the `node 7` cap (the new edge to 7):
#eval ((recKDelegate rsCap 0 1 7).map (fun k => k.caps 1)).getD []   -- [Cap.node 7]
-- Revocation always commits (it only subtracts): revoking 7 from 0 empties its slot.
#eval ((recKRevokeTarget rsCap 0 7).caps 0)  -- [] (the `node 7` cap is filtered out)

end Dregg2.Exec
