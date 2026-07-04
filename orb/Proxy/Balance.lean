/-
Balance — the load-balancer selection algebra.

Composition, outside-in:

  candidates ──filter eligible──▶ eligible set
             ──restrict to best tier──▶ tier pool (primary, else 1st backup, …)
             ──policy──▶ chosen backend      (`select`)
  policies A else B else C                   (`selectChain`)

`eligible` = probe-healthy AND administratively active (draining and down are
both excluded from NEW selection). The tier pool is the eligible subset of the
lowest-numbered tier that has any eligible member: primaries while any primary
is usable, first backup tier only when no primary is, and so on. Policies
never see an ineligible backend, which is what makes the two soundness
theorems one-liners *by construction*:

  * `select_eligible`   — a chosen backend is always eligible; a healthy
    backend can never lose to an unhealthy one because unhealthy backends are
    not in the candidate pool at all;
  * `select_best_tier`  — the chosen backend always sits in the healthiest
    (lowest-numbered) nonempty tier: backups are used exactly when every
    primary is out.

Totality (`select_*_total`): whenever ANY eligible backend exists, selection
succeeds — for weighted round-robin under the config-checked side condition
that weights are positive.

A policy chain `A else B else C` returns the first policy's verdict that is
`some`; `selectChain_none_iff` pins the failure case (every link failed) and
`selectChain_sound` shows the chain inherits both soundness theorems.

The per-policy machinery and its deeper theorems live in `Proxy.Wrr`
(exact window fairness) and `Proxy.Rendezvous` (minimal disruption); this
file re-exports their guarantees at the tiered-selector level
(`select_wrr_fair`, `select_hash_minimal_disruption`).
-/

import Proxy.Basic
import Proxy.Wrr
import Proxy.Rendezvous

namespace Proxy

/-! ### Least-connections -/

/-- Pick the eligible backend with the fewest in-flight connections; ties go
to the earlier list position. -/
def leastConn : List Backend → Option Backend
  | [] => none
  | b :: bs =>
    match leastConn bs with
    | none => some b
    | some c => if b.conns ≤ c.conns then some b else some c

theorem leastConn_total {bs : List Backend} (h : bs ≠ []) :
    (leastConn bs).isSome := by
  cases bs with
  | nil => exact absurd rfl h
  | cons b rest =>
    cases hr : leastConn rest with
    | none => simp [leastConn, hr]
    | some c => by_cases hb : b.conns ≤ c.conns <;> simp [leastConn, hr, hb]

theorem leastConn_mem {bs : List Backend} {b : Backend}
    (h : leastConn bs = some b) : b ∈ bs := by
  induction bs generalizing b with
  | nil => cases h
  | cons c rest ih =>
    cases hr : leastConn rest with
    | none =>
      simp only [leastConn, hr] at h
      cases h
      exact List.mem_cons_self c rest
    | some w =>
      simp only [leastConn, hr] at h
      split at h
      · cases h; exact List.mem_cons_self c rest
      · cases h; exact List.mem_cons_of_mem _ (ih hr)

/-- The chosen backend has minimal in-flight count over the candidate list. -/
theorem leastConn_min {bs : List Backend} {b : Backend}
    (h : leastConn bs = some b) : ∀ c ∈ bs, b.conns ≤ c.conns := by
  induction bs generalizing b with
  | nil => cases h
  | cons a rest ih =>
    intro c hc
    cases hr : leastConn rest with
    | none =>
      have hrest : rest = [] := by
        cases rest with
        | nil => rfl
        | cons x xs =>
          have := leastConn_total (bs := x :: xs) (by intro hx; cases hx)
          rw [hr] at this
          cases this
      simp only [leastConn, hr] at h
      cases h
      rcases List.mem_cons.mp hc with hc' | hc'
      · rw [hc']; exact Nat.le_refl _
      · rw [hrest] at hc'; cases hc'
    | some w =>
      simp only [leastConn, hr] at h
      split at h
      · rename_i hle
        cases h
        rcases List.mem_cons.mp hc with hc' | hc'
        · rw [hc']; exact Nat.le_refl _
        · exact Nat.le_trans hle (ih hr c hc')
      · rename_i hgt
        cases h
        rcases List.mem_cons.mp hc with hc' | hc'
        · rw [hc']; omega
        · exact ih hr c hc'

/-! ### Eligibility and tiers -/

/-- The eligible (healthy ∧ active) subset. -/
def eligibleOf (bs : List Backend) : List Backend :=
  bs.filter Backend.eligible

theorem mem_eligibleOf {bs : List Backend} {b : Backend} :
    b ∈ eligibleOf bs ↔ b ∈ bs ∧ b.eligible = true := List.mem_filter

/-- Lowest tier number present in a list (`none` on empty). -/
def minTier : List Backend → Option Nat
  | [] => none
  | b :: bs =>
    match minTier bs with
    | none => some b.tier
    | some t => some (Nat.min b.tier t)

theorem minTier_le {bs : List Backend} {t : Nat} (h : minTier bs = some t) :
    ∀ b ∈ bs, t ≤ b.tier := by
  induction bs generalizing t with
  | nil => cases h
  | cons a rest ih =>
    intro b hb
    cases hr : minTier rest with
    | none =>
      have hrest : rest = [] := by
        cases rest with
        | nil => rfl
        | cons x xs => simp only [minTier] at hr; split at hr <;> cases hr
      simp only [minTier, hr] at h
      cases h
      rcases List.mem_cons.mp hb with hb' | hb'
      · rw [hb']; exact Nat.le_refl _
      · rw [hrest] at hb'; cases hb'
    | some t' =>
      simp only [minTier, hr] at h
      cases h
      rcases List.mem_cons.mp hb with hb' | hb'
      · rw [hb']; exact Nat.min_le_left ..
      · exact Nat.le_trans (Nat.min_le_right ..) (ih hr b hb')

theorem minTier_mem {bs : List Backend} {t : Nat} (h : minTier bs = some t) :
    ∃ b ∈ bs, b.tier = t := by
  induction bs generalizing t with
  | nil => cases h
  | cons a rest ih =>
    cases hr : minTier rest with
    | none =>
      simp only [minTier, hr] at h
      cases h
      exact ⟨a, List.mem_cons_self a rest, rfl⟩
    | some t' =>
      simp only [minTier, hr] at h
      cases h
      by_cases hmin : a.tier ≤ t'
      · exact ⟨a, List.mem_cons_self a rest, (Nat.min_eq_left hmin).symm⟩
      · obtain ⟨b, hb, hbt⟩ := ih hr
        refine ⟨b, List.mem_cons_of_mem _ hb, ?_⟩
        rw [hbt]
        exact (Nat.min_eq_right (by omega)).symm

theorem minTier_total {bs : List Backend} (h : bs ≠ []) :
    (minTier bs).isSome := by
  cases bs with
  | nil => exact absurd rfl h
  | cons b rest =>
    cases hr : minTier rest with
    | none => simp [minTier, hr]
    | some t => simp [minTier, hr]

/-- The healthiest nonempty tier's number: least tier among eligible
backends. -/
def bestTier (bs : List Backend) : Option Nat :=
  minTier (eligibleOf bs)

/-- The candidate pool policies run on: eligible backends of the best tier. -/
def tierPool (bs : List Backend) : List Backend :=
  match bestTier bs with
  | none => []
  | some t => (eligibleOf bs).filter (fun b => b.tier == t)

/-- Everything in the tier pool is an eligible member of the original list
sitting at the best tier. -/
theorem tierPool_spec {bs : List Backend} {b : Backend}
    (h : b ∈ tierPool bs) :
    b ∈ bs ∧ b.eligible = true ∧ bestTier bs = some b.tier := by
  unfold tierPool at h
  cases ht : bestTier bs with
  | none => rw [ht] at h; cases h
  | some t =>
    rw [ht] at h
    have := List.mem_filter.mp h
    have hmem := mem_eligibleOf.mp this.1
    have htier : b.tier = t := by simpa using this.2
    exact ⟨hmem.1, hmem.2, by rw [htier]⟩

/-- If any eligible backend exists, the tier pool is nonempty. -/
theorem tierPool_ne_nil {bs : List Backend} {w : Backend}
    (hmem : w ∈ bs) (helig : w.eligible = true) : tierPool bs ≠ [] := by
  have hw : w ∈ eligibleOf bs := mem_eligibleOf.mpr ⟨hmem, helig⟩
  have hne : eligibleOf bs ≠ [] := by
    intro hnil; rw [hnil] at hw; cases hw
  have hbt := minTier_total hne
  unfold tierPool bestTier
  cases ht : minTier (eligibleOf bs) with
  | none => rw [ht] at hbt; cases hbt
  | some t =>
    obtain ⟨b, hb, hbt'⟩ := minTier_mem ht
    show (eligibleOf bs).filter (fun b => b.tier == t) ≠ []
    intro hnil
    have : b ∈ (eligibleOf bs).filter (fun b => b.tier == t) :=
      List.mem_filter.mpr ⟨hb, by simp [hbt']⟩
    rw [hnil] at this
    cases this

/-- The tier pool keeps distinct ids distinct (it is a sublist). -/
theorem tierPool_idsNodup {bs : List Backend} (hnd : idsNodup bs) :
    idsNodup (tierPool bs) := by
  unfold tierPool bestTier eligibleOf
  cases minTier (bs.filter Backend.eligible) with
  | none => simp [idsNodup]
  | some t =>
    apply List.Nodup.sublist ?_ hnd
    apply List.Sublist.map
    exact List.Sublist.trans (List.filter_sublist _) (List.filter_sublist _)

/-! ### Policies and the tiered selector -/

/-- The selection policies. The hash function for `rendezvousHash` and the
request key / round counter travel in `Ctx`. -/
inductive Policy where
  /-- Weighted round-robin over the tier pool (`Proxy.Wrr`). -/
  | weightedRoundRobin
  /-- Fewest in-flight connections, earlier position wins ties. -/
  | leastConnections
  /-- Rendezvous hashing on the request key (`Proxy.Rendezvous`). -/
  | rendezvousHash
deriving DecidableEq, Repr

/-- Per-request selection context: the shard-local round counter, the
affinity key (client address / cookie / header hash), and the hash function
used by `rendezvousHash`. -/
structure Ctx where
  round : Nat
  key : Nat
  hash : Nat → Nat → Nat

def applyPolicy : Policy → Ctx → List Backend → Option Backend
  | .weightedRoundRobin, ctx, bs => wrr bs ctx.round
  | .leastConnections, _, bs => leastConn bs
  | .rendezvousHash, ctx, bs => rendezvous ctx.hash ctx.key bs

theorem applyPolicy_mem {p : Policy} {ctx : Ctx} {bs : List Backend}
    {b : Backend} (h : applyPolicy p ctx bs = some b) : b ∈ bs := by
  cases p with
  | weightedRoundRobin => exact wrr_mem h
  | leastConnections => exact leastConn_mem h
  | rendezvousHash => exact rendezvous_mem h

/-- The tiered selector: run the policy on the best-tier eligible pool. -/
def select (p : Policy) (ctx : Ctx) (bs : List Backend) : Option Backend :=
  applyPolicy p ctx (tierPool bs)

/-- **Fallback soundness, part 1.** A selected backend is always eligible —
a healthy backend can never be passed over in favor of an unhealthy one,
because ineligible backends are not candidates at all. -/
theorem select_eligible {p : Policy} {ctx : Ctx} {bs : List Backend}
    {b : Backend} (h : select p ctx bs = some b) :
    b ∈ bs ∧ b.eligible = true :=
  let spec := tierPool_spec (applyPolicy_mem h)
  ⟨spec.1, spec.2.1⟩

/-- **Fallback soundness, part 2.** A selected backend always lives in the
healthiest (lowest-numbered) tier that has any eligible member: primaries are
never skipped for backups, and backups engage exactly when no primary is
eligible. -/
theorem select_best_tier {p : Policy} {ctx : Ctx} {bs : List Backend}
    {b : Backend} (h : select p ctx bs = some b) :
    bestTier bs = some b.tier ∧ ∀ c ∈ bs, c.eligible = true → b.tier ≤ c.tier := by
  have spec := tierPool_spec (applyPolicy_mem h)
  refine ⟨spec.2.2, fun c hc hcelig => ?_⟩
  exact minTier_le spec.2.2 c (mem_eligibleOf.mpr ⟨hc, hcelig⟩)

/-- Selection totality, least-connections: an eligible backend exists ⇒ a
backend is chosen. -/
theorem select_leastConn_total {ctx : Ctx} {bs : List Backend} {w : Backend}
    (hmem : w ∈ bs) (helig : w.eligible = true) :
    (select .leastConnections ctx bs).isSome :=
  leastConn_total (tierPool_ne_nil hmem helig)

/-- Selection totality, rendezvous hashing. -/
theorem select_hash_total {ctx : Ctx} {bs : List Backend} {w : Backend}
    (hmem : w ∈ bs) (helig : w.eligible = true) :
    (select .rendezvousHash ctx bs).isSome :=
  rendezvous_total (tierPool_ne_nil hmem helig)

/-- Selection totality, weighted round-robin — under the config-checked side
condition that every weight is positive (the loader normalizes weight 0 to 1;
a zero-weight backend is otherwise permanently starved *and*, if all weights
hit zero, unselectable). -/
theorem select_wrr_total {ctx : Ctx} {bs : List Backend} {w : Backend}
    (hmem : w ∈ bs) (helig : w.eligible = true)
    (hw : ∀ b ∈ bs, 0 < b.weight) :
    (select .weightedRoundRobin ctx bs).isSome := by
  have hne := tierPool_ne_nil hmem helig
  cases hpool : tierPool bs with
  | nil => exact absurd hpool hne
  | cons c rest =>
    have hcmem : c ∈ tierPool bs := by
      rw [hpool]; exact List.mem_cons_self c rest
    have hc : 0 < c.weight := hw c (tierPool_spec hcmem).1
    have : 0 < totalWeight (tierPool bs) :=
      totalWeight_pos hcmem hc
    exact wrr_total this ctx.round

/-! ### Policy chains: A else B else C -/

/-- First-match fallback across policies: try each in order, return the first
verdict. (Distinct from *tier* fallback, which is inside every `select`.) -/
def selectChain (ps : List Policy) (ctx : Ctx) (bs : List Backend) :
    Option Backend :=
  match ps with
  | [] => none
  | p :: rest =>
    match select p ctx bs with
    | some b => some b
    | none => selectChain rest ctx bs

/-- The chain fails only if every link fails. -/
theorem selectChain_none_iff {ps : List Policy} {ctx : Ctx}
    {bs : List Backend} :
    selectChain ps ctx bs = none ↔ ∀ p ∈ ps, select p ctx bs = none := by
  induction ps with
  | nil => simp [selectChain]
  | cons p rest ih =>
    cases hp : select p ctx bs with
    | none =>
      simp only [selectChain, hp, ih]
      constructor
      · intro h q hq
        rcases List.mem_cons.mp hq with hq' | hq'
        · rw [hq']; exact hp
        · exact h q hq'
      · intro h q hq
        exact h q (List.mem_cons_of_mem _ hq)
    | some b =>
      simp only [selectChain, hp]
      constructor
      · intro h; cases h
      · intro h
        have := h p (List.mem_cons_self p rest)
        rw [hp] at this
        cases this

/-- Chain soundness: a chain verdict is some link's verdict, so it inherits
eligibility and best-tier soundness. -/
theorem selectChain_sound {ps : List Policy} {ctx : Ctx} {bs : List Backend}
    {b : Backend} (h : selectChain ps ctx bs = some b) :
    ∃ p ∈ ps, select p ctx bs = some b := by
  induction ps with
  | nil => cases h
  | cons p rest ih =>
    cases hp : select p ctx bs with
    | none =>
      simp only [selectChain, hp] at h
      obtain ⟨q, hq, hsel⟩ := ih h
      exact ⟨q, List.mem_cons_of_mem _ hq, hsel⟩
    | some c =>
      simp only [selectChain, hp] at h
      cases h
      exact ⟨p, List.mem_cons_self p rest, hp⟩

/-- Chain verdicts are eligible members of the healthiest nonempty tier. -/
theorem selectChain_eligible {ps : List Policy} {ctx : Ctx}
    {bs : List Backend} {b : Backend} (h : selectChain ps ctx bs = some b) :
    b ∈ bs ∧ b.eligible = true ∧ bestTier bs = some b.tier := by
  obtain ⟨p, _, hsel⟩ := selectChain_sound h
  exact ⟨(select_eligible hsel).1, (select_eligible hsel).2,
    (select_best_tier hsel).1⟩

/-- Chain totality: one total link suffices. -/
theorem selectChain_total {ps : List Policy} {ctx : Ctx} {bs : List Backend}
    {p : Policy} (hp : p ∈ ps) (h : (select p ctx bs).isSome) :
    (selectChain ps ctx bs).isSome := by
  induction ps with
  | nil => cases hp
  | cons q rest ih =>
    cases hq : select q ctx bs with
    | some c => simp [selectChain, hq]
    | none =>
      simp only [selectChain, hq]
      rcases List.mem_cons.mp hp with hp' | hp'
      · rw [hp'] at h; rw [hq] at h; cases h
      · exact ih hp'

/-! ### Inherited per-policy guarantees, at the selector level -/

/-- **Weighted-RR fairness through the tiered selector.** Hold the backend
list (health, weights, tiers) fixed and let the round counter run: over any
window of `totalWeight (tierPool bs)` consecutive rounds, each pool member is
selected exactly its weight's worth of times. -/
theorem select_wrr_fair {bs : List Backend} {b : Backend} (hnd : idsNodup bs)
    (hb : b ∈ tierPool bs) (key : Nat) (hash : Nat → Nat → Nat)
    (start : Nat) :
    cnt (fun j => decide
        (select .weightedRoundRobin ⟨start + j, key, hash⟩ bs = some b))
      (totalWeight (tierPool bs)) = b.weight :=
  wrr_window_weight (tierPool_idsNodup hnd) hb start

/-- **Minimal disruption through the tiered selector.** If the eligible set
shrinks (or tiers shift) such that the new tier pool is a sub-collection of
the old one, every key whose backend survived keeps its backend. -/
theorem select_hash_minimal_disruption {bs bs' : List Backend} {b : Backend}
    {ctx : Ctx} (hnd : idsNodup bs) (hnd' : idsNodup bs')
    (hsub : ∀ c ∈ tierPool bs', c ∈ tierPool bs)
    (hsel : select .rendezvousHash ctx bs = some b)
    (hb' : b ∈ tierPool bs') :
    select .rendezvousHash ctx bs' = some b :=
  rendezvous_minimal_disruption (tierPool_idsNodup hnd)
    (tierPool_idsNodup hnd') hsub hsel hb'

end Proxy
