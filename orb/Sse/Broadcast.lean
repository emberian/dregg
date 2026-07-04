/-
# The SSE broadcaster — fan-out delivery accounting

A broadcaster owns a dynamic set of subscribers and a monotone sequence of
published events. Its behaviour is driven by a trace of operations
(`subscribe` / `unsubscribe` / `publish`). Two derived objects are read off a
trace:

* `published ops` — the global event stream, each event tagged with its
  sequence number `0, 1, 2, …` (the monotone id the resumption layer keys on).
* `delivered c ops` — the delivery log observed by subscriber `c`: the tagged
  events fanned out to `c` while it was subscribed.

The theorems are the delivery accounting:

* `subs_nodup` — the subscriber set stays a finite `Nodup` list.
* `delivered_sublist_published` — a subscriber's delivery log is an
  order-preserving **subsequence** of the global stream (soundness: only real
  events, never reordered, never duplicated).
* `published_map_fst` / `published_pairwise` — the sequence numbers are exactly
  `0, 1, …` and strictly increasing (the **monotone** event sequence).
* `deliveredAux_complete` / `delivered_split` — while a subscriber is
  continuously subscribed it receives **every** published event, in order, with
  no gap after its subscribe point (**fan-out faithfulness**).
* `unsub_not_mem` / `publish_not_subscribed_no_deliver` — an unsubscribed client
  receives no further events (**well-behaved unsubscribe**).
-/
import Sse.Basic

namespace Sse

/-- A broadcaster operation. -/
inductive Op where
  /-- A client joins the subscriber set. -/
  | subscribe (c : SubId)
  /-- A client leaves the subscriber set. -/
  | unsubscribe (c : SubId)
  /-- An event is published (fanned out to the current subscribers). -/
  | publish (e : Event)
deriving Repr, DecidableEq

/-! ## The subscriber set -/

/-- Add a subscriber, keeping the set duplicate-free. -/
def addSub (s : List SubId) (c : SubId) : List SubId :=
  if c ∈ s then s else c :: s

/-- Remove a subscriber (every occurrence — a `Nodup` set has at most one). -/
def removeSub (s : List SubId) (c : SubId) : List SubId :=
  s.filter (fun x => decide (x ≠ c))

/-- The subscriber set after a trace, from an initial set. -/
def subsAux (s : List SubId) : List Op → List SubId
  | [] => s
  | .subscribe c :: ops => subsAux (addSub s c) ops
  | .unsubscribe c :: ops => subsAux (removeSub s c) ops
  | .publish _ :: ops => subsAux s ops

/-- The subscriber set after a trace, from empty. -/
def subs (ops : List Op) : List SubId := subsAux [] ops

/-- `removeSub` never leaves `c` behind. -/
theorem unsub_not_mem (s : List SubId) (c : SubId) : c ∉ removeSub s c := by
  simp [removeSub, List.mem_filter]

/-- `removeSub` keeps a member other than the removed one. -/
theorem mem_removeSub {s : List SubId} {c d : SubId} (h : d ∈ s) (hne : d ≠ c) :
    d ∈ removeSub s c := by
  simp only [removeSub, List.mem_filter, decide_eq_true_eq]; exact ⟨h, hne⟩

/-- `addSub` keeps an already-present member, and always keeps `c`. -/
theorem mem_addSub_self (s : List SubId) (c : SubId) : c ∈ addSub s c := by
  unfold addSub; split
  · assumption
  · exact List.mem_cons_self _ _

theorem mem_addSub_of_mem {s : List SubId} {c d : SubId} (h : d ∈ s) :
    d ∈ addSub s c := by
  unfold addSub; split
  · exact h
  · exact List.mem_cons_of_mem _ h

/-- **Duplicate-free subscriber set.** The subscriber set stays `Nodup` under
every trace, from any `Nodup` start. -/
theorem subsAux_nodup (s : List SubId) (ops : List Op) (h : s.Nodup) :
    (subsAux s ops).Nodup := by
  induction ops generalizing s with
  | nil => exact h
  | cons op ops ih =>
    cases op with
    | subscribe c =>
      refine ih (addSub s c) ?_
      unfold addSub; split
      · exact h
      · rename_i hc; exact List.nodup_cons.mpr ⟨hc, h⟩
    | unsubscribe c =>
      exact ih (removeSub s c) ((List.filter_sublist s).nodup h)
    | publish e => exact ih s h

/-- The subscriber set from empty is `Nodup`. -/
theorem subs_nodup (ops : List Op) : (subs ops).Nodup :=
  subsAux_nodup [] ops List.nodup_nil

/-! ## The published stream (monotone sequence) -/

/-- The published events with their sequence numbers, starting the counter at
`next`. Each publish takes the next number and increments; subscribe/unsubscribe
do not advance the sequence. -/
def publishedAux (next : Nat) : List Op → List (Nat × Event)
  | [] => []
  | .publish e :: ops => (next, e) :: publishedAux (next + 1) ops
  | .subscribe _ :: ops => publishedAux next ops
  | .unsubscribe _ :: ops => publishedAux next ops

/-- The global published stream (sequence numbers from `0`). -/
def published (ops : List Op) : List (Nat × Event) := publishedAux 0 ops

/-- The number of publish operations in a trace. -/
def numPub : List Op → Nat
  | [] => 0
  | .publish _ :: ops => numPub ops + 1
  | .subscribe _ :: ops => numPub ops
  | .unsubscribe _ :: ops => numPub ops

theorem publishedAux_length (next : Nat) (ops : List Op) :
    (publishedAux next ops).length = numPub ops := by
  induction ops generalizing next with
  | nil => rfl
  | cons op ops ih => cases op <;> simp [publishedAux, numPub, ih]

/-- **The sequence numbers are `next, next+1, …`.** The published stream's ids
are exactly the contiguous run `List.range' next (numPub ops)`. -/
theorem publishedAux_map_fst (next : Nat) (ops : List Op) :
    (publishedAux next ops).map Prod.fst = List.range' next (numPub ops) := by
  induction ops generalizing next with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | publish e =>
      simp only [publishedAux, numPub, List.map_cons, ih (next + 1)]
      rw [List.range'_succ]
    | subscribe c => simpa [publishedAux, numPub] using ih next
    | unsubscribe c => simpa [publishedAux, numPub] using ih next

theorem published_map_fst (ops : List Op) :
    (published ops).map Prod.fst = List.range' 0 (numPub ops) :=
  publishedAux_map_fst 0 ops

/-- Every published sequence number is at least the starting counter. -/
theorem publishedAux_fst_ge (next : Nat) (ops : List Op) :
    ∀ p ∈ publishedAux next ops, next ≤ p.1 := by
  induction ops generalizing next with
  | nil => intro p hp; simp [publishedAux] at hp
  | cons op ops ih =>
    cases op with
    | publish e =>
      intro p hp
      simp only [publishedAux, List.mem_cons] at hp
      rcases hp with h | h
      · subst h; exact Nat.le_refl _
      · exact Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self next) (ih (next + 1) p h))
    | subscribe c => intro p hp; exact ih next p (by simpa [publishedAux] using hp)
    | unsubscribe c => intro p hp; exact ih next p (by simpa [publishedAux] using hp)

/-- **Strictly-monotone sequence.** The published ids are strictly increasing —
no reordering, no repeats. -/
theorem publishedAux_pairwise (next : Nat) (ops : List Op) :
    (publishedAux next ops).Pairwise (fun a b => a.1 < b.1) := by
  induction ops generalizing next with
  | nil => exact List.Pairwise.nil
  | cons op ops ih =>
    cases op with
    | publish e =>
      simp only [publishedAux]
      refine List.pairwise_cons.mpr ⟨?_, ih (next + 1)⟩
      intro q hq
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self next) (publishedAux_fst_ge (next + 1) ops q hq)
    | subscribe c => simpa [publishedAux] using ih next
    | unsubscribe c => simpa [publishedAux] using ih next

theorem published_pairwise (ops : List Op) :
    (published ops).Pairwise (fun a b => a.1 < b.1) :=
  publishedAux_pairwise 0 ops

/-! ## Delivery -/

/-- The broadcaster's observable state during a run: the current subscriber set
and the next sequence number. -/
structure BState where
  subs : List SubId
  next : Nat

def BState.init : BState := ⟨[], 0⟩

/-- The state after replaying a trace from `st`. -/
def runB (st : BState) : List Op → BState
  | [] => st
  | .subscribe c :: ops => runB { st with subs := addSub st.subs c } ops
  | .unsubscribe c :: ops => runB { st with subs := removeSub st.subs c } ops
  | .publish _ :: ops => runB { st with next := st.next + 1 } ops

/-- The delivery log fanned out to `c` over a trace, from state `st`: each
publish that occurs while `c` is subscribed appends `(seq, event)`. -/
def deliveredAux (c : SubId) (st : BState) : List Op → List (Nat × Event)
  | [] => []
  | .subscribe d :: ops => deliveredAux c { st with subs := addSub st.subs d } ops
  | .unsubscribe d :: ops => deliveredAux c { st with subs := removeSub st.subs d } ops
  | .publish e :: ops =>
      let rest := deliveredAux c { st with next := st.next + 1 } ops
      if c ∈ st.subs then (st.next, e) :: rest else rest

/-- The delivery log for `c` over a whole trace (from the initial state). -/
def delivered (c : SubId) (ops : List Op) : List (Nat × Event) :=
  deliveredAux c BState.init ops

/-- **Fan-out soundness (subsequence).** A subscriber's delivery log is an
order-preserving subsequence of the global published stream: every delivered
event was published, deliveries keep publish order, and none is duplicated
(the seq tags coincide because both count publishes the same way). -/
theorem deliveredAux_sublist_publishedAux (c : SubId) (s : List SubId) (next : Nat)
    (ops : List Op) :
    (deliveredAux c ⟨s, next⟩ ops).Sublist (publishedAux next ops) := by
  induction ops generalizing s next with
  | nil => exact List.Sublist.refl _
  | cons op ops ih =>
    cases op with
    | subscribe d => exact ih (addSub s d) next
    | unsubscribe d => exact ih (removeSub s d) next
    | publish e =>
      simp only [deliveredAux, publishedAux]
      by_cases hc : c ∈ s
      · rw [if_pos hc]; exact (ih s (next + 1)).cons₂ (next, e)
      · rw [if_neg hc]; exact (ih s (next + 1)).cons (next, e)

theorem delivered_sublist_published (c : SubId) (ops : List Op) :
    (delivered c ops).Sublist (published ops) :=
  deliveredAux_sublist_publishedAux c [] 0 ops

/-- Delivery logs inherit strict monotonicity of ids from the published stream:
no delivered event is out of order or repeated. -/
theorem delivered_pairwise (c : SubId) (ops : List Op) :
    (delivered c ops).Pairwise (fun a b => a.1 < b.1) :=
  List.Pairwise.sublist (delivered_sublist_published c ops) (published_pairwise ops)

/-! ### Faithful delivery to a continuously-subscribed client -/

/-- `c` is never unsubscribed anywhere in the trace. (Re-subscribes are
harmless: `addSub` only grows the set.) -/
def NoUnsub (c : SubId) : List Op → Prop
  | [] => True
  | .unsubscribe d :: ops => d ≠ c ∧ NoUnsub c ops
  | .subscribe _ :: ops => NoUnsub c ops
  | .publish _ :: ops => NoUnsub c ops

/-- **Fan-out faithfulness.** If `c` is subscribed and is never unsubscribed for
the remainder of the trace, then its delivery log is exactly the published
stream over that remainder — every event published while subscribed is
delivered, in order, with no gap. -/
theorem deliveredAux_complete (c : SubId) (s : List SubId) (next : Nat)
    (ops : List Op) (hmem : c ∈ s) (hnu : NoUnsub c ops) :
    deliveredAux c ⟨s, next⟩ ops = publishedAux next ops := by
  induction ops generalizing s next with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | subscribe d =>
      exact ih (addSub s d) next (mem_addSub_of_mem hmem) hnu
    | unsubscribe d =>
      obtain ⟨hd, hnu'⟩ := hnu
      exact ih (removeSub s d) next (mem_removeSub hmem (Ne.symm hd)) hnu'
    | publish e =>
      simp only [deliveredAux, publishedAux, if_pos hmem]
      rw [ih s (next + 1) hmem hnu]

/-! ### Splitting a trace at a subscribe point -/

theorem runB_subs (st : BState) (ops : List Op) :
    (runB st ops).subs = subsAux st.subs ops := by
  induction ops generalizing st with
  | nil => rfl
  | cons op ops ih => cases op <;> simp [runB, subsAux, ih]

theorem runB_next (st : BState) (ops : List Op) :
    (runB st ops).next = st.next + numPub ops := by
  induction ops generalizing st with
  | nil => simp [runB, numPub]
  | cons op ops ih =>
    cases op <;> simp only [runB, numPub, ih] <;> omega

/-- Delivery over an appended trace splits at the join: the log over `pre ++ suf`
is the log over `pre`, then the log over `suf` from the state `pre` left. -/
theorem deliveredAux_append (c : SubId) (st : BState) (pre suf : List Op) :
    deliveredAux c st (pre ++ suf)
      = deliveredAux c st pre ++ deliveredAux c (runB st pre) suf := by
  induction pre generalizing st with
  | nil => rfl
  | cons op pre ih =>
    cases op with
    | subscribe d => simp only [List.cons_append, deliveredAux, runB, ih]
    | unsubscribe d => simp only [List.cons_append, deliveredAux, runB, ih]
    | publish e =>
      simp only [List.cons_append, deliveredAux, runB]
      by_cases hc : c ∈ st.subs
      · simp only [if_pos hc, ih, List.cons_append]
      · simp only [if_neg hc, ih]

/-- **No gap after the subscribe point.** Once `c` is a subscriber (after the
prefix `pre`) and is not unsubscribed during the suffix `suf`, the events
delivered to `c` over `pre ++ suf` are exactly those delivered during `pre`,
followed by **every** event published during `suf` — with the sequence numbers
continuing from `numPub pre`. Nothing published while subscribed is dropped. -/
theorem delivered_split (c : SubId) (pre suf : List Op)
    (hmem : c ∈ subs pre) (hnu : NoUnsub c suf) :
    delivered c (pre ++ suf)
      = delivered c pre ++ publishedAux (numPub pre) suf := by
  unfold delivered
  rw [deliveredAux_append]
  congr 1
  have h1 : (runB BState.init pre).subs = subs pre := by rw [runB_subs]; rfl
  have h2 : (runB BState.init pre).next = numPub pre := by rw [runB_next]; simp [BState.init]
  have hstate : runB BState.init pre = ⟨subs pre, numPub pre⟩ :=
    calc runB BState.init pre
        = ⟨(runB BState.init pre).subs, (runB BState.init pre).next⟩ := rfl
      _ = ⟨subs pre, numPub pre⟩ := by rw [h1, h2]
  rw [hstate]
  exact deliveredAux_complete c (subs pre) (numPub pre) suf hmem hnu

/-! ### Unsubscribe silences a client -/

/-- **Well-behaved unsubscribe (local).** A publish delivers nothing to a client
that is not currently subscribed. -/
theorem publish_not_subscribed_no_deliver (c : SubId) (st : BState) (e : Event)
    (ops : List Op) (hc : c ∉ st.subs) :
    deliveredAux c st (.publish e :: ops)
      = deliveredAux c { st with next := st.next + 1 } ops := by
  simp only [deliveredAux, if_neg hc]

/-- **Well-behaved unsubscribe.** Immediately after `unsubscribe c`, `c` is not
in the subscriber set; so if the remainder never re-subscribes `c`, `c` is
silent for the rest of the trace — its delivery log over the post-unsubscribe
suffix is empty. -/
def NoResub (c : SubId) : List Op → Prop
  | [] => True
  | .subscribe d :: ops => d ≠ c ∧ NoResub c ops
  | .unsubscribe _ :: ops => NoResub c ops
  | .publish _ :: ops => NoResub c ops

/-- If `c` is not subscribed and is never re-subscribed, no event is delivered. -/
theorem deliveredAux_silent (c : SubId) (st : BState) (ops : List Op)
    (hc : c ∉ st.subs) (hnr : NoResub c ops) :
    deliveredAux c st ops = [] := by
  induction ops generalizing st with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | subscribe d =>
      obtain ⟨hd, hnr'⟩ := hnr
      refine ih { st with subs := addSub st.subs d } ?_ hnr'
      intro h
      unfold addSub at h; split at h
      · exact hc h
      · rw [List.mem_cons] at h; rcases h with h | h
        · exact hd h.symm
        · exact hc h
    | unsubscribe d =>
      refine ih { st with subs := removeSub st.subs d } ?_ hnr
      intro h
      unfold removeSub at h
      exact hc (List.mem_filter.mp h).1
    | publish e =>
      simp only [deliveredAux, if_neg hc]
      exact ih { st with next := st.next + 1 } hc hnr

end Sse
