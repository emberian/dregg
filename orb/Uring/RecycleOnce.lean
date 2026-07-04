import Uring.Conservation

/-!
# Recycle-exactly-once, trace form

`Uring.Conservation` gives the state-invariant half of the property. This
file gives the trace half, valid for **every** configuration (with or
without the `nodrop` feature):

* `recycle_needs_lend` — a recycle of bid `b` can only occur after the
  environment has lent `b` via a buffer-select delivery;
* `recycle_at_most_once` — between any two recycles of the same bid there
  is a fresh delivery of that bid: no lease is ever recycled twice, under
  every demonic interleaving — exhaustion (`ENOBUFS`) at arbitrary points,
  re-arm boundaries, bufferless completions, overflow, close-with-in-
  flight, and stale deliveries after close included.

Together with `conservation` (no-leak + no-duplication, `nodrop`) and
`recycle_enabled` (a held lease always has its recycle move enabled),
this is the recycle-exactly-once property: every lent buffer id is
recycled exactly once per lease, and with `nodrop` no bid is ever lost.

The proof shape: define `hot s b` — the number of client-facing locations
of `b` (held leases plus leases riding unreaped completions). A recycle
of `b` demands `b ∈ held`, so `hot ≥ 1`; the only edge that can raise
`hot b` from zero is a buffer-select delivery of `b`. Right after a
recycle of `b`, `hot b = 0` (by no-duplication). Induction along the
trace segment does the rest.
-/

namespace Uring

/-- Posting a completion adds at most its carried bid to the client-facing
locations (the drop branch adds nothing). -/
theorem hot_post_le (cfg : Cfg) (s : St) (c : Cqe) (b : Bid) :
    hot (post cfg s c) b ≤ hot s b + (cqBids [c]).count b := by
  unfold post
  split
  · simp [hot, List.count_append]; omega
  · split
    · simp [hot, List.count_append]; omega
    · simp [hot, List.count_append]

/-- The cold-stays-cold lemma: if bid `b` has no client-facing occurrence,
the only transition that can create one is a buffer-select delivery of
`b` itself. Every other move — by either player — preserves coldness. -/
theorem hot_step_zero {cfg : Cfg} {s s' : St} {l : Lbl} {b : Bid}
    (h : Step cfg s l s') (h0 : hot s b = 0)
    (hnl : ∀ fd more, l ≠ .deliver fd b more) : hot s' b = 0 := by
  cases h with
  | submit hid hk hp => simpa [hot] using h0
  | reap hcq =>
      rename_i c rest
      cases hc : c.payload <;>
        (simp [hot, hcq, hc, dispatch, Payload.bid?, List.count_append,
          List.count_cons] at h0 ⊢) <;>
        first | omega | simp_all
  | recycle hheld =>
      simp [hot, hheld, List.count_append, List.count_cons] at h0 ⊢
      first | omega | simp_all
  | publish => simpa [hot] using h0
  | complete hin hms hlk =>
      refine Nat.le_zero.mp (Nat.le_trans (hot_post_le ..) ?_)
      simp [hot, Payload.bid?] at h0 ⊢
      first | omega | simp_all
  | deliver_more hq hk hfree =>
      rename_i q fd bd f₁ f₂
      have hbd : bd ≠ b := fun he => hnl fd true (by rw [he])
      refine Nat.le_zero.mp (Nat.le_trans (hot_post_le ..) ?_)
      simp [hot, Payload.bid?, hbd, List.count_append, List.count_cons,
        List.count_singleton] at h0 ⊢
      first | omega | simp_all
  | deliver_final hin hk hfree =>
      rename_i q fd bd q₁ q₂ f₁ f₂
      have hbd : bd ≠ b := fun he => hnl fd false (by rw [he])
      refine Nat.le_zero.mp (Nat.le_trans (hot_post_le ..) ?_)
      simp [hot, Payload.bid?, hbd, List.count_append, List.count_cons,
        List.count_singleton] at h0 ⊢
      first | omega | simp_all
  | starve_more hq hk =>
      refine Nat.le_zero.mp (Nat.le_trans (hot_post_le ..) ?_)
      simp [hot, Payload.bid?] at h0 ⊢
      first | omega | simp_all
  | starve_final hin hk =>
      refine Nat.le_zero.mp (Nat.le_trans (hot_post_le ..) ?_)
      simp [hot, Payload.bid?] at h0 ⊢
      first | omega | simp_all
  | exhaust hin hk =>
      refine Nat.le_zero.mp (Nat.le_trans (hot_post_le ..) ?_)
      simp [hot, Payload.bid?] at h0 ⊢
      first | omega | simp_all
  | flush hovf hroom =>
      simp [hot, hovf, List.count_append] at h0 ⊢
      first | omega | simp_all

/-- From a state where bid `b` is cold, no trace segment can reach a
recycle of `b` without first passing through a buffer-select delivery of
`b`. -/
theorem cold_recycle_needs_deliver {cfg : Cfg} {t t' : St} {b : Bid}
    {m rest : List Lbl}
    (tr : Trace cfg t (m ++ .recycle b :: rest) t')
    (h0 : hot t b = 0)
    (hm : ∀ fd more, Lbl.deliver fd b more ∉ m) :
    False := by
  induction m generalizing t with
  | nil =>
      cases tr with
      | cons h _ =>
          cases h with
          | recycle hheld =>
              simp [hot, hheld, List.count_append, List.count_cons] at h0
  | cons l m' ih =>
      cases tr with
      | cons h tr' =>
          refine ih tr' (hot_step_zero h h0 fun fd mo hl => ?_) ?_
          · exact hm fd mo (by simp [hl])
          · intro fd mo hmem
            exact hm fd mo (by simp [hmem])

/-- **A recycle happens only under a lease**: any recycle of bid `b` in a
trace from the initial state is preceded by a buffer-select delivery of
`b`. (Any configuration.) -/
theorem recycle_needs_lend {cfg : Cfg} {sfin : St} {b : Bid}
    {m₁ m₂ : List Lbl}
    (tr : Trace cfg (init cfg) (m₁ ++ .recycle b :: m₂) sfin) :
    ∃ fd more, Lbl.deliver fd b more ∈ m₁ := by
  refine Classical.byContradiction fun hno => ?_
  simp only [not_exists] at hno
  exact cold_recycle_needs_deliver tr (by simp [hot, init]) fun fd mo =>
    hno fd mo

/-- **NO DOUBLE RECYCLE** (any configuration, `nodrop` or not): between
any two recycles of the same bid in any trace of the product LTS from the
initial state, the environment delivers that bid afresh. Hence each
lease — each buffer-select delivery — is recycled at most once, across
every demonic interleaving including exhaustion/re-arm boundaries. -/
theorem recycle_at_most_once {cfg : Cfg} {sfin : St} {b : Bid}
    {m₁ m₂ m₃ : List Lbl}
    (tr : Trace cfg (init cfg)
      (m₁ ++ .recycle b :: (m₂ ++ .recycle b :: m₃)) sfin) :
    ∃ fd more, Lbl.deliver fd b more ∈ m₂ := by
  refine Classical.byContradiction fun hno => ?_
  simp only [not_exists] at hno
  obtain ⟨r, tr₁, tr₂⟩ := Trace.append_split (l₁ := m₁) tr
  cases tr₂ with
  | cons h tr₃ =>
      cases h with
      | recycle hheld =>
          refine cold_recycle_needs_deliver tr₃ ?_ fun fd mo => hno fd mo
          have hle := reachable_count_le_one ⟨m₁, tr₁⟩ b
          simp [owned, hheld, List.count_append, List.count_cons] at hle
          simp [hot, List.count_append]
          omega

end Uring
