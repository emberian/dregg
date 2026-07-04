import Uring.Lts

/-!
# Bid conservation

Per-step accounting of buffer ids over `owned` (the multiset of all
locations a bid can inhabit):

* **with the `nodrop` feature** every step conserves the count of every
  bid exactly — `step_count_eq` — so each bid of the universe inhabits
  exactly one location in every reachable state (`conservation`): no leak
  and no duplication, under every demonic interleaving;
* **unconditionally** (with or without `nodrop`) no step ever *increases*
  a bid's count — `step_count_le` — so no reachable state duplicates a
  bid (`reachable_count_le_one`), and a bid once leaked is leaked forever
  (used by the counterexample file).

The single count-decreasing edge is `post`'s silent-drop branch: a full
completion queue without `nodrop` discards a completion, and with it any
buffer id it carried.
-/

namespace Uring

/-- Posting a completion adds exactly its carried bid — when nothing is
dropped (queue has room, or the `nodrop` feature retains it). -/
theorem count_owned_post_nodrop {cfg : Cfg} (hn : cfg.nodrop = true)
    (s : St) (c : Cqe) (b : Bid) :
    (owned (post cfg s c)).count b
      = (owned s).count b + (cqBids [c]).count b := by
  unfold post
  rw [hn]
  split
  · simp [owned, List.count_append]; omega
  · simp [owned, List.count_append]; omega

/-- Posting a completion never adds more than its carried bid (the drop
branch adds nothing — and loses the bid). -/
theorem count_owned_post_le (cfg : Cfg) (s : St) (c : Cqe) (b : Bid) :
    (owned (post cfg s c)).count b
      ≤ (owned s).count b + (cqBids [c]).count b := by
  unfold post
  split
  · simp [owned, List.count_append]; omega
  · split
    · simp [owned, List.count_append]; omega
    · simp [owned, List.count_append]

/-- Client dispatch adds exactly the reaped completion's carried bid (a
`buf` lease moves into `held`; other payloads move nothing). -/
theorem count_owned_dispatch (s : St) (c : Cqe) (b : Bid) :
    (owned (dispatch s c)).count b
      = (owned s).count b + (cqBids [c]).count b := by
  cases hc : c.payload <;>
    simp [dispatch, hc, owned, Payload.bid?, List.count_append,
      List.count_cons] <;>
    omega

/-- **Per-step conservation** (with `nodrop`): every transition of the
product LTS — client or demonic environment — preserves the count of
every bid in `owned`. -/
theorem step_count_eq {cfg : Cfg} {s s' : St} {l : Lbl}
    (hn : cfg.nodrop = true) (h : Step cfg s l s') (b : Bid) :
    (owned s').count b = (owned s).count b := by
  cases h with
  | submit hid hk hp => simp [owned]
  | reap hcq =>
      rw [count_owned_dispatch]
      simp [owned, hcq, List.count_append] <;> omega
  | recycle hheld =>
      simp [owned, hheld, List.count_append, List.count_cons]
      omega
  | publish => simp [owned, List.count_append] <;> omega
  | complete hin hms hlk =>
      rw [count_owned_post_nodrop hn]
      simp [owned, Payload.bid?, List.count_append]
  | deliver_more hq hk hfree =>
      rw [count_owned_post_nodrop hn]
      simp [owned, hfree, Payload.bid?, List.count_append, List.count_cons]
      omega
  | deliver_final hin hk hfree =>
      rw [count_owned_post_nodrop hn]
      simp [owned, hfree, Payload.bid?, List.count_append, List.count_cons]
      omega
  | starve_more hq hk =>
      rw [count_owned_post_nodrop hn]
      simp [Payload.bid?]
  | starve_final hin hk =>
      rw [count_owned_post_nodrop hn]
      simp [owned, Payload.bid?, List.count_append]
  | exhaust hin hk =>
      rw [count_owned_post_nodrop hn]
      simp [owned, Payload.bid?, List.count_append]
  | flush hovf hroom =>
      simp [owned, hovf, List.count_append] <;> omega

/-- **Per-step monotonicity** (any configuration): no transition ever
increases a bid's count. Only `post`'s silent-drop branch decreases it. -/
theorem step_count_le {cfg : Cfg} {s s' : St} {l : Lbl}
    (h : Step cfg s l s') (b : Bid) :
    (owned s').count b ≤ (owned s).count b := by
  cases h with
  | submit hid hk hp => simp [owned]
  | reap hcq =>
      rw [count_owned_dispatch]
      simp [owned, hcq, List.count_append] <;> omega
  | recycle hheld =>
      simp [owned, hheld, List.count_append, List.count_cons]
      omega
  | publish => simp [owned, List.count_append] <;> omega
  | complete hin hms hlk =>
      refine Nat.le_trans (count_owned_post_le ..) ?_
      simp [owned, Payload.bid?, List.count_append]
  | deliver_more hq hk hfree =>
      refine Nat.le_trans (count_owned_post_le ..) ?_
      simp [owned, hfree, Payload.bid?, List.count_append, List.count_cons]
      omega
  | deliver_final hin hk hfree =>
      refine Nat.le_trans (count_owned_post_le ..) ?_
      simp [owned, hfree, Payload.bid?, List.count_append, List.count_cons]
      omega
  | starve_more hq hk =>
      refine Nat.le_trans (count_owned_post_le ..) ?_
      simp [Payload.bid?]
  | starve_final hin hk =>
      refine Nat.le_trans (count_owned_post_le ..) ?_
      simp [owned, Payload.bid?, List.count_append]
  | exhaust hin hk =>
      refine Nat.le_trans (count_owned_post_le ..) ?_
      simp [owned, Payload.bid?, List.count_append]
  | flush hovf hroom =>
      simp [owned, hovf, List.count_append] <;> omega

theorem trace_count_eq {cfg : Cfg} {s s' : St} {ls : List Lbl}
    (hn : cfg.nodrop = true) (tr : Trace cfg s ls s') (b : Bid) :
    (owned s').count b = (owned s).count b := by
  induction tr with
  | nil => rfl
  | cons h _ ih => rw [ih, step_count_eq hn h]

theorem trace_count_le {cfg : Cfg} {s s' : St} {ls : List Lbl}
    (tr : Trace cfg s ls s') (b : Bid) :
    (owned s').count b ≤ (owned s).count b := by
  induction tr with
  | nil => exact Nat.le_refl _
  | cons h _ ih => exact Nat.le_trans ih (step_count_le h b)

/-- **CONSERVATION** (the no-leak/no-duplication half of
recycle-exactly-once, with the `nodrop` feature): in every reachable
state of the product LTS, every buffer id of the universe inhabits
exactly one location — free, pending, held, or riding an unreaped
completion — under every demonic interleaving, including exhaustion,
starvation, overflow-retention, and close-with-in-flight edges. -/
theorem conservation {cfg : Cfg} {s : St}
    (hn : cfg.nodrop = true) (hr : Reachable cfg s) (b : Bid) :
    (owned s).count b = if b < cfg.nbufs then 1 else 0 := by
  obtain ⟨ls, tr⟩ := hr
  rw [trace_count_eq hn tr b, count_owned_init]

/-- No-leak, membership form: with `nodrop`, a bid of the universe is
always *somewhere* recoverable. -/
theorem no_leak {cfg : Cfg} {s : St} {b : Bid}
    (hn : cfg.nodrop = true) (hr : Reachable cfg s) (hb : b < cfg.nbufs) :
    b ∈ owned s := by
  have h := conservation hn hr b
  rw [if_pos hb] at h
  exact List.count_pos_iff.mp (by omega)

/-- No-duplication, any configuration: a bid never inhabits two
locations at once (in particular it is never simultaneously free and
held, or held twice). -/
theorem reachable_count_le_one {cfg : Cfg} {s : St}
    (hr : Reachable cfg s) (b : Bid) :
    (owned s).count b ≤ 1 := by
  obtain ⟨ls, tr⟩ := hr
  refine Nat.le_trans (trace_count_le tr b) ?_
  rw [count_owned_init]
  split <;> simp

/-- A bid that inhabits no location can never again be recycled, on any
continuation: counts never increase (`step_count_le`), and a recycle
demands a held occurrence. This is what makes a leak *permanent*. -/
theorem cold_never_recycled {cfg : Cfg} {b : Bid} {s s' : St}
    {ls : List Lbl} (tr : Trace cfg s ls s') :
    (owned s).count b = 0 → Lbl.recycle b ∉ ls := by
  induction tr with
  | nil => intro _; simp
  | cons h _ ih =>
      intro h0
      have h0' : (owned _).count b = 0 :=
        Nat.le_zero.mp (by rw [← h0]; exact step_count_le h b)
      simp only [List.mem_cons, not_or]
      refine ⟨fun hl => ?_, ih h0'⟩
      subst hl
      cases h with
      | recycle hheld =>
          simp [owned, hheld, List.count_append, List.count_cons] at h0
            <;> omega

end Uring
