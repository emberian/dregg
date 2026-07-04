import Uring.Conservation

/-!
# Named counterexample: the overflow-drop leak (`nodrop` absent)

Without the no-drop feature, conservation is **false**: a full completion
queue silently drops further completions, and a dropped buffer-select
completion takes its lent buffer id with it. The client never sees the
lease, so the bid is recycled zero times — and can never be recycled on
any continuation.

The trace (`cfg₀ = ⟨nbufs := 2, cqCap := 1, nodrop := false⟩`):

1. client arms a multishot buffer-select receive (`submit`);
2. environment delivers bid 0 — queue has room, completion posted;
3. environment delivers bid 1 — queue full, feature absent: the
   completion is **dropped**; bid 1 has left the free ring and rides
   nothing.

State reached: bid 1 inhabits no location (`leak`). Monotonicity makes
the loss permanent (`leak_forever`), and since a recycle demands a held
occurrence, bid 1 is never recycled on any extension of this trace
(`never_recycled`): recycle-exactly-once fails — one lend, zero recycles.

The shape is instructive: one armed multishot can produce more
completions than the queue holds with **no client move able to
interpose**, so no reap discipline can save the property. Droppable
completion queues and provided-buffer leases do not compose; the no-drop
feature (or a queue provably sized for the worst-case completion burst)
is a *soundness precondition* for buffer recycling, not a nicety.
-/

namespace Uring

/-- Ring with two buffers, a one-slot completion queue, no no-drop
feature. -/
def cfg₀ : Cfg := { nbufs := 2, cqCap := 1, nodrop := false }

/-- The multishot receive the client arms on fd 0. -/
def q₀ : Sqe := { id := 0, kind := .recvMulti 0 }

/-- After `submit q₀`. -/
def s₁ : St :=
  { nextId := 1, inflight := [q₀], cq := [], ovf := [], dropped := 0
    free := [0, 1], pending := [], held := [], dead := [] }

/-- After the environment delivers bid 0 (completion posted, queue now
full). -/
def s₂ : St :=
  { nextId := 1, inflight := [q₀], cq := [⟨0, .buf 0, true⟩], ovf := []
    dropped := 0, free := [1], pending := [], held := [], dead := [] }

/-- After the environment delivers bid 1 into the full queue: dropped.
Bid 1 appears nowhere. -/
def s₃ : St :=
  { nextId := 1, inflight := [q₀], cq := [⟨0, .buf 0, true⟩], ovf := []
    dropped := 1, free := [], pending := [], held := [], dead := [] }

theorem step₁ : Step cfg₀ (init cfg₀) (.submit q₀) s₁ := by
  have he : ({ init cfg₀ with inflight := [q₀], nextId := 1 } : St) = s₁ := by
    decide
  rw [← he]
  exact Step.submit rfl (by simp [kindOk, q₀, init]) (by simp [predOk, q₀])

theorem step₂ : Step cfg₀ s₁ (.deliver 0 0 true) s₂ := by
  have he : post cfg₀ { s₁ with free := ([] : List Bid) ++ [1] }
      ⟨q₀.id, .buf 0, true⟩ = s₂ := by decide
  rw [← he]
  exact Step.deliver_more (q := q₀) (by simp [s₁]) rfl rfl

theorem step₃ : Step cfg₀ s₂ (.deliver 0 1 true) s₃ := by
  have he : post cfg₀ { s₂ with free := ([] : List Bid) ++ [] }
      ⟨q₀.id, .buf 1, true⟩ = s₃ := by decide
  rw [← he]
  exact Step.deliver_more (q := q₀) (by simp [s₂]) rfl rfl

/-- The leaking trace, as an explicit derivation. -/
theorem trace_leak :
    Trace cfg₀ (init cfg₀)
      [.submit q₀, .deliver 0 0 true, .deliver 0 1 true] s₃ :=
  .cons step₁ (.cons step₂ (.cons step₃ .nil))

theorem s₃_reachable : Reachable cfg₀ s₃ := ⟨_, trace_leak⟩

/-- **COUNTEREXAMPLE, part 1 — the leak.** In the reachable state `s₃`,
bid 1 (a bid of the universe: `1 < nbufs`) inhabits no location. The
conservation statement is false without the no-drop feature. -/
theorem leak : (owned s₃).count 1 = 0 := by decide

/-- The conservation theorem's statement, refuted at `cfg₀`. -/
theorem conservation_fails_without_nodrop :
    ¬ ∀ (s : St), Reachable cfg₀ s →
      ∀ b, (owned s).count b = if b < cfg₀.nbufs then 1 else 0 := by
  intro h
  have := h s₃ s₃_reachable 1
  rw [leak] at this
  simp [cfg₀] at this

/-- **COUNTEREXAMPLE, part 2 — permanence.** On every extension of the
leaking trace, bid 1 still inhabits no location. -/
theorem leak_forever {s' : St} {ls : List Lbl}
    (tr : Trace cfg₀ s₃ ls s') : (owned s').count 1 = 0 :=
  Nat.le_zero.mp (leak ▸ trace_count_le tr 1)

/-- **COUNTEREXAMPLE, part 3 — never recycled.** No extension of the
leaking trace ever recycles bid 1: the environment lent it (step 3), the
client recycles it zero times, forever. Recycle-exactly-once fails. -/
theorem never_recycled {s' : St} {ls : List Lbl}
    (tr : Trace cfg₀ s₃ ls s') : Lbl.recycle 1 ∉ ls :=
  cold_never_recycled tr leak

end Uring
