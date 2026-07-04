/-
Recv — the two-class receive-buffer pool and the connection-state diet.

Idle connections hold zero heap: when data arrives, the connection borrows a
receive buffer from a reactor-local pool; when the parser consumes everything
(no partial or pipelined bytes remain), the buffer is returned.  The pool has
two size classes — small (plaintext receive) and large (record-protocol
staging) — each a LIFO stack capped at `maxPooled` entries.  Unlike the
general pool (`Pool.Basic`), acceptance is by *sufficient* capacity, not
exact capacity: any buffer at least small-class-sized is worth keeping.

The safety-relevant rule is on the reclaim edge: a buffer may be taken from
a connection **only when it holds no pending bytes** (`recv_len = 0`).
Reclaiming a buffer with unconsumed data would silently drop bytes off a
live connection.

Theorem groups:

* **Invariant preservation** — `WF.takeSmall`, `WF.takeLarge`,
  `WF.returnBuf`, `WF.maybeReclaim`: class membership by capacity range and
  the per-class length caps survive every operation.
* **Capacity never exceeded** — `returnBuf_small_le` / `returnBuf_large_le`.
* **Adequacy** — `takeSmall_cap` / `takeLarge_cap`: a borrowed buffer always
  has at least its class's capacity, pooled or fresh.
* **Conservation** — `return_takeSmall` / `return_takeLarge`: the LIFO round
  trip returns the very same buffer and restores the pool exactly.
* **Reclaim safety** — `reclaim_preserves_len` (pending bytes are never
  dropped), `reclaim_only_when_empty` (the buffer is only taken from an
  empty connection), `reclaim_idle_zero_heap` (an idle connection ends the
  reclaim holding no capacity at all — the diet), `ensureBuf_cap` /
  `ensureBuf_preserves` (re-borrowing on wakeup).
-/
import Pool.Basic

namespace Pool

/-- The receive pool: two LIFO buckets (buffer = its capacity), plus the
sizing configuration it was built with. -/
structure RecvPool where
  small : List Nat
  large : List Nat
  /-- Capacity of a fresh small buffer. -/
  smallCap : Nat
  /-- Capacity of a fresh large buffer. -/
  largeCap : Nat
  /-- Length cap per class. -/
  maxPooled : Nat

namespace RecvPool

/-- A fresh pool: empty buckets, given configuration. -/
def init (smallCap largeCap maxPooled : Nat) : RecvPool where
  small := []
  large := []
  smallCap := smallCap
  largeCap := largeCap
  maxPooled := maxPooled

/-- Borrow a small buffer: pop the stack, or allocate fresh at `smallCap`. -/
def takeSmall (p : RecvPool) : Nat × RecvPool :=
  match p.small with
  | c :: rest => (c, { p with small := rest })
  | [] => (p.smallCap, p)

/-- Borrow a large buffer: pop the stack, or allocate fresh at `largeCap`. -/
def takeLarge (p : RecvPool) : Nat × RecvPool :=
  match p.large with
  | c :: rest => (c, { p with large := rest })
  | [] => (p.largeCap, p)

/-- Return a buffer of capacity `c`: large-class if it can serve as a large
buffer, else small-class if it can serve as a small one, else drop.  A full
class drops the buffer rather than grow past the cap. -/
def returnBuf (p : RecvPool) (c : Nat) : RecvPool :=
  if p.largeCap ≤ c then
    if p.large.length < p.maxPooled then { p with large := c :: p.large } else p
  else if p.smallCap ≤ c then
    if p.small.length < p.maxPooled then { p with small := c :: p.small } else p
  else p

/-! ### Case-shape lemmas -/

theorem takeSmall_pop {p : RecvPool} {c : Nat} {rest : List Nat}
    (h : p.small = c :: rest) :
    p.takeSmall = (c, { p with small := rest }) := by
  simp [takeSmall, h]

theorem takeSmall_fresh {p : RecvPool} (h : p.small = []) :
    p.takeSmall = (p.smallCap, p) := by
  simp [takeSmall, h]

theorem takeLarge_pop {p : RecvPool} {c : Nat} {rest : List Nat}
    (h : p.large = c :: rest) :
    p.takeLarge = (c, { p with large := rest }) := by
  simp [takeLarge, h]

theorem takeLarge_fresh {p : RecvPool} (h : p.large = []) :
    p.takeLarge = (p.largeCap, p) := by
  simp [takeLarge, h]

theorem returnBuf_large {p : RecvPool} {c : Nat}
    (hc : p.largeCap ≤ c) (hlen : p.large.length < p.maxPooled) :
    p.returnBuf c = { p with large := c :: p.large } := by
  simp [returnBuf, hc, hlen]

theorem returnBuf_large_full {p : RecvPool} {c : Nat}
    (hc : p.largeCap ≤ c) (hlen : ¬p.large.length < p.maxPooled) :
    p.returnBuf c = p := by
  simp [returnBuf, hc, hlen]

theorem returnBuf_small {p : RecvPool} {c : Nat}
    (hc1 : ¬p.largeCap ≤ c) (hc2 : p.smallCap ≤ c)
    (hlen : p.small.length < p.maxPooled) :
    p.returnBuf c = { p with small := c :: p.small } := by
  simp [returnBuf, hc1, hc2, hlen]

theorem returnBuf_small_full {p : RecvPool} {c : Nat}
    (hc1 : ¬p.largeCap ≤ c) (hc2 : p.smallCap ≤ c)
    (hlen : ¬p.small.length < p.maxPooled) :
    p.returnBuf c = p := by
  simp [returnBuf, hc1, hc2, hlen]

theorem returnBuf_drop {p : RecvPool} {c : Nat}
    (hc1 : ¬p.largeCap ≤ c) (hc2 : ¬p.smallCap ≤ c) :
    p.returnBuf c = p := by
  simp [returnBuf, hc1, hc2]

/-! ### The invariant -/

/-- Well-formedness:

* `small_fit` / `large_fit` — class membership by capacity range: a small
  bucket entry serves any small request, a large entry any large one;
* `small_len` / `large_len` — the length caps: idle footprint stays bounded. -/
structure WF (p : RecvPool) : Prop where
  small_fit : ∀ c ∈ p.small, p.smallCap ≤ c ∧ c < p.largeCap
  large_fit : ∀ c ∈ p.large, p.largeCap ≤ c
  small_len : p.small.length ≤ p.maxPooled
  large_len : p.large.length ≤ p.maxPooled

protected theorem WF.init (smallCap largeCap maxPooled : Nat) :
    (init smallCap largeCap maxPooled).WF where
  small_fit := by intro c h; exact absurd h (List.not_mem_nil c)
  large_fit := by intro c h; exact absurd h (List.not_mem_nil c)
  small_len := Nat.zero_le _
  large_len := Nat.zero_le _

protected theorem WF.takeSmall {p : RecvPool} (h : p.WF) :
    ((p.takeSmall).2).WF := by
  cases hs : p.small with
  | nil => rw [takeSmall_fresh hs]; exact h
  | cons c rest =>
    rw [takeSmall_pop hs]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only
    · intro c' hc'
      exact h.small_fit c' (by rw [hs]; exact List.mem_cons_of_mem c hc')
    · exact h.large_fit
    · have := h.small_len
      rw [hs] at this
      simp only [List.length_cons] at this
      omega
    · exact h.large_len

protected theorem WF.takeLarge {p : RecvPool} (h : p.WF) :
    ((p.takeLarge).2).WF := by
  cases hs : p.large with
  | nil => rw [takeLarge_fresh hs]; exact h
  | cons c rest =>
    rw [takeLarge_pop hs]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only
    · exact h.small_fit
    · intro c' hc'
      exact h.large_fit c' (by rw [hs]; exact List.mem_cons_of_mem c hc')
    · exact h.small_len
    · have := h.large_len
      rw [hs] at this
      simp only [List.length_cons] at this
      omega

protected theorem WF.returnBuf {p : RecvPool} (h : p.WF) (c : Nat) :
    (p.returnBuf c).WF := by
  by_cases hc1 : p.largeCap ≤ c
  · by_cases hlen : p.large.length < p.maxPooled
    · rw [returnBuf_large hc1 hlen]
      refine ⟨h.small_fit, ?_, h.small_len, ?_⟩ <;> dsimp only
      · intro c' hc'
        cases List.mem_cons.mp hc' with
        | inl he => rw [he]; exact hc1
        | inr hin => exact h.large_fit c' hin
      · simp only [List.length_cons]
        omega
    · rw [returnBuf_large_full hc1 hlen]; exact h
  · by_cases hc2 : p.smallCap ≤ c
    · by_cases hlen : p.small.length < p.maxPooled
      · rw [returnBuf_small hc1 hc2 hlen]
        refine ⟨?_, h.large_fit, ?_, h.large_len⟩ <;> dsimp only
        · intro c' hc'
          cases List.mem_cons.mp hc' with
          | inl he => rw [he]; exact ⟨hc2, by omega⟩
          | inr hin => exact h.small_fit c' hin
        · simp only [List.length_cons]
          omega
      · rw [returnBuf_small_full hc1 hc2 hlen]; exact h
    · rw [returnBuf_drop hc1 hc2]; exact h

/-! ### Capacity never exceeded -/

theorem returnBuf_small_le {p : RecvPool} (h : p.WF) (c : Nat) :
    (p.returnBuf c).small.length ≤ p.maxPooled := by
  have hw := h.returnBuf c
  have hcfg : (p.returnBuf c).maxPooled = p.maxPooled := by
    unfold returnBuf
    split
    · split <;> rfl
    · split
      · split <;> rfl
      · rfl
  rw [← hcfg]
  exact hw.small_len

theorem returnBuf_large_le {p : RecvPool} (h : p.WF) (c : Nat) :
    (p.returnBuf c).large.length ≤ p.maxPooled := by
  have hw := h.returnBuf c
  have hcfg : (p.returnBuf c).maxPooled = p.maxPooled := by
    unfold returnBuf
    split
    · split <;> rfl
    · split
      · split <;> rfl
      · rfl
  rw [← hcfg]
  exact hw.large_len

/-! ### Adequacy -/

/-- A borrowed small buffer always holds a small-class request. -/
theorem takeSmall_cap {p : RecvPool} (h : p.WF) :
    p.smallCap ≤ (p.takeSmall).1 := by
  cases hs : p.small with
  | nil => rw [takeSmall_fresh hs]; exact Nat.le_refl _
  | cons c rest =>
    rw [takeSmall_pop hs]
    exact (h.small_fit c (by rw [hs]; exact List.mem_cons_self c rest)).1

/-- A borrowed large buffer always holds a large-class request. -/
theorem takeLarge_cap {p : RecvPool} (h : p.WF) :
    p.largeCap ≤ (p.takeLarge).1 := by
  cases hs : p.large with
  | nil => rw [takeLarge_fresh hs]; exact Nat.le_refl _
  | cons c rest =>
    rw [takeLarge_pop hs]
    exact h.large_fit c (by rw [hs]; exact List.mem_cons_self c rest)

/-! ### Conservation (LIFO round trips) -/

/-- Returning a small-class buffer and immediately borrowing hands back the
very same buffer and restores the pool exactly. -/
theorem return_takeSmall {p : RecvPool} {c : Nat}
    (hc1 : ¬p.largeCap ≤ c) (hc2 : p.smallCap ≤ c)
    (hlen : p.small.length < p.maxPooled) :
    (p.returnBuf c).takeSmall = (c, p) := by
  rw [returnBuf_small hc1 hc2 hlen]
  exact takeSmall_pop rfl

/-- Large-class round trip. -/
theorem return_takeLarge {p : RecvPool} {c : Nat}
    (hc : p.largeCap ≤ c) (hlen : p.large.length < p.maxPooled) :
    (p.returnBuf c).takeLarge = (c, p) := by
  rw [returnBuf_large hc hlen]
  exact takeLarge_pop rfl

/-! ### The reclaim edge -/

/-- A connection's receive-buffer view: the buffer's capacity (0 = the
connection holds no buffer) and the count of pending bytes the parser has
not yet consumed. -/
structure RecvBuf where
  cap : Nat
  len : Nat

/-- Reclaim the buffer back to the pool **only** when the connection has no
pending bytes and actually holds a buffer; otherwise leave everything
untouched.  On reclaim the connection is left holding nothing. -/
def maybeReclaim (p : RecvPool) (b : RecvBuf) : RecvPool × RecvBuf :=
  if b.len = 0 ∧ 0 < b.cap then (p.returnBuf b.cap, ⟨0, 0⟩) else (p, b)

/-- Re-borrow on wakeup: if the connection holds no buffer, borrow a small
one; pending count is untouched. -/
def ensureBuf (p : RecvPool) (b : RecvBuf) : RecvPool × RecvBuf :=
  if b.cap = 0 then ((p.takeSmall).2, ⟨(p.takeSmall).1, b.len⟩) else (p, b)

/-- **No byte loss.** Reclaiming never changes the pending-byte count: a
buffer with unconsumed data is left in place, and a reclaimed buffer had
none. -/
theorem reclaim_preserves_len (p : RecvPool) (b : RecvBuf) :
    ((maybeReclaim p b).2).len = b.len := by
  unfold maybeReclaim
  by_cases hb : b.len = 0 ∧ 0 < b.cap
  · rw [if_pos hb]
    exact hb.1.symm
  · rw [if_neg hb]

/-- **Reclaim only when empty.** If the reclaim touched the connection at
all, the connection had zero pending bytes. -/
theorem reclaim_only_when_empty {p : RecvPool} {b : RecvBuf}
    (h : (maybeReclaim p b).2 ≠ b) : b.len = 0 := by
  unfold maybeReclaim at h
  by_cases hb : b.len = 0 ∧ 0 < b.cap
  · exact hb.1
  · rw [if_neg hb] at h
    exact absurd rfl h

/-- **The diet.** An idle connection (no pending bytes) ends the reclaim
holding zero heap. -/
theorem reclaim_idle_zero_heap {p : RecvPool} {b : RecvBuf} (h : b.len = 0) :
    ((maybeReclaim p b).2).cap = 0 := by
  unfold maybeReclaim
  by_cases hc : 0 < b.cap
  · rw [if_pos ⟨h, hc⟩]
  · rw [if_neg (fun hand => hc hand.2)]
    show b.cap = 0
    omega

/-- Reclaiming preserves the pool invariant. -/
protected theorem WF.maybeReclaim {p : RecvPool} (h : p.WF) (b : RecvBuf) :
    ((maybeReclaim p b).1).WF := by
  unfold maybeReclaim
  by_cases hb : b.len = 0 ∧ 0 < b.cap
  · rw [if_pos hb]
    exact h.returnBuf b.cap
  · rw [if_neg hb]
    exact h

/-- After `ensureBuf` the connection always holds a buffer of at least the
small class (fresh or pooled), unless it already held one. -/
theorem ensureBuf_cap {p : RecvPool} (h : p.WF) {b : RecvBuf} (hb : b.cap = 0) :
    p.smallCap ≤ ((ensureBuf p b).2).cap := by
  unfold ensureBuf
  rw [if_pos hb]
  exact takeSmall_cap h

/-- `ensureBuf` never drops pending bytes and never swaps out a held
buffer. -/
theorem ensureBuf_preserves (p : RecvPool) (b : RecvBuf) :
    ((ensureBuf p b).2).len = b.len
      ∧ (b.cap ≠ 0 → (ensureBuf p b).2 = b) := by
  unfold ensureBuf
  by_cases hb : b.cap = 0
  · rw [if_pos hb]
    exact ⟨rfl, fun hne => absurd hb hne⟩
  · rw [if_neg hb]
    exact ⟨rfl, fun _ => rfl⟩

/-- `ensureBuf` preserves the pool invariant. -/
protected theorem WF.ensureBuf {p : RecvPool} (h : p.WF) (b : RecvBuf) :
    ((ensureBuf p b).1).WF := by
  unfold ensureBuf
  by_cases hb : b.cap = 0
  · rw [if_pos hb]
    exact h.takeSmall
  · rw [if_neg hb]
    exact h

end RecvPool

end Pool
