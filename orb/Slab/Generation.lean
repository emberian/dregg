/-
Generation epochs — the fd-reuse (ABA) defense.

The kernel recycles file descriptors: close fd 7 and the very next accept may
return fd 7 again.  Any completion or cross-thread response that identifies a
connection by fd alone can therefore be delivered to the *wrong* connection —
a stale event for the old incarnation, drained after the fd was rebound,
would leak one client's data to another.

The defense is a monotone process epoch: the reactor keeps a counter, every
new connection incarnation is tagged with the counter's current value
(`openConn`), and every token that crosses a dispatch/completion gap carries
the `(fd, gen)` pair it was captured with.  At drain time the guard is

  `token.gen == current(fd).gen`

with `gen = 0` reserved as a "no generation check" sentinel for
reactor-internal events (so real generations start at 1, and — in the
fixed-width implementation — the counter skips 0 when it wraps).

This file proves the guard sound: a stale `(fd, gen)` token never resolves
to a newer connection's slot (`stale_token_never_resolves`), because every
incarnation opened after the capture point carries a strictly larger
generation (`run_incarnation`, `captured_ne_newer`).

The model's counter is `Nat` — genuinely monotone, never wraps.  The real
counter is a 64-bit machine word advanced by wrapping increment.  That gap is
this rank's one **named assumption**, `NoWrap` (see the final section): the
`Nat` model is exact as long as the process assigns fewer than `2^64 - 1`
generations, and under `NoWrap` the machine's mod-2^64 equality test decides
the model's equality (`guard_exact_of_noWrap`).
-/
import Slab.Refinement

namespace Slab

universe u

variable {σ : Type u}

/-- One connection incarnation: the payload state tagged with the generation
it was born under.  Two incarnations occupying the same fd at different times
differ in `gen`. -/
structure Conn (σ : Type u) where
  state : σ
  gen : Nat

/-- The reactor's connection view: the slab of live connections plus the
monotone generation counter.  `nextGen` is the generation the *next* opened
connection will receive; it starts at 1 (0 is the sentinel). -/
structure Reactor (σ : Type u) where
  table : Table (Conn σ)
  nextGen : Nat

namespace Reactor

/-- The initial reactor: empty slab, counter at 1 (skipping the sentinel). -/
def empty : Reactor σ where
  table := Table.empty
  nextGen := 1

/-- Accept a new connection on `fd`: tag it with the current counter value
and advance the counter. -/
def openConn (r : Reactor σ) (fd : Nat) (st : σ) : Reactor σ where
  table := r.table.insert fd { state := st, gen := r.nextGen }
  nextGen := r.nextGen + 1

/-- Close the connection on `fd` (the fd becomes recyclable). -/
def closeConn (r : Reactor σ) (fd : Nat) : Reactor σ :=
  { r with table := r.table.erase fd }

/-- Mutate the state of the connection on `fd` in place.  The generation is
preserved: updates do not create a new incarnation. -/
def update (r : Reactor σ) (fd : Nat) (f : σ → σ) : Reactor σ :=
  match r.table.lookup fd with
  | none => r
  | some c => { r with table := r.table.insert fd { state := f c.state, gen := c.gen } }

/-- Resolve a cross-gap `(fd, gen)` token: return the connection state only
if `fd` is live *and* its generation matches the token.  This is the stale
guard. -/
def resolve (r : Reactor σ) (fd g : Nat) : Option σ :=
  (r.table.lookup fd).bind fun c => if c.gen = g then some c.state else none

/-! ### Case-shape lemmas -/

theorem update_none {r : Reactor σ} {fd : Nat}
    (h : r.table.lookup fd = none) (f : σ → σ) : r.update fd f = r := by
  simp [update, h]

theorem update_some {r : Reactor σ} {fd : Nat} {c : Conn σ}
    (h : r.table.lookup fd = some c) (f : σ → σ) :
    r.update fd f =
      { r with table := r.table.insert fd { state := f c.state, gen := c.gen } } := by
  simp [update, h]

theorem update_nextGen (r : Reactor σ) (fd : Nat) (f : σ → σ) :
    (r.update fd f).nextGen = r.nextGen := by
  unfold update
  split <;> rfl

/-! ### The generation invariant -/

/-- Well-formedness of the reactor view:

* `table_wf` — the underlying slab invariant;
* `next_pos` — the counter never revisits the sentinel 0;
* `gen_pos` — no live connection carries the sentinel generation, so a
  0-token can never match a real connection;
* `gen_lt` — every live generation was assigned in the past: it is strictly
  below the counter.  This is the freshness fact the ABA defense rests on. -/
structure GWF (r : Reactor σ) : Prop where
  table_wf : r.table.WF
  next_pos : 1 ≤ r.nextGen
  gen_pos : ∀ fd c, r.table.lookup fd = some c → 1 ≤ c.gen
  gen_lt : ∀ fd c, r.table.lookup fd = some c → c.gen < r.nextGen

protected theorem GWF.empty : (empty : Reactor σ).GWF where
  table_wf := Table.WF.empty
  next_pos := Nat.le_refl 1
  gen_pos := by intro fd c h; rw [empty, Table.lookup_empty] at h; exact Option.noConfusion h
  gen_lt := by intro fd c h; rw [empty, Table.lookup_empty] at h; exact Option.noConfusion h

protected theorem GWF.openConn {r : Reactor σ} (h : r.GWF) (fd : Nat) (st : σ) :
    (r.openConn fd st).GWF := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only [openConn]
  · exact h.table_wf.insert fd _
  · omega
  · intro fd' c hl
    by_cases hfd : fd' = fd
    · rw [hfd, Table.lookup_insert_self] at hl
      obtain rfl := Option.some.inj hl
      exact h.next_pos
    · rw [Table.lookup_insert_ne h.table_wf hfd] at hl
      exact h.gen_pos fd' c hl
  · intro fd' c hl
    by_cases hfd : fd' = fd
    · rw [hfd, Table.lookup_insert_self] at hl
      obtain rfl := Option.some.inj hl
      exact Nat.lt_succ_self _
    · rw [Table.lookup_insert_ne h.table_wf hfd] at hl
      have := h.gen_lt fd' c hl
      omega

protected theorem GWF.closeConn {r : Reactor σ} (h : r.GWF) (fd : Nat) :
    (r.closeConn fd).GWF := by
  refine ⟨?_, h.next_pos, ?_, ?_⟩ <;> dsimp only [closeConn, Table.erase]
  · exact h.table_wf.remove fd
  · intro fd' c hl
    by_cases hfd : fd' = fd
    · rw [hfd, Table.lookup_remove_self] at hl
      exact Option.noConfusion hl
    · rw [Table.lookup_remove_ne h.table_wf hfd] at hl
      exact h.gen_pos fd' c hl
  · intro fd' c hl
    by_cases hfd : fd' = fd
    · rw [hfd, Table.lookup_remove_self] at hl
      exact Option.noConfusion hl
    · rw [Table.lookup_remove_ne h.table_wf hfd] at hl
      exact h.gen_lt fd' c hl

protected theorem GWF.update {r : Reactor σ} (h : r.GWF) (fd : Nat) (f : σ → σ) :
    (r.update fd f).GWF := by
  cases hu : r.table.lookup fd with
  | none => rw [update_none hu]; exact h
  | some c =>
    rw [update_some hu f]
    refine ⟨?_, h.next_pos, ?_, ?_⟩ <;> dsimp only
    · exact h.table_wf.insert fd _
    · intro fd' c' hl
      by_cases hfd : fd' = fd
      · rw [hfd, Table.lookup_insert_self] at hl
        obtain rfl := Option.some.inj hl
        exact h.gen_pos fd c hu
      · rw [Table.lookup_insert_ne h.table_wf hfd] at hl
        exact h.gen_pos fd' c' hl
    · intro fd' c' hl
      by_cases hfd : fd' = fd
      · rw [hfd, Table.lookup_insert_self] at hl
        obtain rfl := Option.some.inj hl
        exact h.gen_lt fd c hu
      · rw [Table.lookup_insert_ne h.table_wf hfd] at hl
        exact h.gen_lt fd' c' hl

/-! ### Runs: arbitrary futures after a capture point -/

/-- The reactor operations a run is made of. -/
inductive Op (σ : Type u) where
  | openConn (fd : Nat) (st : σ)
  | closeConn (fd : Nat)
  | update (fd : Nat) (f : σ → σ)

/-- One operation. -/
def step (r : Reactor σ) : Op σ → Reactor σ
  | .openConn fd st => r.openConn fd st
  | .closeConn fd => r.closeConn fd
  | .update fd f => r.update fd f

/-- A run: a list of operations applied in order. -/
def run (r : Reactor σ) : List (Op σ) → Reactor σ
  | [] => r
  | op :: ops => (r.step op).run ops

protected theorem GWF.step {r : Reactor σ} (h : r.GWF) (op : Op σ) :
    (r.step op).GWF := by
  cases op with
  | openConn fd st => exact h.openConn fd st
  | closeConn fd => exact h.closeConn fd
  | update fd f => exact h.update fd f

protected theorem GWF.run {r : Reactor σ} (h : r.GWF) (ops : List (Op σ)) :
    (r.run ops).GWF := by
  induction ops generalizing r with
  | nil => exact h
  | cons op ops ih => exact ih (h.step op)

/-- The counter never moves backwards. -/
theorem nextGen_mono_step (r : Reactor σ) (op : Op σ) :
    r.nextGen ≤ (r.step op).nextGen := by
  cases op with
  | openConn fd st => exact Nat.le_succ _
  | closeConn fd => exact Nat.le_refl _
  | update fd f => rw [step, update_nextGen]; exact Nat.le_refl _

theorem nextGen_mono_run (r : Reactor σ) (ops : List (Op σ)) :
    r.nextGen ≤ (r.run ops).nextGen := by
  induction ops generalizing r with
  | nil => exact Nat.le_refl _
  | cons op ops ih =>
    have h1 := nextGen_mono_step r op
    have h2 := ih (r.step op)
    exact Nat.le_trans h1 h2

/-- Each operation assigns at most one generation. -/
theorem nextGen_step_le (r : Reactor σ) (op : Op σ) :
    (r.step op).nextGen ≤ r.nextGen + 1 := by
  cases op with
  | openConn fd st => exact Nat.le_refl _
  | closeConn fd => exact Nat.le_succ _
  | update fd f => rw [step, update_nextGen]; exact Nat.le_succ _

theorem nextGen_run_le (r : Reactor σ) (ops : List (Op σ)) :
    (r.run ops).nextGen ≤ r.nextGen + ops.length := by
  induction ops generalizing r with
  | nil => exact Nat.le_refl _
  | cons op ops ih =>
    have h1 := nextGen_step_le r op
    have h2 := ih (r.step op)
    dsimp only [run]
    simp only [List.length_cons]
    omega

/-! ### Incarnation tracking -/

/-- After one step, the connection at `fd` is either the incarnation that was
already there (same generation), or one opened by this step — which carries
a generation at or above the old counter. -/
theorem step_incarnation {r : Reactor σ} (h : r.GWF) (op : Op σ) (fd : Nat)
    {c' : Conn σ} (hl : ((r.step op).table.lookup fd) = some c') :
    (∃ c, r.table.lookup fd = some c ∧ c.gen = c'.gen) ∨ r.nextGen ≤ c'.gen := by
  cases op with
  | openConn fd' st =>
    dsimp only [step, openConn] at hl
    by_cases hfd : fd = fd'
    · rw [hfd, Table.lookup_insert_self] at hl
      obtain rfl := Option.some.inj hl
      right; exact Nat.le_refl _
    · rw [Table.lookup_insert_ne h.table_wf hfd] at hl
      left; exact ⟨c', hl, rfl⟩
  | closeConn fd' =>
    dsimp only [step, closeConn, Table.erase] at hl
    by_cases hfd : fd = fd'
    · rw [hfd, Table.lookup_remove_self] at hl
      exact Option.noConfusion hl
    · rw [Table.lookup_remove_ne h.table_wf hfd] at hl
      left; exact ⟨c', hl, rfl⟩
  | update fd' f =>
    dsimp only [step] at hl
    cases hu : r.table.lookup fd' with
    | none =>
      rw [update_none hu] at hl
      left; exact ⟨c', hl, rfl⟩
    | some c =>
      rw [update_some hu f] at hl
      dsimp only at hl
      by_cases hfd : fd = fd'
      · rw [hfd, Table.lookup_insert_self] at hl
        obtain rfl := Option.some.inj hl
        left
        refine ⟨c, ?_, rfl⟩
        rw [hfd]; exact hu
      · rw [Table.lookup_insert_ne h.table_wf hfd] at hl
        left; exact ⟨c', hl, rfl⟩

/-- Incarnation dichotomy over a whole run: whatever occupies `fd` afterwards
either has the generation `fd` already had at the start of the run, or was
opened during the run and carries a generation at or above the starting
counter.  Generations from before the run and generations assigned during it
can never collide — this is the ABA exclusion. -/
theorem run_incarnation {r : Reactor σ} (h : r.GWF) (ops : List (Op σ)) (fd : Nat)
    {c' : Conn σ} (hl : ((r.run ops).table.lookup fd) = some c') :
    (∃ c, r.table.lookup fd = some c ∧ c.gen = c'.gen) ∨ r.nextGen ≤ c'.gen := by
  induction ops generalizing r with
  | nil => left; exact ⟨c', hl, rfl⟩
  | cons op ops ih =>
    dsimp only [run] at hl
    cases ih (h.step op) hl with
    | inl hsame =>
      obtain ⟨c₁, hl₁, hgen₁⟩ := hsame
      cases step_incarnation h op fd hl₁ with
      | inl h0 =>
        obtain ⟨c₀, hl₀, hg₀⟩ := h0
        left; exact ⟨c₀, hl₀, by rw [hg₀, hgen₁]⟩
      | inr hge =>
        right; omega
    | inr hge =>
      have := nextGen_mono_step r op
      right; omega

/-! ### Guard soundness -/

/-- A `(fd, gen)` token is *captured* at reactor state `r` when it denotes
the connection live at `fd` — the pair a dispatch records before crossing
the gap. -/
def Captured (r : Reactor σ) (fd g : Nat) : Prop :=
  ∃ c, r.table.lookup fd = some c ∧ c.gen = g

/-- A captured generation was assigned in the past. -/
theorem Captured.lt_next {r : Reactor σ} (h : r.GWF) {fd g : Nat}
    (hc : Captured r fd g) : g < r.nextGen := by
  obtain ⟨c, hl, hg⟩ := hc
  have := h.gen_lt fd c hl
  omega

/-- Shape of a successful resolution: the fd is live and the generations
match exactly. -/
theorem resolve_some {r : Reactor σ} {fd g : Nat} {st : σ}
    (hres : r.resolve fd g = some st) :
    ∃ c, r.table.lookup fd = some c ∧ c.gen = g ∧ c.state = st := by
  unfold resolve at hres
  cases hl : r.table.lookup fd with
  | none => rw [hl] at hres; exact Option.noConfusion hres
  | some c =>
    rw [hl] at hres
    have hres' : (if c.gen = g then some c.state else none) = some st := hres
    by_cases hg : c.gen = g
    · rw [if_pos hg] at hres'
      exact ⟨c, rfl, hg, Option.some.inj hres'⟩
    · rw [if_neg hg] at hres'
      exact Option.noConfusion hres'

/-- The sentinel never resolves: no live connection carries generation 0, so
a 0-token cannot match.  (In the implementation, 0-tagged events are the
reactor-internal ones that never cross the gap; the counter's skip-0 rule
keeps this disjointness through wraparound.) -/
theorem resolve_zero {r : Reactor σ} (h : r.GWF) (fd : Nat) :
    r.resolve fd 0 = none := by
  unfold resolve
  cases hl : r.table.lookup fd with
  | none => rfl
  | some c =>
    have := h.gen_pos fd c hl
    show (if c.gen = 0 then some c.state else none) = none
    rw [if_neg (by omega)]

/-- **Freshness.** A generation captured before a run is distinct from the
generation of any *new* incarnation the run put at that fd. -/
theorem captured_ne_newer {r : Reactor σ} (h : r.GWF) {fd g : Nat}
    (hcap : Captured r fd g) (ops : List (Op σ)) {c' : Conn σ}
    (hl : ((r.run ops).table.lookup fd) = some c')
    (hnew : ∀ c, r.table.lookup fd = some c → c.gen ≠ c'.gen) :
    c'.gen ≠ g := by
  cases run_incarnation h ops fd hl with
  | inl hsame =>
    obtain ⟨c, hlc, hgc⟩ := hsame
    exact absurd hgc (hnew c hlc)
  | inr hge =>
    have := hcap.lt_next h
    omega

/-- **Stale-guard soundness (Rank 3's headline).** Capture a `(fd, g)` token,
run any sequence of opens/closes/updates, and suppose `fd` is now occupied by
a *different* incarnation (any connection whose generation differs from what
`fd` held at capture time — in particular any connection opened after the fd
was recycled).  Then the guard rejects: the stale token resolves to `none`,
never to the newer connection's slot. -/
theorem stale_token_never_resolves {r : Reactor σ} (h : r.GWF) {fd g : Nat}
    (hcap : Captured r fd g) (ops : List (Op σ)) {c' : Conn σ}
    (hl : ((r.run ops).table.lookup fd) = some c')
    (hnew : ∀ c, r.table.lookup fd = some c → c.gen ≠ c'.gen) :
    (r.run ops).resolve fd g = none := by
  have hne : c'.gen ≠ g := captured_ne_newer h hcap ops hl hnew
  unfold resolve
  rw [hl]
  show (if c'.gen = g then some c'.state else none) = none
  rw [if_neg hne]

/-- Complement: a resolution that *does* succeed after a run identifies the
same incarnation the token was captured against — same fd, same generation,
still live. -/
theorem resolve_same_incarnation {r : Reactor σ} (h : r.GWF) {fd g : Nat}
    (hcap : Captured r fd g) (ops : List (Op σ)) {st : σ}
    (hres : (r.run ops).resolve fd g = some st) :
    ∃ c, ((r.run ops).table.lookup fd) = some c ∧ c.gen = g
      ∧ (∃ c₀, r.table.lookup fd = some c₀ ∧ c₀.gen = g) := by
  obtain ⟨c, hl, hg, _⟩ := resolve_some hres
  refine ⟨c, hl, hg, ?_⟩
  cases run_incarnation h ops fd hl with
  | inl hsame =>
    obtain ⟨c₀, hl₀, hg₀⟩ := hsame
    exact ⟨c₀, hl₀, by rw [hg₀, hg]⟩
  | inr hge =>
    -- the occupant would be a new incarnation, but its generation equals a
    -- captured (hence past) one — impossible.
    have := hcap.lt_next h
    omega

/-! ### The wraparound assumption — this rank's one named axiom

The counter above is `Nat`: it genuinely never repeats, and every theorem in
this file is unconditional.  The implementation's counter is a 64-bit machine
word advanced by wrapping increment (with the skip-0 rule).  The bridge is a
**named assumption**, stated here as the explicit hypothesis `NoWrap` rather
than a Lean `axiom`, so every use site is visible in a theorem's binders:

> the process assigns fewer than `2^64 - 1` generations over its lifetime.

Under `NoWrap` all assigned generations are below `2^64`, the mod-`2^64`
projection (what the hardware compares) is injective on them, and the machine
equality guard decides the model's equality (`guard_exact_of_noWrap`).
`noWrap_of_run_length` discharges the assumption for any concrete run bound:
a reactor would have to perform ~1.8 × 10^19 operations for the counters to
collide. -/

/-- The machine counter's modulus. -/
def genBound : Nat := 2 ^ 64

/-- The named wraparound assumption: the counter has not exhausted the
64-bit space. -/
def NoWrap (r : Reactor σ) : Prop := r.nextGen < genBound

/-- Under `NoWrap`, the mod-2^64 projection is injective on live
generations: two live connections whose generations agree modulo `2^64`
have equal generations. -/
theorem mod_inj_of_noWrap {r : Reactor σ} (h : r.GWF) (hw : NoWrap r)
    {fd fd' : Nat} {c c' : Conn σ}
    (hl : r.table.lookup fd = some c) (hl' : r.table.lookup fd' = some c')
    (hmod : c.gen % genBound = c'.gen % genBound) : c.gen = c'.gen := by
  have h1 := h.gen_lt fd c hl
  have h2 := h.gen_lt fd' c' hl'
  have hb1 : c.gen < genBound := by unfold NoWrap at hw; omega
  have hb2 : c'.gen < genBound := by unfold NoWrap at hw; omega
  rwa [Nat.mod_eq_of_lt hb1, Nat.mod_eq_of_lt hb2] at hmod

/-- Under `NoWrap`, the machine's truncated equality test on a live
connection's generation against a token assigned in the past decides the
model's exact equality: the guard as implemented is the guard as specified. -/
theorem guard_exact_of_noWrap {r : Reactor σ} (h : r.GWF) (hw : NoWrap r)
    {fd g : Nat} {c : Conn σ}
    (hl : r.table.lookup fd = some c) (hg : g < genBound) :
    (c.gen % genBound = g % genBound) ↔ c.gen = g := by
  have h1 := h.gen_lt fd c hl
  have hb : c.gen < genBound := by unfold NoWrap at hw; omega
  rw [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hg]

/-- Concrete discharge of `NoWrap`: any run from the initial reactor shorter
than `2^64 - 1` operations stays below the bound. -/
theorem noWrap_of_run_length (ops : List (Op σ))
    (hlen : ops.length < genBound - 1) :
    NoWrap ((empty : Reactor σ).run ops) := by
  have hrun := nextGen_run_le (empty : Reactor σ) ops
  have hb : 2 ≤ genBound := by decide
  unfold NoWrap
  have hemp : (empty : Reactor σ).nextGen = 1 := rfl
  omega

end Reactor

end Slab
