import Mux.Priority

/-!
# Mux.RoundRobin — fairness for equal-urgency incremental streams

Non-incremental streams of the same urgency are served to completion in id
order (see `Mux.Scheduler.select_det_by_id`). Incremental streams of the same
urgency are instead *interleaved fairly*: each gets a turn before any is served
twice. We model this as a round-robin over the list of active incremental
stream ids at a fixed urgency.

`rrStep` moves the head to the back. `rrServe q n` collects the ids served in
the first `n` steps. The headline fairness bound is

```
rrServe q q.length = q            -- rrServe_cycle
```

i.e. within one full cycle (`q.length` steps) the served sequence is exactly
`q`: every id is served, and — when ids are distinct — exactly once, in order
(`rr_fair`, `rr_served_nodup`). The queue also returns to its initial state
after a full cycle (`rrRun_cycle`), so the schedule is genuinely periodic.
-/

namespace Mux
namespace RoundRobin

/-! ## List helpers (proved locally to avoid lemma-name drift) -/

/-- `take` of a prefix: taking ≤ `xs.length` from `xs ++ ys` ignores `ys`. -/
theorem take_append_le : ∀ (xs ys : List α) (n : Nat),
    n ≤ xs.length → (xs ++ ys).take n = xs.take n := by
  intro xs ys n
  induction xs generalizing n with
  | nil => intro h; simp only [List.length_nil, Nat.le_zero] at h; subst h; simp
  | cons x xs ih =>
    intro h
    cases n with
    | zero => simp
    | succ m =>
      have hm : m ≤ xs.length := by simp only [List.length_cons] at h; omega
      simp only [List.cons_append, List.take_succ_cons, ih m hm]

/-- `drop` of a prefix: dropping ≤ `xs.length` from `xs ++ ys` keeps all of
`ys`. -/
theorem drop_append_le : ∀ (xs ys : List α) (n : Nat),
    n ≤ xs.length → (xs ++ ys).drop n = xs.drop n ++ ys := by
  intro xs ys n
  induction xs generalizing n with
  | nil => intro h; simp only [List.length_nil, Nat.le_zero] at h; subst h; simp
  | cons x xs ih =>
    intro h
    cases n with
    | zero => simp
    | succ m =>
      have hm : m ≤ xs.length := by simp only [List.length_cons] at h; omega
      simp only [List.cons_append, List.drop_succ_cons, ih m hm]

/-! ## The round-robin step and served sequence -/

/-- One round-robin step: serve the head, rotate it to the back. -/
def rrStep : List StreamId → List StreamId
  | [] => []
  | x :: xs => xs ++ [x]

/-- The ids served in the first `n` steps (each step serves the current head). -/
def rrServe : List StreamId → Nat → List StreamId
  | _, 0 => []
  | q, (n + 1) =>
    match q with
    | [] => []
    | x :: xs => x :: rrServe (xs ++ [x]) n

/-- The queue state after `n` round-robin steps. -/
def rrRun : List StreamId → Nat → List StreamId
  | q, 0 => q
  | q, (n + 1) =>
    match q with
    | [] => []
    | x :: xs => rrRun (xs ++ [x]) n

/-! ## Served sequence within a partial cycle -/

/-- Within a cycle, the served prefix of length `n ≤ |q|` is exactly `q.take
n`: the ids come out in list order, none skipped, none repeated. -/
theorem rrServe_take : ∀ (q : List StreamId) (n : Nat),
    n ≤ q.length → rrServe q n = q.take n := by
  intro q n
  induction n generalizing q with
  | zero => intro _; simp [rrServe]
  | succ m ih =>
    intro h
    cases q with
    | nil => simp [rrServe]
    | cons x xs =>
      have hm : m ≤ xs.length := by simp only [List.length_cons] at h; omega
      have e1 : rrServe (xs ++ [x]) m = (xs ++ [x]).take m :=
        ih (xs ++ [x]) (by simp only [List.length_append, List.length_cons,
          List.length_nil]; omega)
      have e2 : (xs ++ [x]).take m = xs.take m := take_append_le xs [x] m hm
      simp only [rrServe, e1, e2, List.take_succ_cons]

/-- **Fairness bound.** Over one full cycle the served sequence is exactly the
active list `q`. -/
theorem rrServe_cycle (q : List StreamId) : rrServe q q.length = q := by
  rw [rrServe_take q q.length (Nat.le_refl _), List.take_length]

/-- Every active id is served within one cycle (no starvation). -/
theorem rr_fair (q : List StreamId) (x : StreamId) (hx : x ∈ q) :
    x ∈ rrServe q q.length := by
  rw [rrServe_cycle]; exact hx

/-- With distinct ids, each is served *exactly once* per cycle (the served
sequence is duplicate-free). -/
theorem rr_served_nodup (q : List StreamId) (h : q.Nodup) :
    (rrServe q q.length).Nodup := by
  rw [rrServe_cycle]; exact h

/-- Each active id occupies a definite slot `< |q|` within the cycle (a concrete
turn), and distinct ids occupy distinct slots. -/
theorem rr_turn_within_cycle (q : List StreamId) (x : StreamId) (hx : x ∈ q) :
    ∃ k, k < q.length ∧ (rrServe q q.length)[k]? = some x := by
  rw [rrServe_cycle]
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hx
  exact ⟨k, hk, by rw [List.getElem?_eq_getElem hk, hget]⟩

/-! ## Periodicity of the queue state -/

/-- After `n ≤ |q|` steps the queue is the left-rotation `q.drop n ++ q.take
n`. -/
theorem rrRun_rotate : ∀ (q : List StreamId) (n : Nat),
    n ≤ q.length → rrRun q n = q.drop n ++ q.take n := by
  intro q n
  induction n generalizing q with
  | zero => intro _; simp [rrRun]
  | succ m ih =>
    intro h
    cases q with
    | nil => simp [rrRun]
    | cons x xs =>
      have hm : m ≤ xs.length := by simp only [List.length_cons] at h; omega
      have e1 : rrRun (xs ++ [x]) m = (xs ++ [x]).drop m ++ (xs ++ [x]).take m :=
        ih (xs ++ [x]) (by simp only [List.length_append, List.length_cons,
          List.length_nil]; omega)
      have ed : (xs ++ [x]).drop m = xs.drop m ++ [x] := drop_append_le xs [x] m hm
      have et : (xs ++ [x]).take m = xs.take m := take_append_le xs [x] m hm
      simp only [rrRun, e1, ed, et, List.drop_succ_cons, List.take_succ_cons,
        List.append_assoc, List.singleton_append]

/-- **Periodicity.** After one full cycle the queue returns to its initial
state. -/
theorem rrRun_cycle (q : List StreamId) : rrRun q q.length = q := by
  rw [rrRun_rotate q q.length (Nat.le_refl _), List.drop_length, List.take_length,
    List.nil_append]

/-! ## Checker-verified vectors -/

/-- Three incremental streams get served a, b, c within one cycle. -/
example : rrServe [1, 2, 3] 3 = [1, 2, 3] := rfl
/-- After a full cycle the queue is back to [1,2,3]. -/
example : rrRun [1, 2, 3] 3 = [1, 2, 3] := rfl
/-- A partial cycle serves a prefix. -/
example : rrServe [1, 2, 3] 2 = [1, 2] := rfl

end RoundRobin
end Mux
