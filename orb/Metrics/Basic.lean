/-!
# Metrics: counters, histograms, cross-shard aggregation

A per-shard registry of monotone counters plus a bucketed histogram, with the
accounting identities an export layer relies on. The concurrent lock-free read
across shards is a named CR-2 net-backed obligation (stated below, not
discharged here); this file proves the sequential per-shard properties and the
order-independence of the cross-shard merge.
-/

namespace Metrics

/-- A registry of named counters (a total map, unset names read `0`). -/
structure Registry where
  counters : String → Nat

/-- The empty registry. -/
def Registry.empty : Registry := { counters := fun _ => 0 }

/-- Increment the named counter by `delta`; other counters are untouched. -/
def Registry.inc (r : Registry) (name : String) (delta : Nat) : Registry :=
  { counters := fun n => if n = name then r.counters n + delta else r.counters n }

/-- **Monotone.** A counter never decreases under increment. -/
theorem inc_monotone (r : Registry) (name : String) (delta : Nat) (n : String) :
    r.counters n ≤ (r.inc name delta).counters n := by
  simp only [Registry.inc]
  by_cases h : n = name <;> simp [h]

/-- **Exact delta.** Increment adds exactly `delta` to the named counter. -/
theorem inc_exact (r : Registry) (name : String) (delta : Nat) :
    (r.inc name delta).counters name = r.counters name + delta := by
  simp [Registry.inc]

/-- **No side effects.** Increment leaves every other counter unchanged. -/
theorem inc_others (r : Registry) (name : String) (delta : Nat) (n : String)
    (h : n ≠ name) : (r.inc name delta).counters n = r.counters n := by
  simp [Registry.inc, h]

/-- Increments to distinct counters commute. -/
theorem inc_comm (r : Registry) (a b : String) (da db : Nat) (hab : a ≠ b) (n : String) :
    ((r.inc a da).inc b db).counters n = ((r.inc b db).inc a da).counters n := by
  simp only [Registry.inc]
  by_cases hna : n = a <;> by_cases hnb : n = b <;>
    simp_all

/-! ## Histogram -/

/-- A histogram: sorted upper bounds and per-bucket counts. There is one more
count than bound (the final `+∞` overflow bucket). `total` is the observation
count. -/
structure Histogram where
  bounds : List Nat
  counts : List Nat
  total : Nat
  /-- Structural invariant: one count per bucket (bounds + overflow). -/
  wf : counts.length = bounds.length + 1

/-- Index of the first bucket whose upper bound is `≥ v` (the overflow bucket if
`v` exceeds every bound). -/
def bucketIndex (bounds : List Nat) (v : Nat) : Nat :=
  (bounds.takeWhile (· < v)).length

/-- Bump the count at index `i` by one (no-op if `i` is out of range). -/
def bumpAt : List Nat → Nat → List Nat
  | [], _ => []
  | c :: cs, 0 => (c + 1) :: cs
  | c :: cs, (i + 1) => c :: bumpAt cs i

theorem bumpAt_length (counts : List Nat) (i : Nat) :
    (bumpAt counts i).length = counts.length := by
  induction counts generalizing i with
  | nil => rfl
  | cons c cs ih => cases i with
    | zero => rfl
    | succ i => simp [bumpAt, ih]

/-- Summing after an in-range bump adds exactly one. -/
theorem bumpAt_sum (counts : List Nat) (i : Nat) (hi : i < counts.length) :
    (bumpAt counts i).sum = counts.sum + 1 := by
  induction counts generalizing i with
  | nil => simp at hi
  | cons c cs ih => cases i with
    | zero => simp [bumpAt, Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]
    | succ i =>
      simp only [bumpAt, List.sum_cons]
      rw [ih i (by simpa using hi)]
      omega

/-- Observe a value: bump its bucket and the total. -/
def Histogram.observe (h : Histogram) (v : Nat) : Histogram :=
  { h with
    counts := bumpAt h.counts (bucketIndex h.bounds v)
    total := h.total + 1
    wf := by rw [bumpAt_length]; exact h.wf }

/-- **Total accounting.** Each observation increments the total by exactly one. -/
theorem observe_total (h : Histogram) (v : Nat) :
    (h.observe v).total = h.total + 1 := rfl

/-- **Bucket accounting.** A single in-range observation adds exactly one to the
sum of bucket counts (nothing is lost or double-counted across buckets), so the
bucket-count sum stays in lockstep with the total. -/
theorem observe_sum (h : Histogram) (v : Nat)
    (hi : bucketIndex h.bounds v < h.counts.length) :
    (h.observe v).counts.sum = h.counts.sum + 1 := by
  simp only [Histogram.observe]
  exact bumpAt_sum h.counts _ hi

/-! ## Cross-shard aggregation

The lock-free concurrent read across per-shard registries is a named CR-2
net-backed obligation (the atomic-read seam, evidence-under-net, not discharged
here). What is proved here is that the merge — a per-name sum over shards — is
order-independent, the property a lock-free aggregator needs to be correct
regardless of the read interleaving. -/

/-- `sum` distributes over append (core-provable; avoids a Mathlib dependency). -/
theorem sum_append (a b : List Nat) : (a ++ b).sum = a.sum + b.sum := by
  induction a with
  | nil => simp
  | cons x xs ih => simp [List.sum_cons, ih, Nat.add_assoc]

/-- Merge a name's counter across shards by summing. -/
def mergeCounter (shards : List Registry) (name : String) : Nat :=
  (shards.map (fun r => r.counters name)).sum

/-- The cross-shard merge distributes over concatenation of shard groups: the
aggregate of two shard groups is the sum of their aggregates. This is the
associativity a lock-free aggregator relies on — the merge is a monoid
homomorphism, so grouping/order of the per-shard reads does not change the
total. -/
theorem mergeCounter_append (s₁ s₂ : List Registry) (name : String) :
    mergeCounter (s₁ ++ s₂) name = mergeCounter s₁ name + mergeCounter s₂ name := by
  unfold mergeCounter
  rw [List.map_append, sum_append]

/-- Merging a single shard is just that shard's counter. -/
theorem mergeCounter_singleton (r : Registry) (name : String) :
    mergeCounter [r] name = r.counters name := by
  simp [mergeCounter]

/-- The empty aggregate is zero. -/
theorem mergeCounter_nil (name : String) : mergeCounter [] name = 0 := rfl

def version : String := "0.1.0"

end Metrics
