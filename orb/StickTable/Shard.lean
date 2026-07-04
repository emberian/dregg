/-
StickTable.Shard — the cross-shard merge, and the named CR-2 obligation.

The sequential model in `StickTable.Basic`/`Trace` is the *per-shard* view: one
shard, applied in order.  A real stick table is sharded across cores; a client's
observed counter for a key comes from the concurrent execution of the global
event stream, distributed over shards, then merged — per-key SUM of counters
(and, for last-seen, per-key MAX).

This file:

  * defines `aggCount` — the global counter as the per-key sum over shard tables;
  * proves `shard_merge_two` — the SEQUENTIAL-side merge-correctness fact: if the
    event stream is partitioned across shards and each shard runs the sequential
    model on its substream, the merged aggregate equals the whole-stream
    sequential count.  This is a genuine theorem (the counting identity is
    additive over a partition);
  * states **CR-2** (`CR2_LinearizesToSequential`) — the ONE remaining gap, that
    the *concurrent* execution linearizes to the sequential model.  It is stated
    as a well-typed proof obligation and deliberately NOT discharged here: this
    model has no concurrency semantics.  It is discharged externally, against a concurrency model (loom/Iris), not on this chain.
-/

import StickTable.Trace

namespace StickTable

/-- The global counter for `k` across a list of shard tables: the per-key sum of
the shards' counters.  This is the observable side of the merge (last-seen would
merge by `max`; the counter merges by `+`). -/
def aggCount (k : Nat) : List Table → Nat
  | [] => 0
  | s :: rest => getCount k s + aggCount k rest

@[simp] theorem aggCount_nil (k : Nat) : aggCount k [] = 0 := rfl

@[simp] theorem aggCount_cons (k : Nat) (s : Table) (rest : List Table) :
    aggCount k (s :: rest) = getCount k s + aggCount k rest := rfl

/-! ### Sequential-side merge correctness -/

/-- The counting identity is additive over a partition of the trace: the events
targeting `k` split cleanly between the two halves of any boolean partition. -/
theorem countFor_filter_partition (k : Nat) (q : Ev → Bool) (evs : List Ev) :
    countFor k evs
      = countFor k (evs.filter q) + countFor k (evs.filter (fun e => ! q e)) := by
  induction evs with
  | nil => simp [countFor]
  | cons ev rest ih =>
    cases hq : q ev with
    | true =>
      have h1 : (ev :: rest).filter q = ev :: rest.filter q := by simp [List.filter, hq]
      have h2 : (ev :: rest).filter (fun e => ! q e) = rest.filter (fun e => ! q e) := by
        simp [List.filter, hq]
      rw [h1, h2]
      simp only [countFor]
      rw [ih]
      generalize (if ev.key = k then (1 : Nat) else 0) = c
      omega
    | false =>
      have h1 : (ev :: rest).filter q = rest.filter q := by simp [List.filter, hq]
      have h2 : (ev :: rest).filter (fun e => ! q e) = ev :: rest.filter (fun e => ! q e) := by
        simp [List.filter, hq]
      rw [h1, h2]
      simp only [countFor]
      rw [ih]
      generalize (if ev.key = k then (1 : Nat) else 0) = c
      omega

/-- **Merge correctness (sequential side).**  Partition the event stream across
two shards by an arbitrary boolean assignment `q`; run each shard's substream
through the sequential model from empty.  The merged aggregate (per-key sum) is
exactly the whole-stream sequential counter.  This is the half of CR-2 that this
model can prove; the remaining half (concurrent = per-shard-sequential) is CR-2
itself. -/
theorem shard_merge_two (k : Nat) (q : Ev → Bool) (evs : List Ev) :
    getCount k (run [] evs)
      = getCount k (run [] (evs.filter q))
        + getCount k (run [] (evs.filter (fun e => ! q e))) := by
  rw [run_getCount_empty, run_getCount_empty, run_getCount_empty]
  exact countFor_filter_partition k q evs

/-- The same, phrased through the merge aggregate `aggCount`: the whole-stream
sequential counter equals the aggregate over the two shard-runs. -/
theorem run_eq_aggCount_two (k : Nat) (q : Ev → Bool) (evs : List Ev) :
    getCount k (run [] evs)
      = aggCount k [run [] (evs.filter q), run [] (evs.filter (fun e => ! q e))] := by
  simp only [aggCount_cons, aggCount_nil, Nat.add_zero]
  exact shard_merge_two k q evs

/-! ### CR-2 — the concurrency seam (STATED, NOT DISCHARGED) -/

/-- **CR-2 (cross-shard merge / linearizability) — a named runtime-backed obligation,
STATED here and deliberately NOT discharged.**

`concObserve evs k` denotes the counter a client actually observes for key `k`
after the CONCURRENT multi-shard execution of the global event stream `evs`
(lock-free atomic `fetch_add` on per-shard entries, then a merge snapshot summing
per-key counters).  This model contains no concurrency, so `concObserve` is left
abstract — a parameter standing for the real concurrent semantics.

CR-2 is the claim that the concurrent execution *linearizes to* the sequential
per-shard model of this library:

    concObserve evs k = getCount k (run [] evs)

i.e. there exists a sequential ordering of the events whose per-key counter the
concurrent run reproduces exactly.  `shard_merge_two` discharges the algebraic
half — that a merged partition of sequential shard-runs equals the whole-stream
sequential count.  The remaining half — that the real concurrent run equals such
a sequential per-shard run — is a property of the concurrency semantics (atomic
ordering + the merge snapshot), provable only against a concurrency model
(loom/Iris), and so is carried as an external proof obligation rather than proved on
this chain.

This is a `def`-valued `Prop` (a stated obligation), not an `axiom`: nothing in
this library depends on it, so the sequential theorems keep a clean axiom
footprint.  A future concurrent model discharges CR-2 by exhibiting a proof of
`CR2_LinearizesToSequential concObserve` for its `concObserve`. -/
def CR2_LinearizesToSequential (concObserve : List Ev → Nat → Nat) : Prop :=
  ∀ (evs : List Ev) (k : Nat), concObserve evs k = getCount k (run [] evs)

end StickTable
