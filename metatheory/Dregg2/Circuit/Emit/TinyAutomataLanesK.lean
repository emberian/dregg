/-
# Dregg2.Circuit.Emit.TinyAutomataLanesK — the `k`-LANE WITNESS (the scope gap, closed).

**This is Lean-authored AIR.** The descriptor is the `EffectVmDescriptor2` built by
`TinyAutomataCompose.lanesDesc`; the witness is a concrete `VmTrace`; the satisfaction is a theorem
over the EMITTED object. Rust authors nothing.

## What this file closes

`TinyAutomataSatisfiable.lanes2Wit_satisfies` is hard-coded to TWO lanes by construction, so in the
committed §7 cost law the LANES points at `k = 3` and `k = 4` were MEASURED BUT NOT WITNESSED —
cost-of-an-emitted-object rather than cost-of-a-provable-object. This file supplies the missing
witness, and supplies it GENERALLY: `lanesKWit_satisfies` is a `Satisfied2Public` witness for the
`k`-lane composed descriptor over an ARBITRARY lane bank `ds : Nat → TableDfa Nat Nat`, arbitrary
per-lane start states `qs : Nat → Nat`, arbitrary lane count `k`, and any non-empty word `w`.

The two open points are then closed as instances at `k = 3` and `k = 4` against the EXACT committed
descriptors (`TinyAutomataSatisfiable.lanesRunI 3 probeW` / `lanesRunI 4 probeW` — the objects §7
measures, reached by a `rfl` identity, not a re-authored look-alike).

## The shape that makes it possible, and the consistency check it demanded

Each lane declares its OWN traversed edges (`runTable (ds i) (qs i) w`, `|w|` rows), and all lanes
read the ONE shared symbol column. So each lane's `PublicLookupBalanced` is discharged by an
EQUALITY (`lanesRows_triples i`, then `List.Perm.refl`) and no COMMON Eulerian word is needed —
which is exactly what made the whole-graph lanes route unsatisfiable.

⚑ The obligation that had to be checked against the REAL `TinyAutomataCompose.forced_trace_length`:
`k` declared tables each pin the trace length, so the question is whether they pin ONE length or `k`
incompatible ones. `lanesK_forced_length` answers it as a THEOREM: every lane's table has exactly
`|w|` rows (`runTable_length`) and every lane is targeted by exactly ONE lookup
(`lanesK_lookupCount`), so every lane pins `t.rows.length = |w|` — the SAME number, for every
`i < k`, at every `k`. The pins are consistent; the witness goes through; the `k = 3, 4` lanes
points are satisfiable, not merely emitted.

## ⚑ THE RE-STATED §7 SCOPE NOTE (this file's reason to exist)

The committed header of `TinyAutomataSatisfiable` should now read:

  WITNESSED (a satisfying `Satisfied2Public` trace exists, so the cost is the cost of a PROVABLE
  object):
    * product-first at k = 1, 2, 3, 4 — `prodRunWit_satisfies`, general in k.
    * lanes at k = 1, 2, 3, 4 — `TinyAutomataLanesK.lanesKWit_satisfies`, general in k (and in the
      lane bank); the committed k = 2 instance is `lanesRunI2_satisfies`, and k = 3 / k = 4 are
      `lanesRunI3_satisfies` / `lanesRunI4_satisfies` against the very descriptors §7 measures.
  MEASURED BUT NOT WITNESSED: nothing on the run-table routes. The crossover is now witnessed on
  BOTH routes at EVERY measured k, so the law is a comparison of provable objects end to end.
  ALSO NOT WITNESSED (and openly so, unchanged): the reachability-minimised WHOLE-GRAPH product
  costs (area 12/36/72/150). The Eulerian obstruction stands there — no satisfying trace is known
  for any k, and they are quoted only as the price of an attestation the run-table discipline does
  not buy.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. NEW file; imports are
read-only (nothing in `TinyAutomataSatisfiable`, `TinyAutomataCompose` or `DfaRoutingTableEmit` is
edited). Every `#guard` is COMPILED EVALUATION of a closed `Bool` — it proves NO `Prop`; it pins
measured numbers and byte identities and nothing more. The load-bearing objects are the theorems.
-/
import Dregg2.Circuit.Emit.TinyAutomataSatisfiable

namespace Dregg2.Circuit.Emit.TinyAutomataLanesK

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Crypto.DfaAcceptanceAir (TableDfa classifyFrom)
open Dregg2.Circuit.Emit.DfaRoutingTableEmit (hash0 envAt_loc envAt_nxt)
open Dregg2.Circuit.Emit.TinyAutomataCompose
open Dregg2.Circuit.Emit.TinyAutomataSatisfiable

set_option autoImplicit false

/-! ## §1 — LIST PLUMBING: the three general list facts the `k`-lane bookkeeping needs.

All three are elementary inductions; they are stated here rather than searched for so the file has
no hidden dependency on a Mathlib name. -/

/-- `filterMap` distributes over `flatMap`. -/
theorem filterMap_flatMap {α β γ : Type} (l : List α) (g : α → List β) (f : β → Option γ) :
    (l.flatMap g).filterMap f = l.flatMap (fun x => (g x).filterMap f) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.filterMap_append, ih, List.flatMap_cons]

/-- A `flatMap` that never produces anything is empty. -/
theorem flatMap_const_nil {α β : Type} (l : List α) :
    l.flatMap (fun _ => ([] : List β)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, ih]; rfl

/-- Over `range k`, a per-index dispatch that MISSES every index below `k` is empty. -/
theorem range_flatMap_miss {α : Type} (a : List α) (i : Nat) :
    ∀ k, k ≤ i → (List.range k).flatMap (fun j => if j = i then a else []) = []
  | 0,     _ => rfl
  | k + 1, h => by
    rw [List.range_succ, List.flatMap_append, range_flatMap_miss a i k (by omega),
      List.nil_append]
    simp [if_neg (show ¬ (k = i) by omega)]

/-- Over `range k`, a per-index dispatch that HITS exactly `i < k` yields exactly that payload. -/
theorem range_flatMap_hit {α : Type} (a : List α) (i : Nat) :
    ∀ k, i < k → (List.range k).flatMap (fun j => if j = i then a else []) = a
  | 0,     h => absurd h (by omega)
  | k + 1, h => by
    rw [List.range_succ, List.flatMap_append]
    rcases Nat.lt_or_ge i k with hik | hik
    · rw [range_flatMap_hit a i k hik]
      simp only [List.flatMap_cons, List.flatMap_nil, if_neg (by omega : ¬ (k = i))]
      simp
    · have hik' : i = k := by omega
      subst hik'
      rw [range_flatMap_miss a i i (by omega)]
      simp

/-! ## §2 — THE `k`-LANE TRACE ROWS.

The state tuple is carried as a FUNCTION `Nat → Nat` (lane index ↦ state) and the lane bank as a
function `Nat → TableDfa Nat Nat`, so every per-lane fact is index-free — no `zipWith`, no `getD`,
no length side conditions inside the induction. Columns at or beyond the descriptor's declared
`traceWidth = 1 + 2k` are ZERO, so the witness is exactly the emitted object's width. -/

/-- Every lane steps on the SAME symbol. -/
def stepAll (ds : Nat → TableDfa Nat Nat) (qs : Nat → Nat) (y : Nat) : Nat → Nat :=
  fun i => (ds i).step (qs i) y

/-- One `1 + 2k`-column lanes row: the shared symbol in column 0, then `(current, next)` per lane;
zero at and beyond the declared width. -/
def lanesRow (k : Nat) (qs nx : Nat → Nat) (y : Nat) : Assignment :=
  fun c => if 1 + 2 * k ≤ c then 0
    else if c = 0 then Int.ofNat y
    else if c % 2 = 1 then Int.ofNat (qs (c / 2))
    else Int.ofNat (nx (c / 2 - 1))

theorem lanesRow_symbol (k : Nat) (qs nx : Nat → Nat) (y : Nat) :
    lanesRow k qs nx y LANE_SYMBOL = Int.ofNat y := by
  show (if 1 + 2 * k ≤ 0 then (0 : ℤ) else if (0 : Nat) = 0 then Int.ofNat y
        else if (0 : Nat) % 2 = 1 then Int.ofNat (qs (0 / 2)) else Int.ofNat (nx (0 / 2 - 1)))
      = Int.ofNat y
  rw [if_neg (by omega : ¬ (1 + 2 * k ≤ 0)), if_pos rfl]

theorem lanesRow_current (k : Nat) (qs nx : Nat → Nat) (y i : Nat) (hi : i < k) :
    lanesRow k qs nx y (laneCurrent i) = Int.ofNat (qs i) := by
  have h0 : ¬ (1 + 2 * k ≤ laneCurrent i) := by unfold laneCurrent; omega
  have h1 : ¬ (laneCurrent i = 0) := by unfold laneCurrent; omega
  have h2 : laneCurrent i % 2 = 1 := by unfold laneCurrent; omega
  have h3 : laneCurrent i / 2 = i := by unfold laneCurrent; omega
  show (if 1 + 2 * k ≤ laneCurrent i then (0 : ℤ) else if laneCurrent i = 0 then Int.ofNat y
        else if laneCurrent i % 2 = 1 then Int.ofNat (qs (laneCurrent i / 2))
        else Int.ofNat (nx (laneCurrent i / 2 - 1))) = Int.ofNat (qs i)
  rw [if_neg h0, if_neg h1, if_pos h2, h3]

theorem lanesRow_next (k : Nat) (qs nx : Nat → Nat) (y i : Nat) (hi : i < k) :
    lanesRow k qs nx y (laneNext i) = Int.ofNat (nx i) := by
  have h0 : ¬ (1 + 2 * k ≤ laneNext i) := by unfold laneNext; omega
  have h1 : ¬ (laneNext i = 0) := by unfold laneNext; omega
  have h2 : ¬ (laneNext i % 2 = 1) := by unfold laneNext; omega
  have h3 : laneNext i / 2 - 1 = i := by unfold laneNext; omega
  show (if 1 + 2 * k ≤ laneNext i then (0 : ℤ) else if laneNext i = 0 then Int.ofNat y
        else if laneNext i % 2 = 1 then Int.ofNat (qs (laneNext i / 2))
        else Int.ofNat (nx (laneNext i / 2 - 1))) = Int.ofNat (nx i)
  rw [if_neg h0, if_neg h1, if_neg h2, h3]

/-- **The `k`-lane run's trace rows**: one row per input symbol; every lane steps on that symbol. -/
def lanesRows (ds : Nat → TableDfa Nat Nat) (k : Nat) :
    (Nat → Nat) → List Nat → List Assignment
  | _,  []      => []
  | qs, y :: ys => lanesRow k qs (stepAll ds qs y) y :: lanesRows ds k (stepAll ds qs y) ys

theorem lanesRows_length (ds : Nat → TableDfa Nat Nat) (k : Nat) :
    ∀ (w : List Nat) (qs : Nat → Nat), (lanesRows ds k qs w).length = w.length
  | [],      _  => rfl
  | y :: ys, qs => by
    show (lanesRows ds k (stepAll ds qs y) ys).length + 1 = ys.length + 1
    rw [lanesRows_length ds k ys (stepAll ds qs y)]

/-- ⚑ **LANE `i`'s COLUMN TRIPLES ARE LANE `i`'s DECLARED RUN TABLE** — an EQUALITY, for every lane
independently, all of them reading the ONE shared symbol column. This is what removes the need for a
common Eulerian word: each lane's declared multiset IS that lane's own run. -/
theorem lanesRows_triples (ds : Nat → TableDfa Nat Nat) (k i : Nat) (hi : i < k) :
    ∀ (w : List Nat) (qs : Nat → Nat),
      (lanesRows ds k qs w).map
          (fun a => [a (laneCurrent i), a LANE_SYMBOL, a (laneNext i)])
        = exactPublicTable (runTable (ds i) (qs i) w)
  | [],      _  => rfl
  | y :: ys, qs => by
    show (fun a : Assignment => [a (laneCurrent i), a LANE_SYMBOL, a (laneNext i)])
        (lanesRow k qs (stepAll ds qs y) y)
        :: (lanesRows ds k (stepAll ds qs y) ys).map
             (fun a => [a (laneCurrent i), a LANE_SYMBOL, a (laneNext i)]) = _
    rw [lanesRows_triples ds k i hi ys (stepAll ds qs y)]
    show [lanesRow k qs (stepAll ds qs y) y (laneCurrent i),
          lanesRow k qs (stepAll ds qs y) y LANE_SYMBOL,
          lanesRow k qs (stepAll ds qs y) y (laneNext i)] :: _ = _
    rw [lanesRow_current k qs (stepAll ds qs y) y i hi, lanesRow_symbol,
      lanesRow_next k qs (stepAll ds qs y) y i hi]
    rfl

/-- Lane `i`'s rows CHAIN: row `n+1`'s `current` is row `n`'s `next`. -/
theorem lanesRows_chain (ds : Nat → TableDfa Nat Nat) (k i : Nat) (hi : i < k) :
    ∀ (w : List Nat) (qs : Nat → Nat) (n : Nat) (h : n + 1 < (lanesRows ds k qs w).length),
      ((lanesRows ds k qs w)[n + 1]'h) (laneCurrent i)
        = ((lanesRows ds k qs w)[n]'(Nat.lt_of_succ_lt h)) (laneNext i) := by
  intro w
  induction w with
  | nil => intro qs n h; simp [lanesRows] at h
  | cons y ys ih =>
    intro qs n h
    cases n with
    | zero =>
      cases ys with
      | nil => simp [lanesRows] at h
      | cons y' ys' =>
        show lanesRow k (stepAll ds qs y) (stepAll ds (stepAll ds qs y) y') y' (laneCurrent i)
          = lanesRow k qs (stepAll ds qs y) y (laneNext i)
        rw [lanesRow_current k _ _ y' i hi, lanesRow_next k qs _ y i hi]
    | succ m => exact ih (stepAll ds qs y) m (by simpa [lanesRows] using h)

/-- Lane `i`'s FIRST row carries lane `i`'s start state. -/
theorem lanesRows_head (ds : Nat → TableDfa Nat Nat) (k i : Nat) (hi : i < k)
    (qs : Nat → Nat) (w : List Nat) (hw : w ≠ []) (h : 0 < (lanesRows ds k qs w).length) :
    ((lanesRows ds k qs w)[0]'h) (laneCurrent i) = Int.ofNat (qs i) := by
  cases w with
  | nil => exact absurd rfl hw
  | cons y ys =>
    show lanesRow k qs (stepAll ds qs y) y (laneCurrent i) = _
    rw [lanesRow_current k qs (stepAll ds qs y) y i hi]

/-- Lane `i`'s LAST row's `next` IS lane `i`'s classification of the whole word. -/
theorem lanesRows_last (ds : Nat → TableDfa Nat Nat) (k i : Nat) (hi : i < k) :
    ∀ (w : List Nat) (qs : Nat → Nat) (n : Nat) (h : n < (lanesRows ds k qs w).length),
      n + 1 = (lanesRows ds k qs w).length →
      ((lanesRows ds k qs w)[n]'h) (laneNext i) = Int.ofNat (classifyFrom (ds i) (qs i) w) := by
  intro w
  induction w with
  | nil => intro qs n h _; simp [lanesRows] at h
  | cons y ys ih =>
    intro qs n h hlast
    cases n with
    | zero =>
      have hys : ys = [] := by
        have h0 : (lanesRows ds k (stepAll ds qs y) ys).length = 0 := by
          simp only [lanesRows, List.length_cons] at hlast
          omega
        rw [lanesRows_length ds k ys (stepAll ds qs y)] at h0
        exact List.eq_nil_of_length_eq_zero h0
      subst hys
      show lanesRow k qs (stepAll ds qs y) y (laneNext i) = _
      rw [lanesRow_next k qs (stepAll ds qs y) y i hi]
      rfl
    | succ m =>
      exact ih (stepAll ds qs y) m (by simpa [lanesRows] using h)
        (by simpa [lanesRows] using hlast)

/-! ## §3 — THE `k`-LANE PUBLIC INPUTS AND TABLE FAMILY. -/

/-- The `2k` public inputs: `(initial₀, final₀, …, initial_{k-1}, final_{k-1})`, zero beyond. -/
def lanesKPub (k : Nat) (qs fs : Nat → Nat) : Assignment :=
  fun j => if 2 * k ≤ j then 0
    else if j % 2 = 0 then Int.ofNat (qs (j / 2)) else Int.ofNat (fs (j / 2))

theorem lanesKPub_initial (k : Nat) (qs fs : Nat → Nat) (i : Nat) (hi : i < k) :
    lanesKPub k qs fs (2 * i) = Int.ofNat (qs i) := by
  have h0 : ¬ (2 * k ≤ 2 * i) := by omega
  have h1 : 2 * i % 2 = 0 := by omega
  have h2 : 2 * i / 2 = i := by omega
  show (if 2 * k ≤ 2 * i then (0 : ℤ) else if 2 * i % 2 = 0 then Int.ofNat (qs (2 * i / 2))
        else Int.ofNat (fs (2 * i / 2))) = Int.ofNat (qs i)
  rw [if_neg h0, if_pos h1, h2]

theorem lanesKPub_final (k : Nat) (qs fs : Nat → Nat) (i : Nat) (hi : i < k) :
    lanesKPub k qs fs (2 * i + 1) = Int.ofNat (fs i) := by
  have h0 : ¬ (2 * k ≤ 2 * i + 1) := by omega
  have h1 : ¬ ((2 * i + 1) % 2 = 0) := by omega
  have h2 : (2 * i + 1) / 2 = i := by omega
  show (if 2 * k ≤ 2 * i + 1 then (0 : ℤ)
        else if (2 * i + 1) % 2 = 0 then Int.ofNat (qs ((2 * i + 1) / 2))
        else Int.ofNat (fs ((2 * i + 1) / 2))) = Int.ofNat (fs i)
  rw [if_neg h0, if_neg h1, h2]

/-- The `k`-lane table family: lane `i`'s declared run table at lane `i`'s table id. -/
def lanesKTf (tbls : Nat → List (List Nat)) : TraceFamily :=
  fun id => match id with
    | .custom n => if 40 ≤ n then exactPublicTable (tbls (n - 40)) else []
    | _ => []

theorem lanesKTf_lane (tbls : Nat → List (List Nat)) (i : Nat) :
    lanesKTf tbls (LANE_TID i) = exactPublicTable (tbls i) := by
  show (if 40 ≤ 40 + i then exactPublicTable (tbls (40 + i - 40)) else []) = _
  rw [if_pos (Nat.le_add_right 40 i), Nat.add_sub_cancel_left]

/-! ## §4 — THE `k`-LANE DESCRIPTOR, DESTRUCTURED.

`lanesDesc` builds its tables by `getD` off the supplied list and its constraints by `flatMap` over
`range tbls.length`. These two lemmas turn that into per-index form, general in `k`. -/

theorem lanesK_getD (g : Nat → List (List Nat)) (k i : Nat) (hi : i < k) :
    ((List.range k).map g).getD i [] = g i := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem lanesK_tables (name : String) (g : Nat → List (List Nat)) (k : Nat) :
    (lanesDesc name ((List.range k).map g)).tables
      = (List.range k).map (fun i => laneTableDef i (g i)) := by
  show (List.range ((List.range k).map g).length).map
      (fun i => laneTableDef i (((List.range k).map g).getD i [])) = _
  rw [List.length_map, List.length_range]
  refine List.map_congr_left ?_
  intro i hi
  rw [lanesK_getD g k i (List.mem_range.mp hi)]

theorem lanesK_constraints (name : String) (g : Nat → List (List Nat)) (k : Nat) :
    (lanesDesc name ((List.range k).map g)).constraints
      = (List.range k).flatMap laneConstraints := by
  show (List.range ((List.range k).map g).length).flatMap laneConstraints = _
  rw [List.length_map, List.length_range]

theorem lanesK_traceWidth (name : String) (g : Nat → List (List Nat)) (k : Nat) :
    (lanesDesc name ((List.range k).map g)).traceWidth = 1 + 2 * k := by
  show 1 + 2 * ((List.range k).map g).length = _
  rw [List.length_map, List.length_range]

theorem lanesK_piCount (name : String) (g : Nat → List (List Nat)) (k : Nat) :
    (lanesDesc name ((List.range k).map g)).piCount = 2 * k := by
  show 2 * ((List.range k).map g).length = _
  rw [List.length_map, List.length_range]

/-- Lane table ids are collision-free. -/
theorem LANE_TID_inj {i j : Nat} (h : LANE_TID j = LANE_TID i) : j = i := by
  have := congrArg TableId.wireId h
  simp only [LANE_TID, TableId.wireId] at this
  omega

/-- ONE lane's four constraints contribute exactly ONE evaluated tuple to lane `i`'s lookup log —
its own, and only when it IS lane `i`. -/
theorem laneConstraints_tuples (row : Assignment) (i j : Nat) :
    (laneConstraints j).filterMap (fun c => match c with
        | .lookup l => if l.table = LANE_TID i then some (l.tuple.map (·.eval row)) else none
        | _ => none)
      = if j = i then [[row (laneCurrent i), row LANE_SYMBOL, row (laneNext i)]] else [] := by
  by_cases h : j = i
  · subst h
    simp [laneConstraints, EmittedExpr.eval]
  · have hne : ¬ (LANE_TID j = LANE_TID i) := fun heq => h (LANE_TID_inj heq)
    simp [laneConstraints, hne, h]

/-- ⚑ **LANE `i`'s LOOKUP LOG IS LANE `i`'s COLUMN TRIPLES** — general in `k`, for every `i < k`.
(The `k = 2` file proved this twice by `rfl` on a concrete two-element constraint list.) -/
theorem lanesK_lookupLog (name : String) (g : Nat → List (List Nat)) (k i : Nat) (hi : i < k)
    (t : VmTrace) :
    lookupLog (lanesDesc name ((List.range k).map g)) t (LANE_TID i)
      = t.rows.map (fun a => [a (laneCurrent i), a LANE_SYMBOL, a (laneNext i)]) := by
  show t.rows.flatMap (fun row => (lanesDesc name ((List.range k).map g)).constraints.filterMap
      (fun c => match c with
        | .lookup l => if l.table = LANE_TID i then some (l.tuple.map (·.eval row)) else none
        | _ => none)) = _
  rw [lanesK_constraints name g k]
  have hrow : ∀ row : Assignment,
      ((List.range k).flatMap laneConstraints).filterMap (fun c => match c with
        | .lookup l => if l.table = LANE_TID i then some (l.tuple.map (·.eval row)) else none
        | _ => none)
      = [[row (laneCurrent i), row LANE_SYMBOL, row (laneNext i)]] := by
    intro row
    rw [filterMap_flatMap]
    have hpt : (fun j => (laneConstraints j).filterMap (fun c => match c with
        | .lookup l => if l.table = LANE_TID i then some (l.tuple.map (·.eval row)) else none
        | _ => none))
        = fun j => if j = i then [[row (laneCurrent i), row LANE_SYMBOL, row (laneNext i)]]
          else [] := by
      funext j; exact laneConstraints_tuples row i j
    rw [hpt, range_flatMap_hit _ i k hi]
  induction t.rows with
  | nil => rfl
  | cons a rest ih => rw [List.flatMap_cons, ih, hrow a]; rfl

/-- The same count for `lookupCount` — exactly ONE lookup targets each lane's table, which is what
turns `forced_trace_length`'s `rows × lookupCount = declaredRows` into `rows = |w|`. -/
theorem lanesK_lookupCount (name : String) (g : Nat → List (List Nat)) (k i : Nat) (hi : i < k) :
    lookupCount (lanesDesc name ((List.range k).map g)) (LANE_TID i) = 1 := by
  show ((lanesDesc name ((List.range k).map g)).constraints.filterMap (lkOf (LANE_TID i))).length
    = 1
  rw [lanesK_constraints name g k, filterMap_flatMap]
  have hpt : (fun j => (laneConstraints j).filterMap (lkOf (LANE_TID i)))
      = fun j => if j = i then
          [(⟨LANE_TID i, [.var (laneCurrent i), .var LANE_SYMBOL, .var (laneNext i)]⟩ : Lookup)]
        else [] := by
    funext j
    by_cases h : j = i
    · subst h
      simp [laneConstraints, lkOf]
    · have hne : ¬ (LANE_TID j = LANE_TID i) := fun heq => h (LANE_TID_inj heq)
      simp [laneConstraints, lkOf, hne, h]
  rw [hpt, range_flatMap_hit _ i k hi]
  rfl

/-- The lanes family declares no memory ops… -/
theorem lanesK_memOps (name : String) (g : Nat → List (List Nat)) (k : Nat) :
    memOpsOf (lanesDesc name ((List.range k).map g)) = [] := by
  show (lanesDesc name ((List.range k).map g)).constraints.filterMap
    (fun c => match c with | .memOp m => some m | _ => none) = []
  rw [lanesK_constraints name g k, filterMap_flatMap]
  rw [show (fun j => (laneConstraints j).filterMap
      (fun c => match c with | .memOp m => some m | _ => none)) = fun _ => [] from
    funext (fun j => rfl)]
  exact flatMap_const_nil _

/-- …and no map ops. -/
theorem lanesK_mapOps (name : String) (g : Nat → List (List Nat)) (k : Nat) :
    mapOpsOf (lanesDesc name ((List.range k).map g)) = [] := by
  show (lanesDesc name ((List.range k).map g)).constraints.filterMap
    (fun c => match c with | .mapOp m => some m | _ => none) = []
  rw [lanesK_constraints name g k, filterMap_flatMap]
  rw [show (fun j => (laneConstraints j).filterMap
      (fun c => match c with | .mapOp m => some m | _ => none)) = fun _ => [] from
    funext (fun j => rfl)]
  exact flatMap_const_nil _

theorem lanesK_memLog (name : String) (g : Nat → List (List Nat)) (k : Nat) (t : VmTrace) :
    memLog (lanesDesc name ((List.range k).map g)) t = [] := by
  simp [memLog, lanesK_memOps]

theorem lanesK_mapLog (name : String) (g : Nat → List (List Nat)) (k : Nat) (t : VmTrace) :
    mapLog (lanesDesc name ((List.range k).map g)) t = [] := by
  simp [mapLog, lanesK_mapOps]

/-! ## §5 — ⚑ THE DELIVERABLE: the `k`-LANE WITNESS AND ITS SATISFACTION THEOREM. -/

/-- **The `k`-lane composed descriptor** over `k` RUN tables — lane `i` declares exactly the edges
lane `i` traverses on the shared word `w`. -/
def lanesKRunDesc (name : String) (ds : Nat → TableDfa Nat Nat) (qs : Nat → Nat) (k : Nat)
    (w : List Nat) : EffectVmDescriptor2 :=
  lanesDesc name ((List.range k).map (fun i => runTable (ds i) (qs i) w))

/-- **THE `k`-LANE WITNESS.** -/
def lanesKWit (ds : Nat → TableDfa Nat Nat) (qs : Nat → Nat) (k : Nat) (w : List Nat) : VmTrace :=
  { rows := lanesRows ds k qs w
  , pub  := lanesKPub k qs (fun i => classifyFrom (ds i) (qs i) w)
  , tf   := lanesKTf (fun i => runTable (ds i) (qs i) w) }

theorem lanesKWit_rows_ne (ds : Nat → TableDfa Nat Nat) (qs : Nat → Nat) (k : Nat)
    {w : List Nat} (hw : w ≠ []) : (lanesKWit ds qs k w).rows ≠ [] := by
  intro h
  apply hw
  have h0 : (lanesRows ds k qs w).length = 0 := by
    rw [show lanesRows ds k qs w = [] from h]; rfl
  rw [lanesRows_length ds k w qs] at h0
  exact List.eq_nil_of_length_eq_zero h0

/-- ⚑ **THE GATE, GENERAL IN `k`** — a real `Satisfied2Public` witness for the `k`-LANE composed
descriptor, over an ARBITRARY lane bank, arbitrary per-lane start states, arbitrary `k`, and any
non-empty word. Every leg is discharged by construction: each lane's transition lookup by
`lanesRows_triples i`, each lane's continuity window by `lanesRows_chain i`, each lane's two
boundary pins by the head/last rows, and each lane's exact-multiset LogUp balance by
`lanesK_lookupLog` + `lanesRows_triples` — an EQUALITY, so `List.Perm.refl`. No common Eulerian word
is required, because no lane declares an edge it does not traverse. -/
theorem lanesKWit_satisfies (ds : Nat → TableDfa Nat Nat) (qs : Nat → Nat) (k : Nat)
    (w : List Nat) (hw : w ≠ []) (name : String) :
    Satisfied2Public hash0 (lanesKRunDesc name ds qs k w)
      (fun _ => 0) (fun _ => (0, 0)) [] (lanesKWit ds qs k w) where
  rowConstraints := by
    intro n hn c hc
    have hn' : n < (lanesRows ds k qs w).length := hn
    have hloc : (envAt (lanesKWit ds qs k w) n).loc = (lanesRows ds k qs w)[n]'hn' :=
      envAt_loc (t := lanesKWit ds qs k w) hn
    have hnotlast : (n + 1 == (lanesKWit ds qs k w).rows.length) = false →
        n + 1 < (lanesRows ds k qs w).length := by
      intro hnl
      have hne' : ¬ (n + 1 = (lanesRows ds k qs w).length) := by
        intro hEq
        rw [show (lanesKWit ds qs k w).rows = lanesRows ds k qs w from rfl, hEq] at hnl
        simp at hnl
      omega
    rw [show lanesKRunDesc name ds qs k w
        = lanesDesc name ((List.range k).map (fun i => runTable (ds i) (qs i) w)) from rfl,
      lanesK_constraints] at hc
    obtain ⟨i, hi, hci⟩ := List.mem_flatMap.mp hc
    have hik : i < k := List.mem_range.mp hi
    simp only [laneConstraints, List.mem_cons, List.not_mem_nil, or_false] at hci
    rcases hci with rfl | rfl | rfl | rfl
    · -- lane `i` lookup: the row's triple is a DECLARED row of lane `i`'s table, by construction
      show [(envAt (lanesKWit ds qs k w) n).loc (laneCurrent i),
            (envAt (lanesKWit ds qs k w) n).loc LANE_SYMBOL,
            (envAt (lanesKWit ds qs k w) n).loc (laneNext i)]
        ∈ lanesKTf (fun i => runTable (ds i) (qs i) w) (LANE_TID i)
      rw [hloc, lanesKTf_lane, ← lanesRows_triples ds k i hik w qs]
      exact List.mem_map.mpr ⟨(lanesRows ds k qs w)[n]'hn', List.getElem_mem hn', rfl⟩
    · -- lane `i` continuity
      show WindowConstraint.holdsAt (envAt (lanesKWit ds qs k w) n)
        (n + 1 == (lanesKWit ds qs k w).rows.length)
        ⟨.add (.nxt (laneCurrent i)) (.mul (.const (-1)) (.loc (laneNext i))), true⟩
      simp only [WindowConstraint.holdsAt, if_true]
      intro hnl
      have hlt := hnotlast hnl
      have hnxt : (envAt (lanesKWit ds qs k w) n).nxt = (lanesRows ds k qs w)[n + 1]'hlt :=
        envAt_nxt (t := lanesKWit ds qs k w) hlt
      have hch : ((lanesRows ds k qs w)[n + 1]'hlt) (laneCurrent i)
          = ((lanesRows ds k qs w)[n]'hn') (laneNext i) :=
        lanesRows_chain ds k i hik w qs n hlt
      simp only [WindowExpr.eval]
      rw [hloc, hnxt, hch]
      have hz : ((lanesRows ds k qs w)[n]'hn') (laneNext i)
          + (-1) * ((lanesRows ds k qs w)[n]'hn') (laneNext i) = 0 := by ring
      rw [hz]
    · -- lane `i` initial pin
      show (n == 0) = true → (envAt (lanesKWit ds qs k w) n).loc (laneCurrent i)
        ≡ (envAt (lanesKWit ds qs k w) n).pub (2 * i) [ZMOD 2013265921]
      intro hf
      have hn0 : n = 0 := by simpa using hf
      subst hn0
      rw [hloc, lanesRows_head ds k i hik qs w hw hn']
      show Int.ofNat (qs i) ≡ lanesKPub k qs (fun i => classifyFrom (ds i) (qs i) w) (2 * i)
        [ZMOD 2013265921]
      rw [lanesKPub_initial k qs _ i hik]
    · -- lane `i` final pin
      show (n + 1 == (lanesKWit ds qs k w).rows.length) = true →
        (envAt (lanesKWit ds qs k w) n).loc (laneNext i)
          ≡ (envAt (lanesKWit ds qs k w) n).pub (2 * i + 1) [ZMOD 2013265921]
      intro hl
      have hlast : n + 1 = (lanesRows ds k qs w).length :=
        (by simpa using hl : n + 1 = (lanesKWit ds qs k w).rows.length)
      rw [hloc, lanesRows_last ds k i hik w qs n hn' hlast]
      show Int.ofNat (classifyFrom (ds i) (qs i) w)
        ≡ lanesKPub k qs (fun i => classifyFrom (ds i) (qs i) w) (2 * i + 1) [ZMOD 2013265921]
      rw [lanesKPub_final k qs _ i hik]
  rowHashes := by intro n _; trivial
  rowRanges := by
    intro n _ r hr
    simp only [lanesKRunDesc, lanesDesc, List.not_mem_nil] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by
    rw [show lanesKRunDesc name ds qs k w
      = lanesDesc name ((List.range k).map (fun i => runTable (ds i) (qs i) w)) from rfl,
      lanesK_memLog]
    simp
  memDisciplined := by
    rw [show lanesKRunDesc name ds qs k w
      = lanesDesc name ((List.range k).map (fun i => runTable (ds i) (qs i) w)) from rfl,
      lanesK_memLog]
    trivial
  memBalanced := by
    rw [show lanesKRunDesc name ds qs k w
      = lanesDesc name ((List.range k).map (fun i => runTable (ds i) (qs i) w)) from rfl,
      lanesK_memLog]
    exact memCheck_nil _ _
  memTableFaithful := by
    rw [show lanesKRunDesc name ds qs k w
      = lanesDesc name ((List.range k).map (fun i => runTable (ds i) (qs i) w)) from rfl,
      lanesK_memLog]
    rfl
  mapTableFaithful := by
    rw [show lanesKRunDesc name ds qs k w
      = lanesDesc name ((List.range k).map (fun i => runTable (ds i) (qs i) w)) from rfl,
      lanesK_mapLog]
    rfl
  publicTablesFaithful := by
    intro td htd
    rw [show lanesKRunDesc name ds qs k w
        = lanesDesc name ((List.range k).map (fun i => runTable (ds i) (qs i) w)) from rfl,
      lanesK_tables] at htd
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp htd
    have hik : i < k := List.mem_range.mp hi
    show lanesKTf (fun i => runTable (ds i) (qs i) w) (LANE_TID i)
      = exactPublicTable (runTable (ds i) (qs i) w)
    rw [lanesKTf_lane]
  publicLookupBalanced := by
    intro td htd
    rw [show lanesKRunDesc name ds qs k w
        = lanesDesc name ((List.range k).map (fun i => runTable (ds i) (qs i) w)) from rfl,
      lanesK_tables] at htd
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp htd
    have hik : i < k := List.mem_range.mp hi
    show (lookupLog (lanesDesc name ((List.range k).map (fun i => runTable (ds i) (qs i) w)))
      (lanesKWit ds qs k w) (LANE_TID i)).Perm (exactPublicTable (runTable (ds i) (qs i) w))
    rw [lanesK_lookupLog _ _ k i hik]
    exact (lanesRows_triples ds k i hik w qs) ▸ List.Perm.refl _

/-! ## §6 — ⚑ THE CONSISTENCY CHECK THE LANE ROUTE OWED: `k` TABLES PIN **ONE** TRACE LENGTH.

`forced_trace_length` says a declared exact-public table pins `rows × lookupCount = declaredRows`.
A `k`-lane descriptor declares `k` tables, so a priori it could pin `k` INCOMPATIBLE lengths and be
unsatisfiable for `k ≥ 2` on arithmetic alone. Under the RUN discipline every lane's table has
exactly `|w|` rows and exactly one lookup, so every lane pins the SAME `|w|` — the pins agree, and
the witness above is not accidental. -/

theorem lanesK_forced_length {name : String} {ds : Nat → TableDfa Nat Nat} {qs : Nat → Nat}
    {k : Nat} {w : List Nat} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2Public hash0 (lanesKRunDesc name ds qs k w) minit mfin maddrs t)
    (i : Nat) (hi : i < k) :
    t.rows.length = w.length := by
  have htd : laneTableDef i (runTable (ds i) (qs i) w)
      ∈ (lanesKRunDesc name ds qs k w).tables := by
    rw [show lanesKRunDesc name ds qs k w
        = lanesDesc name ((List.range k).map (fun i => runTable (ds i) (qs i) w)) from rfl,
      lanesK_tables]
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  have h := forced_trace_length hsat htd (rows := runTable (ds i) (qs i) w) rfl
  rw [show (laneTableDef i (runTable (ds i) (qs i) w)).id = LANE_TID i from rfl,
    show lanesKRunDesc name ds qs k w
      = lanesDesc name ((List.range k).map (fun i => runTable (ds i) (qs i) w)) from rfl,
    lanesK_lookupCount _ _ k i hi, Nat.mul_one, runTable_length] at h
  exact h

/-- WHY the `k` pins agree — the declared row counts are UNIFORM across lanes (each lane declares
exactly the `|w|` edges it traverses), so the `k` instances of `forced_trace_length` demand the same
number. This is the arithmetic fact `lanesK_forced_length` turns into ONE consistent pin; it carries
no satisfaction hypothesis and claims none. -/
theorem lanesK_declared_rows_uniform (ds : Nat → TableDfa Nat Nat) (qs : Nat → Nat)
    (w : List Nat) (i j : Nat) :
    (runTable (ds i) (qs i) w).length = (runTable (ds j) (qs j) w).length := by
  rw [runTable_length, runTable_length]

/-- The word EVERY lane reads is the ONE shared word `w` (the shared symbol column, read off the
witness). -/
theorem lanesRows_symbols (ds : Nat → TableDfa Nat Nat) (k : Nat) :
    ∀ (w : List Nat) (qs : Nat → Nat),
      (lanesRows ds k qs w).map (fun a => (a LANE_SYMBOL).toNat) = w
  | [],      _  => rfl
  | y :: ys, qs => by
    show (lanesRow k qs (stepAll ds qs y) y LANE_SYMBOL).toNat
        :: (lanesRows ds k (stepAll ds qs y) ys).map (fun a => (a LANE_SYMBOL).toNat) = y :: ys
    rw [lanesRows_symbols ds k ys (stepAll ds qs y), lanesRow_symbol]
    rfl

/-- ⚑ **THE LANES ROUTE'S EXPOSURE STATEMENT** (the analogue of `prodRunWit_exposes_components` on
the other route): the satisfying `k`-lane trace reads exactly `w` off its ONE shared symbol column,
and lane `i`'s two public inputs are lane `i`'s own start state and lane `i`'s own classification of
that same word. Every lane's verdict on the SAME word, exposed by the one composed descriptor, with
a trace that exists. -/
theorem lanesKWit_exposes_components (ds : Nat → TableDfa Nat Nat) (qs : Nat → Nat) (k : Nat)
    (w : List Nat) (i : Nat) (hi : i < k) :
    (lanesKWit ds qs k w).rows.map (fun a => (a LANE_SYMBOL).toNat) = w
      ∧ (lanesKWit ds qs k w).pub (2 * i) = Int.ofNat (qs i)
      ∧ (lanesKWit ds qs k w).pub (2 * i + 1) = Int.ofNat (classifyFrom (ds i) (qs i) w) := by
  refine ⟨lanesRows_symbols ds k w qs, ?_, ?_⟩
  · show lanesKPub k qs (fun i => classifyFrom (ds i) (qs i) w) (2 * i) = _
    exact lanesKPub_initial k qs _ i hi
  · show lanesKPub k qs (fun i => classifyFrom (ds i) (qs i) w) (2 * i + 1) = _
    exact lanesKPub_final k qs (fun i => classifyFrom (ds i) (qs i) w) i hi

/-- The witness itself realises that pinned length: `|w|` rows, at every `k`. -/
theorem lanesKWit_length (ds : Nat → TableDfa Nat Nat) (qs : Nat → Nat) (k : Nat) (w : List Nat) :
    (lanesKWit ds qs k w).rows.length = w.length :=
  lanesRows_length ds k w qs

/-! ## §7 — ⚑ THE TWO OPEN POINTS, CLOSED: `k = 3` and `k = 4` on the COMMITTED descriptors.

`TinyAutomataSatisfiable.lanesRunI k probeW` is the object §7's cost law MEASURES. The instances
below are witnesses for exactly that object (reached by `rfl` — the same emitted descriptor, not a
re-authored look-alike). -/

/-- The independent bank as a lane-indexed function (`indep` is 4 machines; lanes at index ≥ 4
repeat the first, which is irrelevant at `k ≤ 4` and keeps the bank total). -/
def indepAt (i : Nat) : TableDfa Nat Nat := indep.getD i modTwoDfa

/-- Every lane starts in state 0. -/
def zeroStates : Nat → Nat := fun _ => 0

/-- The `k`-lane run descriptor over the independent bank, in `lanesKRunDesc` form. -/
def lanesRunIK (k : Nat) (w : List Nat) : EffectVmDescriptor2 :=
  lanesKRunDesc s!"tiny-automata-indep-lanes-run-k{k}::exact-public-v1" indepAt zeroStates k w

/-- The function-indexed bank builds the SAME descriptor as the committed list-indexed one at
`k = 3` (a `rfl` identity of the EMITTED objects, not a resemblance). -/
theorem lanesRunIK_eq_3 : lanesRunIK 3 probeW = lanesRunI 3 probeW := rfl

/-- …and at `k = 4`. -/
theorem lanesRunIK_eq_4 : lanesRunIK 4 probeW = lanesRunI 4 probeW := rfl

/-- …and at the already-witnessed `k = 2` and the degenerate `k = 1`, so the whole measured lanes
family is the same object family. -/
theorem lanesRunIK_eq_1 : lanesRunIK 1 probeW = lanesRunI 1 probeW := rfl

theorem lanesRunIK_eq_2 : lanesRunIK 2 probeW = lanesRunI 2 probeW := rfl

/-- ⚑ **`k = 3` — WITNESSED.** The third measured lanes point now carries a satisfying trace. -/
theorem lanesRunI3_satisfies :
    Satisfied2Public hash0 (lanesRunI 3 probeW) (fun _ => 0) (fun _ => (0, 0)) []
      (lanesKWit indepAt zeroStates 3 probeW) := by
  rw [← lanesRunIK_eq_3]
  exact lanesKWit_satisfies indepAt zeroStates 3 probeW probeW_ne _

/-- ⚑ **`k = 4` — WITNESSED.** -/
theorem lanesRunI4_satisfies :
    Satisfied2Public hash0 (lanesRunI 4 probeW) (fun _ => 0) (fun _ => (0, 0)) []
      (lanesKWit indepAt zeroStates 4 probeW) := by
  rw [← lanesRunIK_eq_4]
  exact lanesKWit_satisfies indepAt zeroStates 4 probeW probeW_ne _

/-- And the same construction re-derives the two already-closed points, so ONE theorem now covers
the whole measured lanes family `k = 1, 2, 3, 4`. -/
theorem lanesRunI1_satisfies :
    Satisfied2Public hash0 (lanesRunI 1 probeW) (fun _ => 0) (fun _ => (0, 0)) []
      (lanesKWit indepAt zeroStates 1 probeW) := by
  rw [← lanesRunIK_eq_1]
  exact lanesKWit_satisfies indepAt zeroStates 1 probeW probeW_ne _

theorem lanesRunI2_satisfies' :
    Satisfied2Public hash0 (lanesRunI 2 probeW) (fun _ => 0) (fun _ => (0, 0)) []
      (lanesKWit indepAt zeroStates 2 probeW) := by
  rw [← lanesRunIK_eq_2]
  exact lanesKWit_satisfies indepAt zeroStates 2 probeW probeW_ne _

/-- NON-VACUITY of the length pin: `lanesK_forced_length` FIRES on this file's own satisfying
`k = 4` witness — lane 3 of 4 pins the trace to exactly the rows the witness has. The hypothesis is
inhabited, so the pin is a real constraint on a real witness, not an empty implication. -/
theorem lanesK_forced_length_fires :
    (lanesKWit indepAt zeroStates 4 probeW).rows.length = probeW.length :=
  lanesK_forced_length (lanesKWit_satisfies indepAt zeroStates 4 probeW probeW_ne
    "tiny-automata-indep-lanes-run-k4::exact-public-v1") 3 (by omega)

/-- The same pin from LANE 0 of the same witness — the `k` pins really do agree on one length. -/
theorem lanesK_forced_length_fires_lane0 :
    (lanesKWit indepAt zeroStates 4 probeW).rows.length = probeW.length :=
  lanesK_forced_length (lanesKWit_satisfies indepAt zeroStates 4 probeW probeW_ne
    "tiny-automata-indep-lanes-run-k4::exact-public-v1") 0 (by omega)

/-- The trace length of every witnessed lanes point IS the probe word length — 8 rows, at every
`k`, which is the `forcedTraceRows := .pinned 8` the cost law reads off the descriptor. -/
theorem lanesKWit_probe_length (k : Nat) :
    (lanesKWit indepAt zeroStates k probeW).rows.length = 8 := by
  rw [lanesKWit_length]
  rfl

/-! ### §7a — ⚑ THE FALSIFIERS: the gate DISCRIMINATES.

A witness theorem is worth nothing if the descriptor accepts anything. These two are `Prop`-level
REFUSALS, each derived from a different leg of the denotation. -/

/-- A lane bank that is WRONG at lane 1: it runs "an even number of 1s" where the descriptor
declares "the count of 1s is divisible by 3". Every other lane is correct. -/
def badAt (i : Nat) : TableDfa Nat Nat := if i = 1 then modTwoDfa else indepAt i

/-- ⚑ **FALSIFIER 1 (content).** A trace whose lane 1 runs the WRONG automaton — right width, right
length, right shared word, every other lane correct — is REFUSED. The exact-public LogUp balance
forces lane 1's column triples to be a permutation of lane 1's DECLARED run table, and the two
multisets differ (they differ already in the sum of their `next` column). -/
theorem lanesKWit_wrong_lane_refuted (name : String) :
    ¬ Satisfied2Public hash0 (lanesKRunDesc name indepAt zeroStates 2 probeW)
      (fun _ => 0) (fun _ => (0, 0)) [] (lanesKWit badAt zeroStates 2 probeW) := by
  intro hsat
  have htd : laneTableDef 1 (runTable (indepAt 1) (zeroStates 1) probeW)
      ∈ (lanesKRunDesc name indepAt zeroStates 2 probeW).tables := by
    rw [show lanesKRunDesc name indepAt zeroStates 2 probeW
        = lanesDesc name ((List.range 2).map
            (fun i => runTable (indepAt i) (zeroStates i) probeW)) from rfl,
      lanesK_tables]
    exact List.mem_map.mpr ⟨1, List.mem_range.mpr (by omega), rfl⟩
  have hperm := hsat.exact_lookup_perm htd
    (rows := runTable (indepAt 1) (zeroStates 1) probeW) rfl
  rw [show (laneTableDef 1 (runTable (indepAt 1) (zeroStates 1) probeW)).id = LANE_TID 1 from rfl,
    show lanesKRunDesc name indepAt zeroStates 2 probeW
      = lanesDesc name ((List.range 2).map
          (fun i => runTable (indepAt i) (zeroStates i) probeW)) from rfl,
    lanesK_lookupLog name _ 2 1 (by omega),
    show (lanesKWit badAt zeroStates 2 probeW).rows = lanesRows badAt 2 zeroStates probeW from rfl,
    lanesRows_triples badAt 2 1 (by omega) probeW zeroStates] at hperm
  have hsum := (hperm.map (fun r => r.getD 2 0)).sum_eq
  revert hsum
  decide

/-- ⚑ **FALSIFIER 2 (length).** A trace that is the correct run of a DIFFERENT (shorter) word is
REFUSED — `lanesK_forced_length` pins the trace to `|w|` rows, so a 4-row trace cannot satisfy the
8-symbol descriptor. This is the `forced_trace_length` law biting on the lanes route. -/
theorem lanesKWit_wrong_word_refuted (name : String) :
    ¬ Satisfied2Public hash0 (lanesKRunDesc name indepAt zeroStates 4 probeW)
      (fun _ => 0) (fun _ => (0, 0)) [] (lanesKWit indepAt zeroStates 4 (probeW.take 4)) := by
  intro hsat
  have h := lanesK_forced_length hsat 0 (by omega)
  rw [lanesKWit_length] at h
  exact absurd h (by decide)

/-! ## §8 — THE MEASUREMENT, over objects that ALL have witnesses now.

⚠ Every `#guard` here is COMPILED EVALUATION of a closed `Bool` — it proves NO `Prop`. The `Prop`
content is §5's witness, §6's length pins, and §7's four instances. These are the SAME numbers the
committed §7 quotes; what changed is their STATUS on the lanes side: cost-of-a-provable-object at
every `k` measured, no longer cost-of-an-emitted-object at `k = 3, 4`. -/

-- Byte identity of the witnessed object and the measured object, at every k (the `rfl` theorems
-- above are the Prop-level version; this pins the WIRE bytes too).
#guard (List.map (fun k => emitVmJson2 (lanesRunIK k probeW) == emitVmJson2 (lanesRunI k probeW))
  [1, 2, 3, 4]) == [true, true, true, true]

-- The lanes cost record, k = 1…4 — every point now witnessed.
#guard (List.map (fun k => costOf (lanesRunIK k probeW)) [1, 2, 3, 4]) ==
  [ { traceWidth := 3,  piCount := 2, constraints := 4,  tables := 1
    , declaredRows := 8,  forcedTraceRows := .pinned 8, nonlinearMults := 0 }
  , { traceWidth := 5,  piCount := 4, constraints := 8,  tables := 2
    , declaredRows := 16, forcedTraceRows := .pinned 8, nonlinearMults := 0 }
  , { traceWidth := 7,  piCount := 6, constraints := 12, tables := 3
    , declaredRows := 24, forcedTraceRows := .pinned 8, nonlinearMults := 0 }
  , { traceWidth := 9,  piCount := 8, constraints := 16, tables := 4
    , declaredRows := 32, forcedTraceRows := .pinned 8, nonlinearMults := 0 } ]

-- ⚑ THE LAW IN AREA, both routes witnessed at every measured k: product-first FLAT at 24;
-- lanes 24, 40, 56, 72. Tie at k = 1, product-first strictly cheaper from k = 2 on.
#guard (List.map (fun k => ((costOf (prodRunDesc k probeW)).area, (costOf (lanesRunIK k probeW)).area))
  [1, 2, 3, 4]) == [(some 24, some 24), (some 24, some 40), (some 24, some 56), (some 24, some 72)]

-- The same in emitted descriptor bytes (the verifier-held object).
#guard (List.map (fun k => (jsonBytes (prodRunDesc k probeW), jsonBytes (lanesRunIK k probeW)))
  [1, 2, 3, 4]) == [(669, 672), (669, 1168), (680, 1664), (685, 2160)]

-- The witness's own realised trace length at each k (compiled evaluation of the same 8 the
-- `Prop`-level `lanesKWit_probe_length` proves).
#guard (List.map (fun k => (lanesKWit indepAt zeroStates k probeW).rows.length) [1, 2, 3, 4])
  == [8, 8, 8, 8]

-- The witnessed lanes' exposed public finals at k = 4: lane i's `pi[2i+1]` is lane i's own verdict
-- on the probe word — [1, 2, 1, 2], the same component verdicts the product route packs into 102.
#guard (List.map (fun i => (lanesKWit indepAt zeroStates 4 probeW).pub (2 * i + 1)) [0, 1, 2, 3])
  == [1, 2, 1, 2]

/-! ## §9 — axiom tripwires. -/

#assert_axioms filterMap_flatMap
#assert_axioms flatMap_const_nil
#assert_axioms range_flatMap_miss
#assert_axioms range_flatMap_hit
#assert_axioms lanesRow_symbol
#assert_axioms lanesRow_current
#assert_axioms lanesRow_next
#assert_axioms lanesRows_length
#assert_axioms lanesRows_triples
#assert_axioms lanesRows_chain
#assert_axioms lanesRows_head
#assert_axioms lanesRows_last
#assert_axioms lanesKPub_initial
#assert_axioms lanesKPub_final
#assert_axioms lanesKTf_lane
#assert_axioms lanesK_getD
#assert_axioms lanesK_tables
#assert_axioms lanesK_constraints
#assert_axioms lanesK_traceWidth
#assert_axioms lanesK_piCount
#assert_axioms LANE_TID_inj
#assert_axioms laneConstraints_tuples
#assert_axioms lanesK_lookupLog
#assert_axioms lanesK_lookupCount
#assert_axioms lanesK_memOps
#assert_axioms lanesK_mapOps
#assert_axioms lanesK_memLog
#assert_axioms lanesK_mapLog
#assert_axioms lanesKWit_rows_ne
#assert_axioms lanesKWit_satisfies
#assert_axioms lanesK_forced_length
#assert_axioms lanesK_declared_rows_uniform
#assert_axioms lanesRows_symbols
#assert_axioms lanesKWit_exposes_components
#assert_axioms lanesKWit_length
#assert_axioms lanesK_forced_length_fires
#assert_axioms lanesK_forced_length_fires_lane0
#assert_axioms lanesRunIK_eq_1
#assert_axioms lanesRunIK_eq_2
#assert_axioms lanesRunIK_eq_3
#assert_axioms lanesRunIK_eq_4
#assert_axioms lanesRunI1_satisfies
#assert_axioms lanesRunI2_satisfies'
#assert_axioms lanesRunI3_satisfies
#assert_axioms lanesRunI4_satisfies
#assert_axioms lanesKWit_probe_length
#assert_axioms lanesKWit_wrong_lane_refuted
#assert_axioms lanesKWit_wrong_word_refuted

end Dregg2.Circuit.Emit.TinyAutomataLanesK
