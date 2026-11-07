/-

⚑ THE DEPLOYED CEILING — READ THIS ALONGSIDE THE COST LAW BELOW. Established by reading
`circuit/src/descriptor_ir2.rs`, not by measurement:

  const MAX_EXACT_PUBLIC_ROWS  : usize = 128     (:378)
  const MAX_EXACT_PUBLIC_CELLS : usize = 4_096   (:380)
  enforced at :1487 as `rows.len() > MAX_EXACT_PUBLIC_ROWS || rows.len()*arity > MAX_EXACT_PUBLIC_CELLS`

The check is **PER TABLE** — there is no aggregate cap across tables and no instance-count cap. The
run table has arity 3 (current, symbol, next), so the CELL bound would allow 1365 rows and the ROW
bound binds first. Therefore:

  * product-first : ONE run table of |w| rows      ⇒ **|w| ≤ 128, for any k**
  * parallel lanes: k run tables of |w| rows EACH  ⇒ **|w| ≤ 128, also independent of k**

⇒ THE CEILING IS ON WORD LENGTH, NOT ON k. (An earlier reading of mine divided the 128 by k and
concluded "32 symbols at k=4" — WRONG, because the cap is per-table; corrected here before it
travelled.) The composition law below is unaffected — both routes cap identically — but the honest
statement of what SHIPS is: **the deployed run-table carrier cannot prove a word longer than 128
symbols at all.**

⚑ AND THAT IS WHY PER-ROW PACKING IS A CAPABILITY UNLOCK, NOT MERELY A SPEEDUP. With s automaton
steps per row an n-symbol word occupies ⌈n/s⌉ rows, so the ceiling becomes n ≤ 128·s:
    s = 1 → 128    s = 2 → 256    s = 4 → 512    s = 8 → 1024    s = 16 → 2048
i.e. s = 8 is exactly what would bring the n = 1024 point into reach for the shipping shape. Note
that the widely-quoted n = 1024 timing was measured on the SHARED-TABLE shape (2 instances, a
`sem:"range"` table), which is NOT the deployed carrier and is not subject to this cap — see the
retraction at the top of `circuit/tests/tiny_automata_prove_time_attack.rs`.

⚠ SCOPE OF THE COST LAW BELOW (an adversarial verify checked this; read before quoting §7).

WITNESSED (a satisfying `Satisfied2Public` trace exists, so the cost is the cost of a PROVABLE object):
  * product-first at k = 1, 2, 3, 4 — `prodRunWit_satisfies`, general in k.
  * lanes at k = 1 (identical object to product) and k = 2 — `lanesRunI2_satisfies`.
MEASURED BUT **NOT** WITNESSED: lanes at k = 3 and k = 4. `lanes2Wit_satisfies` is hard-coded to TWO
lanes by construction; the k-lane generalisation is obvious but WAS NOT BUILT. Those two points are
cost-of-an-emitted-object, not cost-of-a-provable-object — the exact distinction whose absence got the
previous file's headline retracted. Quote them as such.

The crossover claim survives that scope: BOTH ENDPOINTS of the k=1 tie and the k=2 strict win are
witnessed on both routes, which is what the previous retraction demanded. The k=3,4 lanes numbers
strengthen an already-witnessed direction; they do not carry it.

ALSO NOT WITNESSED (and openly so): the reachability-minimised WHOLE-GRAPH product costs (area
12/36/72/150). The Eulerian obstruction stands there — no satisfying trace is known for any k. They are
quoted only as the price of the attestation the run-table discipline does not buy, never as a crossover.
# Dregg2.Circuit.Emit.TinyAutomataSatisfiable — the REPAIR of the composition experiment:
a genuinely-independent tiny-automaton family, the RUN-table discipline, and — the deliverable —
a REAL `Satisfied2Public` WITNESS for a COMPOSED descriptor.

**This is Lean-authored AIR.** The composed descriptors are `EffectVmDescriptor2` values authored
here (via `DfaRoutingTableEmit.tableRoutingDesc`); the witness is a concrete `VmTrace`; the
satisfaction is a theorem over the EMITTED object. Rust parses the emitted IR2 bytes and supplies
witnesses; it authors nothing.

## What this file repairs

`TinyAutomataCompose.lean` measured a cost law over descriptors NO PROVER CAN SATISFY. Its own
retraction header names the three defects; this file fixes each:

  * **(a) A DEGENERATE FAMILY.** `fam k` alternated only TWO machines, so the `k`-fold product's
    REACHABLE state space was 4 for every `k` while `tableOf` tabulated `2^k` (504/512 dead rows at
    `k = 8`). Here the family is FOUR pairwise non-isomorphic machines — count-mod-2, count-mod-3,
    ends-in-1, contains-the-factor-01 — and §2's reachability census MEASURES the product's
    reachable space growing 2 → 6 → 12 → 25 over `k = 1…4`.
  * **(b) THE EULERIAN OBSTRUCTION.** A whole-graph `exactPublicRows` table forces the run to be an
    EULERIAN path through the declared multigraph (`TinyAutomataCompose`'s
    `tableRouting_traverses_each_declared_row_once` + `forced_trace_length`), and the previous
    family's components had DISJOINT Eulerian word sets. This file uses the RUN-TABLE discipline:
    the descriptor declares exactly the `|w|` edges the run traverses, in order, so the
    exact-multiset permutation obligation is discharged BY CONSTRUCTION — `runWit_lookupLog` is an
    EQUALITY, hence `List.Perm.refl`.
  * **(c) NO WITNESS EXISTED.** §4's `runWit_satisfies` is a GENERAL construction — for ANY
    `TableDfa`, start state and non-empty word — of a `VmTrace` that PROVABLY satisfies the emitted
    `tableRoutingDesc name (runTable d q w)`. §5 fires it on the COMPOSED product descriptors at
    `k = 1, 2, 3, 4` and pushes it through `TinyAutomataCompose.productDesc_refines_components`, so
    the witness's exposed public `final_state` PROVABLY decodes to every component automaton's own
    classification of the word the trace reads.

§6 adds the second satisfiable route (a 2-lane witness), so the `k = 2` comparison is between two
families that BOTH have witnesses. §7 states the measured law.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. NEW file; imports
read-only (nothing in `TinyAutomataCompose` or `DfaRoutingTableEmit` is edited). Every `#guard` is
COMPILED EVALUATION of a closed `Bool` — it proves NO `Prop`; it pins measured numbers and nothing
more. The load-bearing objects are the theorems.
-/
import Dregg2.Circuit.Emit.TinyAutomataCompose

namespace Dregg2.Circuit.Emit.TinyAutomataSatisfiable

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
  (VmConstraint VmRow VmRowEnv holdsVm_piFirst_true holdsVm_piLast_true)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Crypto.DfaAcceptanceAir (TableDfa classifyFrom)
open Dregg2.Circuit.Emit.DfaRoutingTableEmit
  (CURRENT SYMBOL NEXT TRT_TID TRT_WIDTH TRT_PI_COUNT PI_INITIAL PI_FINAL
   tableRoutingDesc transitionTableDef contWindowBody tableRoutingDesc_constraints
   tableRoutingDesc_tables tableRoutingDesc_ranges
   hash0 envAt_loc envAt_nxt tableRouting_refines_classify)
open Dregg2.Circuit.Emit.TinyAutomataCompose

set_option autoImplicit false

/-! ## §1 — FOUR GENUINELY INDEPENDENT tiny automata (defect (a), fixed).

The previous family alternated two machines, so the product collapsed. These four are pairwise
non-isomorphic — two of them have three states, and no two agree on all of {state count, whether
the state resets on every symbol, whether there is an absorbing state}. Every step function is
TOTAL on `ℕ` and lands strictly below `IRADIX = 4`, which is the uniform digit width the mixed-radix
product encoding (`TinyAutomataCompose.prodListDfa`) needs. -/

/-- The uniform mixed-radix digit width: every machine below has at most 4 states. -/
def IRADIX : Nat := 4

/-- M1 — "an EVEN number of 1s" (the count mod 2). Two states, no absorbing state. -/
def modTwoDfa : TableDfa Nat Nat :=
  { step := fun s y => (s + y) % 2, start := 0, accepts := fun s => s = 0 }

/-- M2 — "the number of 1s is divisible by 3" (the count mod 3). THREE states, cyclic. -/
def modThreeDfa : TableDfa Nat Nat :=
  { step := fun s y => (s + y) % 3, start := 0, accepts := fun s => s = 0 }

/-- M3 — "ENDS IN 1". Two states, and the state RESETS on every symbol (memoryless). -/
def endsOneDfa : TableDfa Nat Nat :=
  { step := fun _ y => y % 2, start := 0, accepts := fun s => s = 1 }

/-- M4 — "CONTAINS the factor `01`". Three states with an ABSORBING accept state:
`0` = no pending `0`, `1` = the last symbol was `0`, `2` = an `01` has been seen (sink). -/
def containsZeroOneDfa : TableDfa Nat Nat :=
  { step := fun s y => if s = 2 then 2 else if y % 2 = 0 then 1 else if s = 1 then 2 else 0
  , start := 0, accepts := fun s => s = 2 }

/-- The independent bank, in the order the `k`-fold product consumes it. -/
def indep : List (TableDfa Nat Nat) := [modTwoDfa, modThreeDfa, endsOneDfa, containsZeroOneDfa]

/-- The `k`-machine family: the FIRST `k` of the independent bank (`k ≤ 4`). -/
def famI (k : Nat) : List (TableDfa Nat Nat) := indep.take k

/-- The `k`-fold product automaton over the independent family, radix `IRADIX`. -/
def prodI (k : Nat) : TableDfa Nat Nat := prodListDfa IRADIX (famI k)

/-- Every machine in the bank steps strictly inside the radix — the `hstep` hypothesis of
`TinyAutomataCompose.classify_prodList` / `productDesc_refines_components`, discharged. -/
theorem indep_step_lt : ∀ d ∈ indep, ∀ s y, d.step s y < IRADIX := by
  intro d hd s y
  simp only [indep, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl
  · exact Nat.lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num [IRADIX])
  · exact Nat.lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num [IRADIX])
  · exact Nat.lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num [IRADIX])
  · show (if s = 2 then 2 else if y % 2 = 0 then 1 else if s = 1 then 2 else 0) < IRADIX
    split
    · norm_num [IRADIX]
    · split
      · norm_num [IRADIX]
      · split <;> norm_num [IRADIX]

/-- The same bound for the `k`-machine prefix. -/
theorem famI_step_lt (k : Nat) : ∀ d ∈ famI k, ∀ s y, d.step s y < IRADIX :=
  fun d hd => indep_step_lt d (List.mem_of_mem_take hd)

/-! ## §2 — THE REACHABILITY CENSUS: the product state space GENUINELY grows.

The previous family's product had 4 reachable states at EVERY `k`; the "exponential" it measured
was 504/512 dead rows. Here the reachable set is COMPUTED (a saturating BFS over the two symbols)
and it grows. ⚠ Every `#guard` in this file is COMPILED EVALUATION of a closed `Bool` — it proves
NO `Prop`. -/

/-- One BFS layer: the frontier plus every 0/1 successor, de-duplicated. -/
def reachStep (d : TableDfa Nat Nat) (qs : List Nat) : List Nat :=
  (qs ++ qs.flatMap (fun q => [d.step q 0, d.step q 1])).eraseDups

/-- Saturate the BFS for `fuel` layers. -/
def reachN (d : TableDfa Nat Nat) : Nat → List Nat → List Nat
  | 0,     qs => qs
  | n + 1, qs => reachN d n (reachStep d qs)

/-- The reachable state set from `d.start` (saturated at `fuel` layers). -/
def reachable (d : TableDfa Nat Nat) (fuel : Nat) : List Nat := reachN d fuel [d.start]

/-- The REACHABILITY-MINIMISED whole-graph transition table: only the states the automaton can
actually be in, `|Σ| = 2` rows each. This is the honest whole-graph declaration; `tableOf` over the
full `r^k` grid is the one that tabulated dead states. -/
def reachTable (d : TableDfa Nat Nat) (fuel : Nat) : List (List Nat) :=
  (reachable d fuel).flatMap (fun s => (List.range NSYM).map (fun y => [s, y, d.step s y]))

-- ⚑ THE PRODUCT STATE SPACE GENUINELY GROWS (compiled evaluation, NO `Prop`): reachable states at
-- k = 1, 2, 3, 4 are 2, 6, 12, 25 — against the DECLARED `IRADIX^k` grid of 4, 16, 64, 256. The
-- previous family was FLAT at 4 reachable states for every k; this one is not.
#guard (List.map (fun k => (reachable (prodI k) 24).length) [1, 2, 3, 4]) == [2, 6, 12, 25]
#guard (List.map (fun k => IRADIX ^ k) [1, 2, 3, 4]) == [4, 16, 64, 256]

-- The reachability-minimised WHOLE-GRAPH tables, and the trace length each would PIN
-- (`TinyAutomataCompose.forced_trace_length`): 4, 12, 24, 50 rows — genuinely growing in `k`, with
-- every row REACHABLE. ⚠ These are the honest whole-graph COSTS; no witness is exhibited for a
-- whole-graph table (the Eulerian obstruction is unresolved for them), so they are NOT quoted in
-- §7's law.
#guard (List.map (fun k => (reachTable (prodI k) 24).length) [1, 2, 3, 4]) == [4, 12, 24, 50]

/-! ## §3 — THE RUN-TABLE WITNESS CONSTRUCTION (defects (b) and (c), fixed).

`TinyAutomataCompose.runTable d q w` declares exactly the `|w|` edges the run traverses, in order,
with multiplicity. The trace below reads exactly those edges in exactly that order, so the
unit-capacity LogUp receive's permutation obligation is an EQUALITY — the Eulerian obstruction is
discharged by construction rather than searched for. -/

/-- One 3-column trace row: `(current, symbol, next) = (s, y, n)`. -/
def asg3 (s y n : Nat) : Assignment :=
  fun c => if c = 0 then Int.ofNat s else if c = 1 then Int.ofNat y
           else if c = 2 then Int.ofNat n else 0

@[simp] theorem asg3_current (s y n : Nat) : asg3 s y n CURRENT = Int.ofNat s := rfl
@[simp] theorem asg3_symbol (s y n : Nat) : asg3 s y n SYMBOL = Int.ofNat y := rfl
@[simp] theorem asg3_next (s y n : Nat) : asg3 s y n NEXT = Int.ofNat n := rfl

/-- **The run's trace rows**: one row per input symbol, carrying the state before, the symbol read,
and the state after. Chained by construction. -/
def runRows (d : TableDfa Nat Nat) (q : Nat) : List Nat → List Assignment
  | []      => []
  | y :: ys => asg3 q y (d.step q y) :: runRows d (d.step q y) ys

theorem runRows_length (d : TableDfa Nat Nat) :
    ∀ (w : List Nat) (q : Nat), (runRows d q w).length = w.length
  | [],      _ => rfl
  | y :: ys, q => by
    show (runRows d (d.step q y) ys).length + 1 = ys.length + 1
    rw [runRows_length d ys (d.step q y)]

/-- **The trace's `(current, symbol, next)` column triples ARE the declared run table** — an
EQUALITY, not merely a permutation. This is what discharges the Eulerian obstruction. -/
theorem runRows_triples (d : TableDfa Nat Nat) :
    ∀ (w : List Nat) (q : Nat),
      (runRows d q w).map (fun a => [a CURRENT, a SYMBOL, a NEXT])
        = exactPublicTable (runTable d q w)
  | [],      _ => rfl
  | y :: ys, q => by
    show (fun a : Assignment => [a CURRENT, a SYMBOL, a NEXT]) (asg3 q y (d.step q y))
        :: (runRows d (d.step q y) ys).map (fun a => [a CURRENT, a SYMBOL, a NEXT]) = _
    rw [runRows_triples d ys (d.step q y)]
    rfl

/-- Adjacent rows CHAIN: row `i+1`'s `current` is row `i`'s `next`. (The continuity window's whole
content, discharged by construction.) -/
theorem runRows_chain (d : TableDfa Nat Nat) :
    ∀ (w : List Nat) (q i : Nat) (h : i + 1 < (runRows d q w).length),
      ((runRows d q w)[i + 1]'h) CURRENT
        = ((runRows d q w)[i]'(Nat.lt_of_succ_lt h)) NEXT := by
  intro w
  induction w with
  | nil => intro q i h; simp [runRows] at h
  | cons y ys ih =>
    intro q i h
    cases i with
    | zero =>
      cases ys with
      | nil => simp [runRows] at h
      | cons y' ys' => rfl
    | succ j => exact ih (d.step q y) j (by simpa [runRows] using h)

/-- The FIRST row's `current` is the start state. -/
theorem runRows_head_current (d : TableDfa Nat Nat) (q : Nat) (w : List Nat) (hw : w ≠ [])
    (h : 0 < (runRows d q w).length) : ((runRows d q w)[0]'h) CURRENT = Int.ofNat q := by
  cases w with
  | nil => exact absurd rfl hw
  | cons y ys => rfl

/-- The LAST row's `next` IS the classification of the whole word. -/
theorem runRows_last_next (d : TableDfa Nat Nat) :
    ∀ (w : List Nat) (q i : Nat) (h : i < (runRows d q w).length),
      i + 1 = (runRows d q w).length →
      ((runRows d q w)[i]'h) NEXT = Int.ofNat (classifyFrom d q w) := by
  intro w
  induction w with
  | nil => intro q i h _; simp [runRows] at h
  | cons y ys ih =>
    intro q i h hlast
    cases i with
    | zero =>
      have hys : ys = [] := by
        have h0 : (runRows d (d.step q y) ys).length = 0 := by
          simp only [runRows, List.length_cons] at hlast
          omega
        rw [runRows_length d ys (d.step q y)] at h0
        exact List.eq_nil_of_length_eq_zero h0
      subst hys
      rfl
    | succ j =>
      exact ih (d.step q y) j (by simpa [runRows] using h) (by simpa [runRows] using hlast)

/-- The witness's public inputs: `pi[initial_state] = q`, `pi[final_state] = f`. -/
def runPub (q f : Nat) : Assignment :=
  fun k => if k = 1 then Int.ofNat f else Int.ofNat q

/-- The witness's table family: the declared run table at `TRT_TID`, empty elsewhere. -/
def runTf (tbl : List (List Nat)) : TraceFamily :=
  fun id => if id = TRT_TID then exactPublicTable tbl else []

/-- **THE WITNESS**: the trace that runs `d` from `q` on `w` against the declared run table. -/
def runWit (d : TableDfa Nat Nat) (q : Nat) (w : List Nat) : VmTrace :=
  { rows := runRows d q w
  , pub  := runPub q (classifyFrom d q w)
  , tf   := runTf (runTable d q w) }

theorem runWit_rows_ne (d : TableDfa Nat Nat) (q : Nat) {w : List Nat} (hw : w ≠ []) :
    (runWit d q w).rows ≠ [] := by
  intro h
  apply hw
  have h0 : (runRows d q w).length = 0 := by
    rw [show runRows d q w = [] from h]
    rfl
  rw [runRows_length d w q] at h0
  exact List.eq_nil_of_length_eq_zero h0

/-- The lookup log of the witness IS the declared table — an equality, so `PublicLookupBalanced`
is `List.Perm.refl`. -/
theorem runWit_lookupLog (d : TableDfa Nat Nat) (q : Nat) (w : List Nat) (name : String) :
    lookupLog (tableRoutingDesc name (runTable d q w)) (runWit d q w) TRT_TID
      = exactPublicTable (runTable d q w) := by
  rw [tableRouting_lookupLog]
  exact runRows_triples d w q

/-- The table-routing family declares no memory ops. -/
theorem trt_memOps (name : String) (tbl : List (List Nat)) :
    memOpsOf (tableRoutingDesc name tbl) = [] := rfl

/-- …and no map ops. -/
theorem trt_mapOps (name : String) (tbl : List (List Nat)) :
    mapOpsOf (tableRoutingDesc name tbl) = [] := rfl

theorem trt_memLog (name : String) (tbl : List (List Nat)) (t : VmTrace) :
    memLog (tableRoutingDesc name tbl) t = [] := by
  simp [memLog, trt_memOps]

theorem trt_mapLog (name : String) (tbl : List (List Nat)) (t : VmTrace) :
    mapLog (tableRoutingDesc name tbl) t = [] := by
  simp [mapLog, trt_mapOps]

/-! ## §4 — ⚑ THE GATE: the witness PROVABLY satisfies the emitted descriptor.

GENERAL over the automaton, the start state, the (non-empty) word and the descriptor name. Every
leg is discharged by construction: the transition lookup by `runRows_triples`, the continuity
window by `runRows_chain`, the two boundary pins by the head/last rows, and the exact-multiset
LogUp balance by `runWit_lookupLog` — an EQUALITY, which is the repair of the Eulerian defect. -/

theorem runWit_satisfies (d : TableDfa Nat Nat) (q : Nat) (w : List Nat) (hw : w ≠ [])
    (name : String) :
    Satisfied2Public hash0 (tableRoutingDesc name (runTable d q w))
      (fun _ => 0) (fun _ => (0, 0)) [] (runWit d q w) where
  rowConstraints := by
    intro i hi c hc
    have hi' : i < (runRows d q w).length := hi
    have hloc : (envAt (runWit d q w) i).loc = (runRows d q w)[i]'hi' :=
      envAt_loc (t := runWit d q w) hi
    simp only [tableRoutingDesc_constraints, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · -- the transition lookup: the row's triple is a DECLARED row, by construction
      show [(envAt (runWit d q w) i).loc CURRENT, (envAt (runWit d q w) i).loc SYMBOL,
            (envAt (runWit d q w) i).loc NEXT] ∈ runTf (runTable d q w) TRT_TID
      rw [hloc, show runTf (runTable d q w) TRT_TID = exactPublicTable (runTable d q w) from rfl,
        ← runRows_triples d w q]
      exact List.mem_map.mpr ⟨(runRows d q w)[i]'hi', List.getElem_mem hi', rfl⟩
    · -- the continuity window: adjacent rows chain
      show WindowConstraint.holdsAt (envAt (runWit d q w) i)
        (i + 1 == (runWit d q w).rows.length) ⟨contWindowBody, true⟩
      simp only [WindowConstraint.holdsAt, if_true]
      intro hnl
      have hlt : i + 1 < (runRows d q w).length := by
        have hne' : ¬ (i + 1 = (runRows d q w).length) := by
          intro hEq
          rw [show (runWit d q w).rows = runRows d q w from rfl, hEq] at hnl
          simp at hnl
        omega
      have hnxt : (envAt (runWit d q w) i).nxt = (runRows d q w)[i + 1]'hlt :=
        envAt_nxt (t := runWit d q w) hlt
      have hch : ((runRows d q w)[i + 1]'hlt) CURRENT = ((runRows d q w)[i]'hi') NEXT :=
        runRows_chain d w q i hlt
      show (WindowExpr.add (.nxt CURRENT) (.mul (.const (-1)) (.loc NEXT))).eval
        (envAt (runWit d q w) i) ≡ 0 [ZMOD 2013265921]
      simp only [WindowExpr.eval]
      rw [hloc, hnxt, hch]
      have hz : ((runRows d q w)[i]'hi') NEXT + (-1) * ((runRows d q w)[i]'hi') NEXT = 0 := by
        ring
      rw [hz]
    · -- B1: the FIRST row's `current` IS `pi[initial_state]`
      show (i == 0) = true → (envAt (runWit d q w) i).loc CURRENT
        ≡ (envAt (runWit d q w) i).pub PI_INITIAL [ZMOD 2013265921]
      intro hf
      have hi0 : i = 0 := by simpa using hf
      subst hi0
      rw [hloc, runRows_head_current d q w hw hi']
      exact Int.ModEq.refl _
    · -- B2: the LAST row's `next` IS `pi[final_state]` — the classification
      show (i + 1 == (runWit d q w).rows.length) = true → (envAt (runWit d q w) i).loc NEXT
        ≡ (envAt (runWit d q w) i).pub PI_FINAL [ZMOD 2013265921]
      intro hl
      have hlast : i + 1 = (runRows d q w).length :=
        (by simpa using hl : i + 1 = (runWit d q w).rows.length)
      rw [hloc, runRows_last_next d w q i hi' hlast]
      exact Int.ModEq.refl _
  rowHashes := by intro i _; trivial
  rowRanges := by
    intro i _ r hr
    simp only [tableRoutingDesc_ranges, List.not_mem_nil] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by rw [trt_memLog]; simp
  memDisciplined := by rw [trt_memLog]; trivial
  memBalanced := by rw [trt_memLog]; exact memCheck_nil _ _
  memTableFaithful := by rw [trt_memLog]; rfl
  mapTableFaithful := by rw [trt_mapLog]; rfl
  publicTablesFaithful := by
    intro td htd
    simp only [tableRoutingDesc_tables, List.mem_singleton] at htd
    subst htd
    show runTf (runTable d q w) TRT_TID = exactPublicTable (runTable d q w)
    rfl
  publicLookupBalanced := by
    intro td htd
    simp only [tableRoutingDesc_tables, List.mem_singleton] at htd
    subst htd
    show (lookupLog (tableRoutingDesc name (runTable d q w)) (runWit d q w) TRT_TID).Perm
      (exactPublicTable (runTable d q w))
    rw [runWit_lookupLog]

/-! ## §5 — ⚑ THE COMPOSED WITNESS: the gate FIRED on the `k`-fold PRODUCT descriptor.

`prodRunDesc k w` is ONE `tableRoutingDesc` over the `k`-fold product of the INDEPENDENT family,
declaring the RUN table. `prodRunWit k w` is a concrete `VmTrace`, and `prodRunWit_satisfies` is the
theorem that it satisfies that COMPOSED descriptor — the object `TinyAutomataCompose` never built.
`prodRunWit_exposes_components` then pushes the witness through the composition-soundness theorem:
the witness's exposed public `final_state` IS the mixed-radix packing of EVERY component
automaton's classification of the word the trace reads (and that word IS `w`). -/

/-- The 8-symbol probe word (`TinyAutomataCompose.probeWord`), held fixed by the measurement. -/
def probeW : List Nat := probeWord

theorem probeW_ne : probeW ≠ [] := by decide

/-- **The COMPOSED descriptor**: one product-DFA table-routing descriptor over the RUN table. -/
def prodRunDesc (k : Nat) (w : List Nat) : EffectVmDescriptor2 :=
  tableRoutingDesc s!"tiny-automata-indep-product-run-k{k}::exact-public-v1"
    (runTable (prodI k) 0 w)

/-- **The COMPOSED witness**. -/
def prodRunWit (k : Nat) (w : List Nat) : VmTrace := runWit (prodI k) 0 w

/-- ⚑ **THE GATE — a real `Satisfied2Public` witness for a COMPOSED descriptor**, at every `k`. -/
theorem prodRunWit_satisfies (k : Nat) (w : List Nat) (hw : w ≠ []) :
    Satisfied2Public hash0 (prodRunDesc k w) (fun _ => 0) (fun _ => (0, 0)) [] (prodRunWit k w) :=
  runWit_satisfies (prodI k) 0 w hw _

/-- The all-zero start tuple encodes to product state `0`. -/
theorem encodeDigits_replicate_zero (r : Nat) : ∀ k, encodeDigits r (List.replicate k 0) = 0
  | 0     => rfl
  | k + 1 => by
    show 0 * r ^ (List.replicate k 0).length + encodeDigits r (List.replicate k 0) = 0
    rw [encodeDigits_replicate_zero r k]
    simp

/-- The word the witness's symbol column reads IS `w`. -/
theorem runRows_symbols (d : TableDfa Nat Nat) :
    ∀ (w : List Nat) (q : Nat), (runRows d q w).map (fun a => (a SYMBOL).toNat) = w
  | [],      _ => rfl
  | y :: ys, q => by
    show (asg3 q y (d.step q y) SYMBOL).toNat
        :: (runRows d (d.step q y) ys).map (fun a => (a SYMBOL).toNat) = y :: ys
    rw [runRows_symbols d ys (d.step q y)]
    rfl

/-- ⚑ **THE COMPOSITION, LANDED ON A REAL WITNESS.** The satisfying witness of the COMPOSED
descriptor reads exactly the word `w` off its symbol column, and its exposed public `final_state`
is the mixed-radix packing of the `k` COMPONENT automata's classifications of `w`. Every
component's verdict is exposed by the one composed descriptor — now with a trace that exists. -/
theorem prodRunWit_exposes_components (k : Nat) (hlen : (famI k).length = k)
    (w : List Nat) (hw : w ≠ [])
    (hsmall : ∀ row ∈ runTable (prodI k) 0 w, ∀ v ∈ row, v < 2013265921)
    (fN : ℕ) (hfin : (prodRunWit k w).pub PI_FINAL = Int.ofNat fN) (hfN : fN < 2013265921) :
    (prodRunWit k w).rows.map (fun a => (a SYMBOL).toNat) = w
      ∧ fN = encodeDigits IRADIX
          (List.zipWith (fun d q => classifyFrom d q w) (famI k) (List.replicate k 0)) := by
  have hword : (prodRunWit k w).rows.map (fun a => (a SYMBOL).toNat) = w :=
    runRows_symbols (prodI k) w 0
  refine ⟨hword, ?_⟩
  have h := productDesc_refines_components (hash := hash0) (t := prodRunWit k w)
    IRADIX (by norm_num [IRADIX]) (famI k) (List.replicate k 0)
    (by rw [hlen, List.length_replicate])
    (famI_step_lt k)
    (fun x hx => by rw [List.eq_of_mem_replicate hx]; norm_num [IRADIX])
    (runTable_graph (prodI k) w 0)
    hsmall
    (prodRunWit_satisfies k w hw)
    (runWit_rows_ne (prodI k) 0 hw)
    (by rw [encodeDigits_replicate_zero]; rfl)
    (by rw [encodeDigits_replicate_zero]; norm_num)
    fN hfin hfN
  rw [hword] at h
  exact h.2

/-! ### §5a — the gate FIRED at `k = 2, 3, 4` on the concrete probe word.

Each of these is the composed descriptor's satisfying witness, pushed through the composition
soundness theorem: the trace reads exactly `probeW`, and its exposed public `final_state` is the
mixed-radix packing of the component verdicts. -/

/-- `k = 2` — the product of "even number of 1s" × "count of 1s divisible by 3". -/
theorem prodRunWit_k2_components :
    (prodRunWit 2 probeW).rows.map (fun a => (a SYMBOL).toNat) = probeW
      ∧ classifyFrom (prodI 2) 0 probeW
        = encodeDigits IRADIX (List.zipWith (fun d q => classifyFrom d q probeW)
            (famI 2) (List.replicate 2 0)) :=
  prodRunWit_exposes_components 2 rfl probeW probeW_ne (by decide)
    (classifyFrom (prodI 2) 0 probeW) rfl (by decide)

/-- `k = 3` — the above × "ends in 1". -/
theorem prodRunWit_k3_components :
    (prodRunWit 3 probeW).rows.map (fun a => (a SYMBOL).toNat) = probeW
      ∧ classifyFrom (prodI 3) 0 probeW
        = encodeDigits IRADIX (List.zipWith (fun d q => classifyFrom d q probeW)
            (famI 3) (List.replicate 3 0)) :=
  prodRunWit_exposes_components 3 rfl probeW probeW_ne (by decide)
    (classifyFrom (prodI 3) 0 probeW) rfl (by decide)

/-- `k = 4` — the above × "contains the factor 01". FOUR independent verdicts exposed by ONE
3-column, 4-constraint, 2-PI descriptor with a satisfying trace. -/
theorem prodRunWit_k4_components :
    (prodRunWit 4 probeW).rows.map (fun a => (a SYMBOL).toNat) = probeW
      ∧ classifyFrom (prodI 4) 0 probeW
        = encodeDigits IRADIX (List.zipWith (fun d q => classifyFrom d q probeW)
            (famI 4) (List.replicate 4 0)) :=
  prodRunWit_exposes_components 4 rfl probeW probeW_ne (by decide)
    (classifyFrom (prodI 4) 0 probeW) rfl (by decide)

-- The DECODED verdicts (compiled evaluation — NO `Prop`; the `Prop` is the three theorems above).
-- The product state at k = 4 is 102 = 1·64 + 2·16 + 1·4 + 2, i.e. digits [1, 2, 1, 2]:
-- five 1s (odd ⇒ mod-2 state 1), 5 mod 3 = 2, ends in 1, and `01` occurs ⇒ the sink state 2.
#guard (List.map (fun k => classifyFrom (prodI k) 0 probeW) [1, 2, 3, 4]) == [1, 6, 25, 102]
#guard (List.map (fun k => List.zipWith (fun d q => classifyFrom d q probeW) (famI k)
  (List.replicate k 0)) [1, 2, 3, 4]) == [[1], [1, 2], [1, 2, 1], [1, 2, 1, 2]]

/-! ## §6 — THE SECOND SATISFIABLE ROUTE: a 2-LANE witness.

`TinyAutomataCompose`'s lanes route was the one its retraction proved VACUOUS at `k ≥ 2` (each
lane's whole-graph table forced its own Eulerian path, and the components' Eulerian word sets were
disjoint). Under the RUN-table discipline the obstruction disappears for lanes too: each lane
declares exactly its own run over the SHARED word, so each lane's lookup log is that lane's run
table by construction. This section builds the witness, so the `k = 2` cost comparison of §7 is
between two families that BOTH have one. -/

/-- One 5-column lanes row: shared symbol, then `(current, next)` per lane. -/
def lane2Row (y s0 n0 s1 n1 : Nat) : Assignment :=
  fun c => if c = 0 then Int.ofNat y
    else if c = 1 then Int.ofNat s0 else if c = 2 then Int.ofNat n0
    else if c = 3 then Int.ofNat s1 else if c = 4 then Int.ofNat n1 else 0

/-- The 2-lane trace rows: both machines step on the SAME symbol column. -/
def lanes2Rows (d0 d1 : TableDfa Nat Nat) (q0 q1 : Nat) : List Nat → List Assignment
  | []      => []
  | y :: ys => lane2Row y q0 (d0.step q0 y) q1 (d1.step q1 y)
               :: lanes2Rows d0 d1 (d0.step q0 y) (d1.step q1 y) ys

theorem lanes2Rows_length (d0 d1 : TableDfa Nat Nat) :
    ∀ (w : List Nat) (q0 q1 : Nat), (lanes2Rows d0 d1 q0 q1 w).length = w.length
  | [],      _,  _  => rfl
  | y :: ys, q0, q1 => by
    show (lanes2Rows d0 d1 (d0.step q0 y) (d1.step q1 y) ys).length + 1 = ys.length + 1
    rw [lanes2Rows_length d0 d1 ys (d0.step q0 y) (d1.step q1 y)]

theorem lanes2Rows_triples0 (d0 d1 : TableDfa Nat Nat) :
    ∀ (w : List Nat) (q0 q1 : Nat),
      (lanes2Rows d0 d1 q0 q1 w).map
          (fun a => [a (laneCurrent 0), a LANE_SYMBOL, a (laneNext 0)])
        = exactPublicTable (runTable d0 q0 w)
  | [],      _,  _  => rfl
  | y :: ys, q0, q1 => by
    show (fun a : Assignment => [a (laneCurrent 0), a LANE_SYMBOL, a (laneNext 0)])
        (lane2Row y q0 (d0.step q0 y) q1 (d1.step q1 y))
        :: (lanes2Rows d0 d1 (d0.step q0 y) (d1.step q1 y) ys).map
             (fun a => [a (laneCurrent 0), a LANE_SYMBOL, a (laneNext 0)]) = _
    rw [lanes2Rows_triples0 d0 d1 ys (d0.step q0 y) (d1.step q1 y)]
    rfl

theorem lanes2Rows_triples1 (d0 d1 : TableDfa Nat Nat) :
    ∀ (w : List Nat) (q0 q1 : Nat),
      (lanes2Rows d0 d1 q0 q1 w).map
          (fun a => [a (laneCurrent 1), a LANE_SYMBOL, a (laneNext 1)])
        = exactPublicTable (runTable d1 q1 w)
  | [],      _,  _  => rfl
  | y :: ys, q0, q1 => by
    show (fun a : Assignment => [a (laneCurrent 1), a LANE_SYMBOL, a (laneNext 1)])
        (lane2Row y q0 (d0.step q0 y) q1 (d1.step q1 y))
        :: (lanes2Rows d0 d1 (d0.step q0 y) (d1.step q1 y) ys).map
             (fun a => [a (laneCurrent 1), a LANE_SYMBOL, a (laneNext 1)]) = _
    rw [lanes2Rows_triples1 d0 d1 ys (d0.step q0 y) (d1.step q1 y)]
    rfl

theorem lanes2Rows_chain0 (d0 d1 : TableDfa Nat Nat) :
    ∀ (w : List Nat) (q0 q1 i : Nat) (h : i + 1 < (lanes2Rows d0 d1 q0 q1 w).length),
      ((lanes2Rows d0 d1 q0 q1 w)[i + 1]'h) (laneCurrent 0)
        = ((lanes2Rows d0 d1 q0 q1 w)[i]'(Nat.lt_of_succ_lt h)) (laneNext 0) := by
  intro w
  induction w with
  | nil => intro q0 q1 i h; simp [lanes2Rows] at h
  | cons y ys ih =>
    intro q0 q1 i h
    cases i with
    | zero =>
      cases ys with
      | nil => simp [lanes2Rows] at h
      | cons y' ys' => rfl
    | succ j =>
      exact ih (d0.step q0 y) (d1.step q1 y) j (by simpa [lanes2Rows] using h)

theorem lanes2Rows_chain1 (d0 d1 : TableDfa Nat Nat) :
    ∀ (w : List Nat) (q0 q1 i : Nat) (h : i + 1 < (lanes2Rows d0 d1 q0 q1 w).length),
      ((lanes2Rows d0 d1 q0 q1 w)[i + 1]'h) (laneCurrent 1)
        = ((lanes2Rows d0 d1 q0 q1 w)[i]'(Nat.lt_of_succ_lt h)) (laneNext 1) := by
  intro w
  induction w with
  | nil => intro q0 q1 i h; simp [lanes2Rows] at h
  | cons y ys ih =>
    intro q0 q1 i h
    cases i with
    | zero =>
      cases ys with
      | nil => simp [lanes2Rows] at h
      | cons y' ys' => rfl
    | succ j =>
      exact ih (d0.step q0 y) (d1.step q1 y) j (by simpa [lanes2Rows] using h)

theorem lanes2Rows_head0 (d0 d1 : TableDfa Nat Nat) (q0 q1 : Nat) (w : List Nat) (hw : w ≠ [])
    (h : 0 < (lanes2Rows d0 d1 q0 q1 w).length) :
    ((lanes2Rows d0 d1 q0 q1 w)[0]'h) (laneCurrent 0) = Int.ofNat q0 := by
  cases w with
  | nil => exact absurd rfl hw
  | cons y ys => rfl

theorem lanes2Rows_head1 (d0 d1 : TableDfa Nat Nat) (q0 q1 : Nat) (w : List Nat) (hw : w ≠ [])
    (h : 0 < (lanes2Rows d0 d1 q0 q1 w).length) :
    ((lanes2Rows d0 d1 q0 q1 w)[0]'h) (laneCurrent 1) = Int.ofNat q1 := by
  cases w with
  | nil => exact absurd rfl hw
  | cons y ys => rfl

theorem lanes2Rows_last0 (d0 d1 : TableDfa Nat Nat) :
    ∀ (w : List Nat) (q0 q1 i : Nat) (h : i < (lanes2Rows d0 d1 q0 q1 w).length),
      i + 1 = (lanes2Rows d0 d1 q0 q1 w).length →
      ((lanes2Rows d0 d1 q0 q1 w)[i]'h) (laneNext 0) = Int.ofNat (classifyFrom d0 q0 w) := by
  intro w
  induction w with
  | nil => intro q0 q1 i h _; simp [lanes2Rows] at h
  | cons y ys ih =>
    intro q0 q1 i h hlast
    cases i with
    | zero =>
      have hys : ys = [] := by
        have h0 : (lanes2Rows d0 d1 (d0.step q0 y) (d1.step q1 y) ys).length = 0 := by
          simp only [lanes2Rows, List.length_cons] at hlast
          omega
        rw [lanes2Rows_length d0 d1 ys (d0.step q0 y) (d1.step q1 y)] at h0
        exact List.eq_nil_of_length_eq_zero h0
      subst hys
      rfl
    | succ j =>
      exact ih (d0.step q0 y) (d1.step q1 y) j (by simpa [lanes2Rows] using h)
        (by simpa [lanes2Rows] using hlast)

theorem lanes2Rows_last1 (d0 d1 : TableDfa Nat Nat) :
    ∀ (w : List Nat) (q0 q1 i : Nat) (h : i < (lanes2Rows d0 d1 q0 q1 w).length),
      i + 1 = (lanes2Rows d0 d1 q0 q1 w).length →
      ((lanes2Rows d0 d1 q0 q1 w)[i]'h) (laneNext 1) = Int.ofNat (classifyFrom d1 q1 w) := by
  intro w
  induction w with
  | nil => intro q0 q1 i h _; simp [lanes2Rows] at h
  | cons y ys ih =>
    intro q0 q1 i h hlast
    cases i with
    | zero =>
      have hys : ys = [] := by
        have h0 : (lanes2Rows d0 d1 (d0.step q0 y) (d1.step q1 y) ys).length = 0 := by
          simp only [lanes2Rows, List.length_cons] at hlast
          omega
        rw [lanes2Rows_length d0 d1 ys (d0.step q0 y) (d1.step q1 y)] at h0
        exact List.eq_nil_of_length_eq_zero h0
      subst hys
      rfl
    | succ j =>
      exact ih (d0.step q0 y) (d1.step q1 y) j (by simpa [lanes2Rows] using h)
        (by simpa [lanes2Rows] using hlast)

/-- The 2-lane public inputs: `(initial₀, final₀, initial₁, final₁)`. -/
def lanes2Pub (q0 f0 q1 f1 : Nat) : Assignment :=
  fun k => if k = 0 then Int.ofNat q0 else if k = 1 then Int.ofNat f0
    else if k = 2 then Int.ofNat q1 else Int.ofNat f1

/-- The 2-lane table family: each lane's declared run table at its own id. -/
def lanes2Tf (t0 t1 : List (List Nat)) : TraceFamily :=
  fun id => if id = LANE_TID 0 then exactPublicTable t0
    else if id = LANE_TID 1 then exactPublicTable t1 else []

/-- **The 2-LANE WITNESS.** -/
def lanes2Wit (d0 d1 : TableDfa Nat Nat) (q0 q1 : Nat) (w : List Nat) : VmTrace :=
  { rows := lanes2Rows d0 d1 q0 q1 w
  , pub  := lanes2Pub q0 (classifyFrom d0 q0 w) q1 (classifyFrom d1 q1 w)
  , tf   := lanes2Tf (runTable d0 q0 w) (runTable d1 q1 w) }

/-- The 2-lane composed descriptor over two RUN tables. -/
def lanes2RunDesc (name : String) (d0 d1 : TableDfa Nat Nat) (q0 q1 : Nat) (w : List Nat) :
    EffectVmDescriptor2 :=
  lanesDesc name [runTable d0 q0 w, runTable d1 q1 w]

theorem lanes2_constraints (name : String) (t0 t1 : List (List Nat)) :
    (lanesDesc name [t0, t1]).constraints =
      [ .lookup ⟨LANE_TID 0, [.var (laneCurrent 0), .var LANE_SYMBOL, .var (laneNext 0)]⟩
      , .windowGate ⟨.add (.nxt (laneCurrent 0)) (.mul (.const (-1)) (.loc (laneNext 0))), true⟩
      , .base (.piBinding VmRow.first (laneCurrent 0) 0)
      , .base (.piBinding VmRow.last (laneNext 0) 1)
      , .lookup ⟨LANE_TID 1, [.var (laneCurrent 1), .var LANE_SYMBOL, .var (laneNext 1)]⟩
      , .windowGate ⟨.add (.nxt (laneCurrent 1)) (.mul (.const (-1)) (.loc (laneNext 1))), true⟩
      , .base (.piBinding VmRow.first (laneCurrent 1) 2)
      , .base (.piBinding VmRow.last (laneNext 1) 3) ] := rfl

theorem lanes2_tables (name : String) (t0 t1 : List (List Nat)) :
    (lanesDesc name [t0, t1]).tables = [laneTableDef 0 t0, laneTableDef 1 t1] := rfl

theorem lanes2_lookupLog0 (name : String) (t0 t1 : List (List Nat)) (t : VmTrace) :
    lookupLog (lanesDesc name [t0, t1]) t (LANE_TID 0)
      = t.rows.map (fun a => [a (laneCurrent 0), a LANE_SYMBOL, a (laneNext 0)]) := by
  show t.rows.flatMap
      (fun row => [[row (laneCurrent 0), row LANE_SYMBOL, row (laneNext 0)]]) = _
  induction t.rows with
  | nil => rfl
  | cons a rest ih => rw [List.flatMap_cons, ih]; rfl

theorem lanes2_lookupLog1 (name : String) (t0 t1 : List (List Nat)) (t : VmTrace) :
    lookupLog (lanesDesc name [t0, t1]) t (LANE_TID 1)
      = t.rows.map (fun a => [a (laneCurrent 1), a LANE_SYMBOL, a (laneNext 1)]) := by
  show t.rows.flatMap
      (fun row => [[row (laneCurrent 1), row LANE_SYMBOL, row (laneNext 1)]]) = _
  induction t.rows with
  | nil => rfl
  | cons a rest ih => rw [List.flatMap_cons, ih]; rfl

theorem lanes2_memLog (name : String) (t0 t1 : List (List Nat)) (t : VmTrace) :
    memLog (lanesDesc name [t0, t1]) t = [] := by
  simp [memLog, show memOpsOf (lanesDesc name [t0, t1]) = [] from rfl]

theorem lanes2_mapLog (name : String) (t0 t1 : List (List Nat)) (t : VmTrace) :
    mapLog (lanesDesc name [t0, t1]) t = [] := by
  simp [mapLog, show mapOpsOf (lanesDesc name [t0, t1]) = [] from rfl]

/-- ⚑ **THE SECOND WITNESS**: the 2-lane trace PROVABLY satisfies the emitted 2-lane descriptor.
Both lanes read the SAME symbol column; each lane's declared table is its OWN run, so each lane's
unit-capacity receive is balanced by an equality. -/
theorem lanes2Wit_satisfies (d0 d1 : TableDfa Nat Nat) (q0 q1 : Nat) (w : List Nat) (hw : w ≠ [])
    (name : String) :
    Satisfied2Public hash0 (lanes2RunDesc name d0 d1 q0 q1 w)
      (fun _ => 0) (fun _ => (0, 0)) [] (lanes2Wit d0 d1 q0 q1 w) where
  rowConstraints := by
    intro i hi c hc
    have hi' : i < (lanes2Rows d0 d1 q0 q1 w).length := hi
    have hloc : (envAt (lanes2Wit d0 d1 q0 q1 w) i).loc = (lanes2Rows d0 d1 q0 q1 w)[i]'hi' :=
      envAt_loc (t := lanes2Wit d0 d1 q0 q1 w) hi
    have hnotlast : (i + 1 == (lanes2Wit d0 d1 q0 q1 w).rows.length) = false →
        i + 1 < (lanes2Rows d0 d1 q0 q1 w).length := by
      intro hnl
      have hne' : ¬ (i + 1 = (lanes2Rows d0 d1 q0 q1 w).length) := by
        intro hEq
        rw [show (lanes2Wit d0 d1 q0 q1 w).rows = lanes2Rows d0 d1 q0 q1 w from rfl, hEq] at hnl
        simp at hnl
      omega
    rw [show lanes2RunDesc name d0 d1 q0 q1 w
        = lanesDesc name [runTable d0 q0 w, runTable d1 q1 w] from rfl,
      lanes2_constraints] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · -- lane 0 lookup
      show [(envAt (lanes2Wit d0 d1 q0 q1 w) i).loc (laneCurrent 0),
            (envAt (lanes2Wit d0 d1 q0 q1 w) i).loc LANE_SYMBOL,
            (envAt (lanes2Wit d0 d1 q0 q1 w) i).loc (laneNext 0)]
        ∈ lanes2Tf (runTable d0 q0 w) (runTable d1 q1 w) (LANE_TID 0)
      rw [hloc, show lanes2Tf (runTable d0 q0 w) (runTable d1 q1 w) (LANE_TID 0)
          = exactPublicTable (runTable d0 q0 w) from rfl,
        ← lanes2Rows_triples0 d0 d1 w q0 q1]
      exact List.mem_map.mpr ⟨(lanes2Rows d0 d1 q0 q1 w)[i]'hi', List.getElem_mem hi', rfl⟩
    · -- lane 0 continuity
      show WindowConstraint.holdsAt (envAt (lanes2Wit d0 d1 q0 q1 w) i)
        (i + 1 == (lanes2Wit d0 d1 q0 q1 w).rows.length)
        ⟨.add (.nxt (laneCurrent 0)) (.mul (.const (-1)) (.loc (laneNext 0))), true⟩
      simp only [WindowConstraint.holdsAt, if_true]
      intro hnl
      have hlt := hnotlast hnl
      have hnxt : (envAt (lanes2Wit d0 d1 q0 q1 w) i).nxt
          = (lanes2Rows d0 d1 q0 q1 w)[i + 1]'hlt :=
        envAt_nxt (t := lanes2Wit d0 d1 q0 q1 w) hlt
      have hch : ((lanes2Rows d0 d1 q0 q1 w)[i + 1]'hlt) (laneCurrent 0)
          = ((lanes2Rows d0 d1 q0 q1 w)[i]'hi') (laneNext 0) :=
        lanes2Rows_chain0 d0 d1 w q0 q1 i hlt
      simp only [WindowExpr.eval]
      rw [hloc, hnxt, hch]
      have hz : ((lanes2Rows d0 d1 q0 q1 w)[i]'hi') (laneNext 0)
          + (-1) * ((lanes2Rows d0 d1 q0 q1 w)[i]'hi') (laneNext 0) = 0 := by ring
      rw [hz]
    · -- lane 0 initial pin
      show (i == 0) = true → (envAt (lanes2Wit d0 d1 q0 q1 w) i).loc (laneCurrent 0)
        ≡ (envAt (lanes2Wit d0 d1 q0 q1 w) i).pub 0 [ZMOD 2013265921]
      intro hf
      have hi0 : i = 0 := by simpa using hf
      subst hi0
      rw [hloc, lanes2Rows_head0 d0 d1 q0 q1 w hw hi']
      exact Int.ModEq.refl _
    · -- lane 0 final pin
      show (i + 1 == (lanes2Wit d0 d1 q0 q1 w).rows.length) = true →
        (envAt (lanes2Wit d0 d1 q0 q1 w) i).loc (laneNext 0)
          ≡ (envAt (lanes2Wit d0 d1 q0 q1 w) i).pub 1 [ZMOD 2013265921]
      intro hl
      have hlast : i + 1 = (lanes2Rows d0 d1 q0 q1 w).length :=
        (by simpa using hl : i + 1 = (lanes2Wit d0 d1 q0 q1 w).rows.length)
      rw [hloc, lanes2Rows_last0 d0 d1 w q0 q1 i hi' hlast]
      exact Int.ModEq.refl _
    · -- lane 1 lookup
      show [(envAt (lanes2Wit d0 d1 q0 q1 w) i).loc (laneCurrent 1),
            (envAt (lanes2Wit d0 d1 q0 q1 w) i).loc LANE_SYMBOL,
            (envAt (lanes2Wit d0 d1 q0 q1 w) i).loc (laneNext 1)]
        ∈ lanes2Tf (runTable d0 q0 w) (runTable d1 q1 w) (LANE_TID 1)
      rw [hloc, show lanes2Tf (runTable d0 q0 w) (runTable d1 q1 w) (LANE_TID 1)
          = exactPublicTable (runTable d1 q1 w) from rfl,
        ← lanes2Rows_triples1 d0 d1 w q0 q1]
      exact List.mem_map.mpr ⟨(lanes2Rows d0 d1 q0 q1 w)[i]'hi', List.getElem_mem hi', rfl⟩
    · -- lane 1 continuity
      show WindowConstraint.holdsAt (envAt (lanes2Wit d0 d1 q0 q1 w) i)
        (i + 1 == (lanes2Wit d0 d1 q0 q1 w).rows.length)
        ⟨.add (.nxt (laneCurrent 1)) (.mul (.const (-1)) (.loc (laneNext 1))), true⟩
      simp only [WindowConstraint.holdsAt, if_true]
      intro hnl
      have hlt := hnotlast hnl
      have hnxt : (envAt (lanes2Wit d0 d1 q0 q1 w) i).nxt
          = (lanes2Rows d0 d1 q0 q1 w)[i + 1]'hlt :=
        envAt_nxt (t := lanes2Wit d0 d1 q0 q1 w) hlt
      have hch : ((lanes2Rows d0 d1 q0 q1 w)[i + 1]'hlt) (laneCurrent 1)
          = ((lanes2Rows d0 d1 q0 q1 w)[i]'hi') (laneNext 1) :=
        lanes2Rows_chain1 d0 d1 w q0 q1 i hlt
      simp only [WindowExpr.eval]
      rw [hloc, hnxt, hch]
      have hz : ((lanes2Rows d0 d1 q0 q1 w)[i]'hi') (laneNext 1)
          + (-1) * ((lanes2Rows d0 d1 q0 q1 w)[i]'hi') (laneNext 1) = 0 := by ring
      rw [hz]
    · -- lane 1 initial pin
      show (i == 0) = true → (envAt (lanes2Wit d0 d1 q0 q1 w) i).loc (laneCurrent 1)
        ≡ (envAt (lanes2Wit d0 d1 q0 q1 w) i).pub 2 [ZMOD 2013265921]
      intro hf
      have hi0 : i = 0 := by simpa using hf
      subst hi0
      rw [hloc, lanes2Rows_head1 d0 d1 q0 q1 w hw hi']
      exact Int.ModEq.refl _
    · -- lane 1 final pin
      show (i + 1 == (lanes2Wit d0 d1 q0 q1 w).rows.length) = true →
        (envAt (lanes2Wit d0 d1 q0 q1 w) i).loc (laneNext 1)
          ≡ (envAt (lanes2Wit d0 d1 q0 q1 w) i).pub 3 [ZMOD 2013265921]
      intro hl
      have hlast : i + 1 = (lanes2Rows d0 d1 q0 q1 w).length :=
        (by simpa using hl : i + 1 = (lanes2Wit d0 d1 q0 q1 w).rows.length)
      rw [hloc, lanes2Rows_last1 d0 d1 w q0 q1 i hi' hlast]
      exact Int.ModEq.refl _
  rowHashes := by intro i _; trivial
  rowRanges := by
    intro i _ r hr
    simp only [lanes2RunDesc, lanesDesc, List.not_mem_nil] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by rw [show lanes2RunDesc name d0 d1 q0 q1 w
    = lanesDesc name [runTable d0 q0 w, runTable d1 q1 w] from rfl, lanes2_memLog]; simp
  memDisciplined := by rw [show lanes2RunDesc name d0 d1 q0 q1 w
    = lanesDesc name [runTable d0 q0 w, runTable d1 q1 w] from rfl, lanes2_memLog]; trivial
  memBalanced := by rw [show lanes2RunDesc name d0 d1 q0 q1 w
    = lanesDesc name [runTable d0 q0 w, runTable d1 q1 w] from rfl, lanes2_memLog]
                    exact memCheck_nil _ _
  memTableFaithful := by rw [show lanes2RunDesc name d0 d1 q0 q1 w
    = lanesDesc name [runTable d0 q0 w, runTable d1 q1 w] from rfl, lanes2_memLog]; rfl
  mapTableFaithful := by rw [show lanes2RunDesc name d0 d1 q0 q1 w
    = lanesDesc name [runTable d0 q0 w, runTable d1 q1 w] from rfl, lanes2_mapLog]; rfl
  publicTablesFaithful := by
    intro td htd
    rw [show lanes2RunDesc name d0 d1 q0 q1 w
        = lanesDesc name [runTable d0 q0 w, runTable d1 q1 w] from rfl, lanes2_tables] at htd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htd
    rcases htd with rfl | rfl
    · show lanes2Tf (runTable d0 q0 w) (runTable d1 q1 w) (LANE_TID 0)
        = exactPublicTable (runTable d0 q0 w)
      rfl
    · show lanes2Tf (runTable d0 q0 w) (runTable d1 q1 w) (LANE_TID 1)
        = exactPublicTable (runTable d1 q1 w)
      rfl
  publicLookupBalanced := by
    intro td htd
    rw [show lanes2RunDesc name d0 d1 q0 q1 w
        = lanesDesc name [runTable d0 q0 w, runTable d1 q1 w] from rfl, lanes2_tables] at htd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htd
    rcases htd with rfl | rfl
    · show (lookupLog (lanesDesc name [runTable d0 q0 w, runTable d1 q1 w])
        (lanes2Wit d0 d1 q0 q1 w) (LANE_TID 0)).Perm (exactPublicTable (runTable d0 q0 w))
      rw [lanes2_lookupLog0]
      exact (lanes2Rows_triples0 d0 d1 w q0 q1) ▸ List.Perm.refl _
    · show (lookupLog (lanesDesc name [runTable d0 q0 w, runTable d1 q1 w])
        (lanes2Wit d0 d1 q0 q1 w) (LANE_TID 1)).Perm (exactPublicTable (runTable d1 q1 w))
      rw [lanes2_lookupLog1]
      exact (lanes2Rows_triples1 d0 d1 w q0 q1) ▸ List.Perm.refl _

/-! ## §7 — ⚑ THE COST LAW, over families that HAVE WITNESSES.

Everything below is READ OFF the emitted descriptors by `TinyAutomataCompose.costOf` / `jsonBytes`,
at the fixed 8-symbol probe word. ⚠ `#guard` is compiled evaluation and proves NO `Prop`; the
`Prop`-level content is `prodRunWit_satisfies` / `lanes2Wit_satisfies` (the witnesses),
`forced_trace_length` (why a declared table pins the trace length, hence AREA) and
`productDesc_refines_components` (why the composed verdict is sound).

**What is WITNESSED.** Product-first at `k = 1, 2, 3, 4` (`prodRunWit_satisfies`, general in `k`);
parallel-lanes at `k = 2` (`lanesRunI2_satisfies`). At `k = 1` the two routes are the same 3-column
object. So both endpoints of the claimed crossover carry a satisfying trace. -/

/-- The `k`-lane run-table descriptor over the independent family (measurement only for `k ≠ 2`;
`k = 2` is the witnessed `lanesRunI2`). -/
def lanesRunI (k : Nat) (w : List Nat) : EffectVmDescriptor2 :=
  lanesDesc s!"tiny-automata-indep-lanes-run-k{k}::exact-public-v1"
    ((famI k).map (fun d => runTable d 0 w))

/-- The witnessed 2-lane instance's name. -/
def LANES2_NAME : String := "tiny-automata-indep-lanes-run-k2::exact-public-v1"

/-- The witnessed 2-lane descriptor: lanes for "even number of 1s" and "count divisible by 3". -/
def lanesRunI2 : EffectVmDescriptor2 :=
  lanes2RunDesc LANES2_NAME modTwoDfa modThreeDfa 0 0 probeW

/-- ⚑ **THE SECOND ROUTE'S WITNESS, concrete.** -/
theorem lanesRunI2_satisfies :
    Satisfied2Public hash0 lanesRunI2 (fun _ => 0) (fun _ => (0, 0)) []
      (lanes2Wit modTwoDfa modThreeDfa 0 0 probeW) :=
  lanes2Wit_satisfies modTwoDfa modThreeDfa 0 0 probeW probeW_ne LANES2_NAME

-- The witnessed instance IS the `k = 2` member of the measured lanes family (byte identity of the
-- emitted descriptors — compiled evaluation).
#guard emitVmJson2 (lanesRunI 2 probeW) == emitVmJson2 lanesRunI2

-- ⚑ PRODUCT-FIRST over a RUN table is FLAT in `k` on EVERY axis: 3 columns, 4 constraints, 2 PIs,
-- ONE table of `|w| = 8` rows, 8 forced trace rows, 0 nonlinear multiplications — at k = 1, 2, 3, 4.
#guard (List.map (fun k => costOf (prodRunDesc k probeW)) [1, 2, 3, 4]) ==
  [ { traceWidth := 3, piCount := 2, constraints := 4, tables := 1
    , declaredRows := 8, forcedTraceRows := .pinned 8, nonlinearMults := 0 }
  , { traceWidth := 3, piCount := 2, constraints := 4, tables := 1
    , declaredRows := 8, forcedTraceRows := .pinned 8, nonlinearMults := 0 }
  , { traceWidth := 3, piCount := 2, constraints := 4, tables := 1
    , declaredRows := 8, forcedTraceRows := .pinned 8, nonlinearMults := 0 }
  , { traceWidth := 3, piCount := 2, constraints := 4, tables := 1
    , declaredRows := 8, forcedTraceRows := .pinned 8, nonlinearMults := 0 } ]

-- ⚑ PARALLEL LANES over run tables: `1 + 2k` columns, `4k` constraints, `2k` PIs, `k` tables of 8
-- rows each — and the SAME 8 forced trace rows (every lane's table has |w| rows, so the
-- equal-row-count side condition of `lanesDesc` is met by construction under the run discipline).
#guard (List.map (fun k => costOf (lanesRunI k probeW)) [1, 2, 3, 4]) ==
  [ { traceWidth := 3,  piCount := 2, constraints := 4,  tables := 1
    , declaredRows := 8,  forcedTraceRows := .pinned 8, nonlinearMults := 0 }
  , { traceWidth := 5,  piCount := 4, constraints := 8,  tables := 2
    , declaredRows := 16, forcedTraceRows := .pinned 8, nonlinearMults := 0 }
  , { traceWidth := 7,  piCount := 6, constraints := 12, tables := 3
    , declaredRows := 24, forcedTraceRows := .pinned 8, nonlinearMults := 0 }
  , { traceWidth := 9,  piCount := 8, constraints := 16, tables := 4
    , declaredRows := 32, forcedTraceRows := .pinned 8, nonlinearMults := 0 } ]

-- ⚑ THE LAW, IN AREA (columns × the trace length the exact-public receive PINS): product-first is
-- FLAT at 3·|w| = 24 for every k; lanes are (1 + 2k)·|w| = 24, 40, 56, 72. They TIE at k = 1 (the
-- same object) and PRODUCT-FIRST WINS STRICTLY FROM k = 2 ON. Both k = 1 and k = 2 carry witnesses.
#guard (List.map (fun k => ((costOf (prodRunDesc k probeW)).area,
    (costOf (lanesRunI k probeW)).area)) [1, 2, 3, 4])
  == [(some 24, some 24), (some 24, some 40), (some 24, some 56), (some 24, some 72)]

-- The same in EMITTED DESCRIPTOR BYTES (the verifier-held object): the product's run descriptor
-- barely moves with k (669 → 685); the lanes' grows ~496 bytes per lane (672 → 2160).
#guard (List.map (fun k => (jsonBytes (prodRunDesc k probeW), jsonBytes (lanesRunI k probeW)))
    [1, 2, 3, 4]) -- ⚑ +15 bytes per emitted descriptor: `,"challenges":0` (2026-08-05). Both routes pay it
    -- once, so the SHAPE this guard measures — flat vs ~496/lane — is unchanged.
    == [(669, 672), (669, 1168), (680, 1664), (685, 2160)]

-- ⚑ AND THE FORK THAT ACTUALLY COSTS: WHOLE-GRAPH vs RUN tables, at the SAME product route. The
-- reachability-minimised whole-graph declaration pins 4, 12, 24, 50 trace rows (area 12, 36, 72,
-- 150) against the run table's flat 8 rows / area 24. ⚠ NO witness is exhibited for ANY whole-graph
-- declaration (the Eulerian obstruction of `TinyAutomataCompose` is unresolved for them), so these
-- are quoted as the COST of an object whose satisfiability is OPEN — never as a crossover.
#guard (List.map (fun k => (costOf (tableRoutingDesc "wg" (reachTable (prodI k) 24))).area)
    [1, 2, 3, 4]) == [some 12, some 36, some 72, some 150]

/-! ### The law, stated

At a fixed word length `|w|`, under the RUN-table discipline (the only one with witnesses):

  * **product-first** — `traceWidth 3`, `4` constraints, `2` PIs, `1` table of `|w|` rows,
    `0` nonlinear multiplications, AREA `3·|w|`. INDEPENDENT of `k`. Witnessed at `k = 1…4`.
  * **parallel lanes** — `traceWidth 1 + 2k`, `4k` constraints, `2k` PIs, `k` tables of `|w|` rows,
    `0` nonlinear multiplications, AREA `(1 + 2k)·|w|`. Witnessed at `k = 2`.
  * TIE in AREA at `k = 1` (24 = 24 — the two routes are the same 3-column object there);
    product-first strictly cheaper for every `k ≥ 2`, on EVERY axis measured — AREA (24 vs 40, 56,
    72), constraints (4 vs 8, 12, 16), PIs (2 vs 4, 6, 8) and wire bytes (654/665/670 vs 1153, 1649,
    2145). There is NO axis on which lanes win: even at `k = 1` the lanes descriptor is 3 bytes
    larger (657 vs 654), from the longer table name. The `TinyAutomataCompose` headline — "lanes
    win at every `k ≥ 2`, AREA crossover `k = 2`" — is exactly inverted once both sides are
    satisfiable, and its own §4b already predicted this flip for run tables.

What product-first costs is ATTESTATION, exactly as `TinyAutomataCompose` §4b said and this file
does not repair: a run table commits the edges TRAVERSED, not the automaton, so "which product
automaton ran" must be bound elsewhere. The whole-graph declaration buys that binding — at 12 → 150
area over `k = 1…4` even after reachability minimisation, and with NO witness in hand. -/

/-! ## §8 — axiom tripwires. -/

#assert_axioms indep_step_lt
#assert_axioms famI_step_lt
#assert_axioms runRows_length
#assert_axioms runRows_triples
#assert_axioms runRows_chain
#assert_axioms runRows_head_current
#assert_axioms runRows_last_next
#assert_axioms runRows_symbols
#assert_axioms runWit_rows_ne
#assert_axioms runWit_lookupLog
#assert_axioms trt_memLog
#assert_axioms trt_mapLog
#assert_axioms runWit_satisfies
#assert_axioms prodRunWit_satisfies
#assert_axioms encodeDigits_replicate_zero
#assert_axioms prodRunWit_exposes_components
#assert_axioms prodRunWit_k2_components
#assert_axioms prodRunWit_k3_components
#assert_axioms prodRunWit_k4_components
#assert_axioms lanes2Rows_length
#assert_axioms lanes2Rows_triples0
#assert_axioms lanes2Rows_triples1
#assert_axioms lanes2Rows_chain0
#assert_axioms lanes2Rows_chain1
#assert_axioms lanes2Rows_head0
#assert_axioms lanes2Rows_head1
#assert_axioms lanes2Rows_last0
#assert_axioms lanes2Rows_last1
#assert_axioms lanes2_lookupLog0
#assert_axioms lanes2_lookupLog1
#assert_axioms lanes2Wit_satisfies
#assert_axioms lanesRunI2_satisfies

end Dregg2.Circuit.Emit.TinyAutomataSatisfiable
