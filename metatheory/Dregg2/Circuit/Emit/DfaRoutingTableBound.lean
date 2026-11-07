/-
# Dregg2.Circuit.Emit.DfaRoutingTableBound — what the table-routing family binds about its word,
and the statement its legacy shape cannot make (L2).

Lane E, `docs/automata/SUBSTRATE-DECISION.md` §5.2. 2026-11-06.

## The family

`DfaRoutingTableEmit.tableRoutingDesc name tbl` (legacy served name `dregg-dfa-routing-table::exact-public-v1`):
three columns `(current, symbol, next)`, one lookup into the DECLARED exact-public transition table,
a continuity window, and two PIs (`initial_state`, `final_state`). Its refinement
`tableRouting_refines_classify` reads the word off the private symbol column.

## Correction to the brief, on contact [READ]

The exact-public table is the TRANSITION table, not the word: `pi` carries two states and nothing
else, so the word is not public. What the exact-public semantics does make public is the MULTISET
of transitions the run uses: `exactPublicRows` is a unit-capacity LogUp receive
(`Satisfied2Public.exact_lookup_perm`), so the run's `(current, symbol, next)` triples are a
permutation of the declared rows.

## What is proved

  * `lookupLog_eq` — the descriptor's lookup log is the trace's triple column.
  * ⚑ `tableRouting_trail` — a necessary public-data characterization: a satisfying trace's triples
    (read as naturals) are a PERMUTATION of the declared table, form a TRAIL from the public initial
    state (each row starts where the previous ended), and the word is the trail's label column.
    This is a forward implication, not a completeness theorem constructing a satisfying trace.
  * ⚑ `word_public_of_functional` — the trivial binding, where it holds: if every state has at most
    one declared row (checked by `functionalB tbl` and proved `Functional tbl`), any two satisfying traces with the same initial state read
    the SAME word. The word is then a function of public data (`trail_unique`).

## Falsifier (§4, kernel-checked)

The table `[(0,1,0), (0,2,0)]` (two self-loops at `0`) is not functional. The traces reading `[1,2]`
and `[2,1]` BOTH satisfy the served descriptor with the same public inputs and the same table
(`tA_satisfies`, `tB_satisfies`), and both meet the unbound shape (`tableRouting_refines_classify`
fires on each). `word_not_public`: no function of the public data `(tbl, initial, final)` returns
the read word; `bound_shape_fails`: for an injective content scheme no single commitment `c` is
opened by both, so a statement naming the record cannot be discharged by this descriptor.

## The additive ordered shape

`DfaRoutingTableRoute8.tableRoutingBoundDesc` retains the certified table lowering and adds
`RouteChain8`: eight predecessor lanes, eight output lanes, a one-based position, eight public
route lanes and public length. One arity-16 lookup per row binds domain/position/edge/predecessor8;
three literal zeros pad the meaningful 13 inputs to the admitted arity. This is +17 columns,
+9 PIs, +28 constraints, +1 wide permutation per row. `DfaRoutingTableRoute8Bound` supplies the
bound statement. The legacy shape and its counterexample remain useful as the weak control.

## Axiom hygiene
`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.DfaRoutingTableEmit

namespace Dregg2.Circuit.Emit.DfaRoutingTableBound

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
  (VmConstraint VmRow VmRowEnv holdsVm_piFirst_true holdsVm_piLast_true)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.DfaRoutingTableEmit
open Dregg2.Crypto.DfaAcceptanceAir (TableDfa classifyFrom)

set_option autoImplicit false

/-! ## §1 — The lookup log is the triple column; the triples are the declared multiset. -/

/-- A row's triple as integers (what the lookup reads). -/
def triZ (a : Assignment) : List ℤ := [a CURRENT, a SYMBOL, a NEXT]

/-- A row's triple as naturals. -/
def tri (a : Assignment) : List ℕ := [(a CURRENT).toNat, (a SYMBOL).toNat, (a NEXT).toNat]

/-- The word a trace reads. -/
def readWord (t : VmTrace) : List ℕ := t.rows.map fun a => (a SYMBOL).toNat

theorem lookupLog_eq (name : String) (tbl : List (List Nat)) (t : VmTrace) :
    lookupLog (tableRoutingDesc name tbl) t TRT_TID = t.rows.map triZ := by
  have h : ∀ l : List Assignment,
      List.flatMap (fun row => [[row CURRENT, row SYMBOL, row NEXT]]) l = l.map triZ := by
    intro l
    induction l with
    | nil => rfl
    | cons a as ih => simp [ih, triZ]
  simpa [lookupLog, tableRoutingDesc_constraints, EmittedExpr.eval] using h t.rows

/-- A trail from `q`: each row starts where the previous one ended (`[state, symbol, next]`). -/
def IsTrail : ℕ → List (List ℕ) → Prop
  | _, [] => True
  | q, r :: rs => r.getD 0 0 = q ∧ IsTrail (r.getD 2 0) rs

theorem isTrail_of_chain : ∀ (l : List Assignment) (q : ℕ),
    (∀ a₀, l.head? = some a₀ → (a₀ CURRENT).toNat = q) →
    (∀ i (_ : i + 1 < l.length), ((l[i + 1]) CURRENT).toNat = ((l[i]) NEXT).toNat) →
    IsTrail q (l.map tri)
  | [], _, _, _ => trivial
  | [a], q, hh, _ => ⟨hh a rfl, trivial⟩
  | a :: b :: rest, q, hh, hc => by
    refine ⟨hh a rfl, isTrail_of_chain (b :: rest) _ (fun a₀ h₀ => ?_) (fun i hi => ?_)⟩
    · simp only [List.head?_cons, Option.some.injEq] at h₀
      subst h₀
      have := hc 0 (by simp)
      simpa [tri] using this
    · have := hc (i + 1) (by simp only [List.length_cons] at hi ⊢; omega)
      simpa using this

section Extract
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
variable {name : String} {tbl : List (List Nat)} {t : VmTrace}

/-- Every row's integer triple is the image of a declared row, and its natural triple IS that row. -/
theorem row_decl (hsat : Satisfied2Public hash (tableRoutingDesc name tbl) minit mfin maddrs t)
    {i : Nat} (hi : i < t.rows.length) :
    tri (t.rows[i]'hi) ∈ tbl ∧ triZ (t.rows[i]'hi) = (tri (t.rows[i]'hi)).map Int.ofNat := by
  have h := row_triple hsat hi
  simp only [exactPublicTable, List.mem_map] at h
  obtain ⟨r, hr, hmap⟩ := h
  have hl : r.length = 3 := by
    have := congrArg List.length hmap; simp at this; omega
  obtain ⟨x, y, z, rfl⟩ := List.length_eq_three.mp hl
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmap
  obtain ⟨h1, h2, h3⟩ := hmap
  have ht : tri (t.rows[i]'hi) = [x, y, z] := by
    simp only [tri, ← h1, ← h2, ← h3]; rfl
  refine ⟨ht ▸ hr, ?_⟩
  rw [ht]; simp only [triZ, ← h1, ← h2, ← h3]; rfl

/-- ⚑ **`tableRouting_trail`** — the complete public-data characterization of the word. -/
theorem tableRouting_trail
    (hsat : Satisfied2Public hash (tableRoutingDesc name tbl) minit mfin maddrs t)
    (hne : t.rows ≠ [])
    (hsmall : ∀ r ∈ tbl, ∀ v ∈ r, v < 2013265921)
    (q0 : ℕ) (hstart : t.pub PI_INITIAL = Int.ofNat q0) (hq0 : q0 < 2013265921) :
    (t.rows.map tri).Perm tbl ∧ IsTrail q0 (t.rows.map tri) ∧
      readWord t = (t.rows.map tri).map (·.getD 1 0) := by
  have hpos : 0 < t.rows.length := List.length_pos_of_ne_nil hne
  refine ⟨?_, ?_, ?_⟩
  · -- the multiset
    have hp := hsat.exact_lookup_perm (td := transitionTableDef tbl)
      (by simp [tableRoutingDesc_tables]) (rows := tbl) rfl
    have hp' : (lookupLog (tableRoutingDesc name tbl) t TRT_TID).Perm (exactPublicTable tbl) := hp
    rw [lookupLog_eq] at hp'
    clear hp
    have hp := hp'
    have hz : t.rows.map triZ = (t.rows.map tri).map (List.map Int.ofNat) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro a ha
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
      exact (row_decl hsat hi).2
    rw [hz] at hp
    have hp2 := hp.map (List.map Int.toNat)
    simp only [exactPublicTable, List.map_map] at hp2
    have hcomp : (List.map Int.toNat ∘ List.map Int.ofNat ∘ tri) = tri := by
      funext a; simp [Function.comp_def]
    have hcomp2 : (List.map Int.toNat ∘ List.map Int.ofNat) = (id : List ℕ → List ℕ) := by
      funext l; simp [Function.comp_def]
    simpa [hcomp, hcomp2] using hp2
  · -- the trail
    apply isTrail_of_chain
    · intro a₀ h₀
      have h0 : t.rows[0]'hpos = a₀ := by
        rw [List.head?_eq_some_head hne] at h₀
        rw [← Option.some.inj h₀, List.head_eq_getElem hne]
      obtain ⟨hm, hz⟩ := row_decl hsat hpos
      have hpf := piFirst_forces hsat hne
      rw [envAt_loc hpos, hstart] at hpf
      have hc : (t.rows[0]'hpos) CURRENT = Int.ofNat ((t.rows[0]'hpos) CURRENT).toNat := by
        have := congrArg (·.getD 0 0) hz; simpa [triZ, tri] using this
      rw [hc] at hpf
      have := ofNat_eq_of_modEq (hsmall _ hm _ (by simp [tri])) hq0 hpf
      rw [← h0]; exact this
    · intro i hi1
      have hi : i < t.rows.length := Nat.lt_of_succ_lt hi1
      obtain ⟨hm1, hz1⟩ := row_decl hsat hi1
      obtain ⟨hm0, hz0⟩ := row_decl hsat hi
      have hw := window_forces hsat hi (Nat.ne_of_lt hi1)
      have hx : (envAt t i).nxt CURRENT = Int.ofNat ((t.rows[i + 1]'hi1) CURRENT).toNat := by
        rw [envAt_nxt hi1]
        have := congrArg (·.getD 0 0) hz1; simpa [triZ, tri] using this
      have hy : (envAt t i).loc NEXT = Int.ofNat ((t.rows[i]'hi) NEXT).toNat := by
        rw [envAt_loc hi]
        have := congrArg (·.getD 2 0) hz0; simpa [triZ, tri] using this
      exact cont_eq hw hx hy (hsmall _ hm1 _ (by simp [tri])) (hsmall _ hm0 _ (by simp [tri]))
  · simp [readWord, tri, Function.comp_def]

end Extract

/-! ## §2 — The trivial binding: a functional table admits one trail, so the word is public. -/

/-- At most one declared row per source state. -/
def Functional (tbl : List (List Nat)) : Prop :=
  ∀ r ∈ tbl, ∀ r' ∈ tbl, r.getD 0 0 = r'.getD 0 0 → r = r'

/-- Validate the public finite table, rather than assuming an ideal hash floor.
The entire declared row is determined by its source state. -/
def functionalB (tbl : List (List Nat)) : Bool :=
  tbl.all fun r => tbl.all fun r' => decide (r.getD 0 0 ≠ r'.getD 0 0 ∨ r = r')

/-- The original finite structural invariant is constructively decidable. -/
instance functionalDecidable (tbl : List (List Nat)) : Decidable (Functional tbl) := by
  unfold Functional
  infer_instance

/-- Exact decision-procedure correctness, including completeness. This claims
an equality for every table; it does not assume the structural invariant. -/
theorem functionalB_eq_decide (tbl : List (List Nat)) :
    functionalB tbl = decide (Functional tbl) := by
  apply Bool.eq_iff_iff.mpr
  simp only [functionalB, List.all_eq_true, decide_eq_true_eq, Functional]
  simp only [ne_eq, or_iff_not_imp_left, not_not]

/-- The executable validator establishes the exact structural invariant. -/
theorem functionalB_sound {tbl : List (List Nat)} (h : functionalB tbl = true) :
    Functional tbl := by
  intro r hr r' hr' he
  have hrow := List.all_eq_true.mp h r hr
  have hpair := of_decide_eq_true (List.all_eq_true.mp hrow r' hr')
  exact hpair.resolve_left (fun hne => hne he)

theorem trail_unique {tbl : List (List Nat)} (hf : functionalB tbl = true) :
    ∀ (q : ℕ) (T₁ T₂ : List (List ℕ)), (∀ r ∈ T₁, r ∈ tbl) → (∀ r ∈ T₂, r ∈ tbl) →
      T₁.length = T₂.length → IsTrail q T₁ → IsTrail q T₂ → T₁ = T₂
  | _, [], [], _, _, _, _, _ => rfl
  | _, [], _ :: _, _, _, hl, _, _ => by simp at hl
  | _, _ :: _, [], _, _, hl, _, _ => by simp at hl
  | q, r₁ :: R₁, r₂ :: R₂, h₁, h₂, hl, ⟨hq₁, ht₁⟩, ⟨hq₂, ht₂⟩ => by
    have hr : r₁ = r₂ := functionalB_sound hf r₁ (h₁ r₁ List.mem_cons_self) r₂ (h₂ r₂ List.mem_cons_self)
      (by rw [hq₁, hq₂])
    subst hr
    rw [trail_unique hf _ R₁ R₂ (fun r hr => h₁ r (List.mem_cons_of_mem _ hr))
      (fun r hr => h₂ r (List.mem_cons_of_mem _ hr)) (by simpa using hl) ht₁ ht₂]

/-- ⚑ **`word_public_of_functional`** — for a functional table, two satisfying traces with the
same initial state read the same word: the word is a function of the public data.
The finite-table validator must succeed; no global cryptographic injectivity is assumed. -/
theorem word_public_of_functional {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {name : String} {tbl : List (List Nat)} {t₁ t₂ : VmTrace}
    (hf : functionalB tbl = true) (hsmall : ∀ r ∈ tbl, ∀ v ∈ r, v < 2013265921)
    (h₁ : Satisfied2Public hash (tableRoutingDesc name tbl) minit mfin maddrs t₁)
    (h₂ : Satisfied2Public hash (tableRoutingDesc name tbl) minit mfin maddrs t₂)
    (hne₁ : t₁.rows ≠ []) (hne₂ : t₂.rows ≠ [])
    (q0 : ℕ) (hq0 : q0 < 2013265921)
    (hs₁ : t₁.pub PI_INITIAL = Int.ofNat q0) (hs₂ : t₂.pub PI_INITIAL = Int.ofNat q0) :
    readWord t₁ = readWord t₂ := by
  obtain ⟨hp₁, ht₁, hw₁⟩ := tableRouting_trail h₁ hne₁ hsmall q0 hs₁ hq0
  obtain ⟨hp₂, ht₂, hw₂⟩ := tableRouting_trail h₂ hne₂ hsmall q0 hs₂ hq0
  rw [hw₁, hw₂, trail_unique hf q0 _ _ (fun r hr => hp₁.subset hr) (fun r hr => hp₂.subset hr)
    (by rw [hp₁.length_eq, hp₂.length_eq]) ht₁ ht₂]

/-! ## §3 — Non-vacuity of the trivial binding on the served demo table. -/

theorem demoTbl_functional : Functional demoTbl := by
  intro r hr r' hr' _
  simp only [demoTbl, List.mem_singleton] at hr hr'
  rw [hr, hr']

/-- A non-singleton validation witness: different states determine different rows. -/
theorem two_rows_functionalB : functionalB [[0, 1, 1], [1, 2, 2]] = true := rfl

/-- The two distinct rows also inhabit the proposition established by validation. -/
theorem two_rows_functional : Functional [[0, 1, 1], [1, 2, 2]] :=
  functionalB_sound two_rows_functionalB

/-- The demo witness's trail and word: `[1]`, read along the one declared row. -/
theorem demo_trail :
    (routeWitTrace.rows.map tri).Perm demoTbl ∧ IsTrail 0 (routeWitTrace.rows.map tri) ∧
      readWord routeWitTrace = [1] :=
  let h := tableRouting_trail routeWit_satisfies (List.cons_ne_nil _ _) demoTbl_small 0 rfl
    (by decide)
  ⟨h.1, h.2.1, rfl⟩

/-! ## §4 — The falsifier: a non-functional table, two words, one public statement. -/

/-- Two self-loops at state `0`, on symbols `1` and `2`. -/
def loopTbl : List (List Nat) := [[0, 1, 0], [0, 2, 0]]
def LOOP_NAME : String := "lane-e-loop-falsifier"
def loopDesc : EffectVmDescriptor2 := tableRoutingDesc LOOP_NAME loopTbl

def row1 : Assignment := fun c => if c = 1 then 1 else 0
def row2 : Assignment := fun c => if c = 1 then 2 else 0
def loopPub : Assignment := fun _ => 0
def loopTf : TraceFamily := fun id => if id = TRT_TID then exactPublicTable loopTbl else []

/-- Reads `[1, 2]`. -/
def tA : VmTrace := { rows := [row1, row2], pub := loopPub, tf := loopTf }
/-- Reads `[2, 1]`. -/
def tB : VmTrace := { rows := [row2, row1], pub := loopPub, tf := loopTf }

theorem memLog_loop (t : VmTrace) : memLog loopDesc t = [] := by
  simp [memLog, memOpsOf, loopDesc, tableRoutingDesc_constraints]
theorem mapLog_loop (t : VmTrace) : mapLog loopDesc t = [] := by
  simp [mapLog, mapOpsOf, loopDesc, tableRoutingDesc_constraints]

theorem loop_satisfies (t : VmTrace) (ht : t = tA ∨ t = tB) :
    Satisfied2Public hash0 loopDesc (fun _ => 0) (fun _ => (0, 0)) [] t := by
  rcases ht with rfl | rfl <;>
  exact
    { rowConstraints := by
        intro i hi c hc
        simp only [loopDesc, tableRoutingDesc_constraints, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        have hi2 : i < 2 := hi
        interval_cases i <;> rcases hc with rfl | rfl | rfl | rfl <;>
          simp [VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt,
            WindowConstraint.holdsAt, envAt, tA, tB, row1, row2, loopPub, loopTf, exactPublicTable,
            loopTbl, contWindowBody_eq, WindowExpr.eval, EmittedExpr.eval, CURRENT, SYMBOL, NEXT,
            PI_INITIAL, PI_FINAL]
      rowHashes := by intro i _; trivial
      rowRanges := by intro i _ r hr; simp only [loopDesc, tableRoutingDesc_ranges,
        List.not_mem_nil] at hr
      memAddrsNodup := List.nodup_nil
      memClosed := by rw [memLog_loop]; simp
      memDisciplined := by rw [memLog_loop]; trivial
      memBalanced := by rw [memLog_loop]; exact memCheck_nil _ _
      memTableFaithful := by rw [memLog_loop]; rfl
      mapTableFaithful := by rw [mapLog_loop]; rfl
      publicTablesFaithful := by
        intro td htd
        simp only [loopDesc, tableRoutingDesc_tables, List.mem_singleton] at htd
        subst htd
        rfl
      publicLookupBalanced := by
        intro td htd
        simp only [loopDesc, tableRoutingDesc_tables, List.mem_singleton] at htd
        subst htd
        show (lookupLog loopDesc _ TRT_TID).Perm (exactPublicTable loopTbl)
        rw [loopDesc, lookupLog_eq]
        first
          | exact List.Perm.refl _
          | exact List.Perm.swap _ _ _ }

theorem tA_satisfies : Satisfied2Public hash0 loopDesc (fun _ => 0) (fun _ => (0, 0)) [] tA :=
  loop_satisfies tA (Or.inl rfl)
theorem tB_satisfies : Satisfied2Public hash0 loopDesc (fun _ => 0) (fun _ => (0, 0)) [] tB :=
  loop_satisfies tB (Or.inr rfl)

/-- The loop table's step function (every edge returns to `0`). -/
def loopDfa : TableDfa Nat Nat := { step := fun _ _ => 0, start := 0, accepts := fun s => s = 0 }

theorem loopTbl_graph : ∀ r ∈ loopTbl, ∃ s y, r = [s, y, loopDfa.step s y] := by
  intro r hr
  simp only [loopTbl, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨0, 1, rfl⟩
  · exact ⟨0, 2, rfl⟩

theorem loopTbl_small : ∀ r ∈ loopTbl, ∀ v ∈ r, v < 2013265921 := by decide

/-- Both traces MEET the unbound shape: each is classified by the refinement. -/
theorem both_meet_unbound :
    (0 : ℕ) = classifyFrom loopDfa 0 (tA.rows.map fun a => (a SYMBOL).toNat) ∧
    (0 : ℕ) = classifyFrom loopDfa 0 (tB.rows.map fun a => (a SYMBOL).toNat) :=
  ⟨(tableRouting_refines_classify loopDfa loopTbl_graph loopTbl_small tA_satisfies
      (List.cons_ne_nil _ _) 0 rfl (by decide) 0 rfl (by decide)).2,
   (tableRouting_refines_classify loopDfa loopTbl_graph loopTbl_small tB_satisfies
      (List.cons_ne_nil _ _) 0 rfl (by decide) 0 rfl (by decide)).2⟩

theorem tA_word : readWord tA = [1, 2] := by decide
theorem tB_word : readWord tB = [2, 1] := by decide

/-- ⚑ **`word_not_public`** — no function of the public data returns the read word. -/
theorem word_not_public :
    ¬ ∃ f : List (List Nat) → ℤ → ℤ → List ℕ, ∀ t : VmTrace,
      Satisfied2Public hash0 loopDesc (fun _ => 0) (fun _ => (0, 0)) [] t →
        readWord t = f loopTbl (t.pub PI_INITIAL) (t.pub PI_FINAL) := by
  rintro ⟨f, hf⟩
  have hA := hf tA tA_satisfies
  have hB := hf tB tB_satisfies
  rw [tA_word] at hA
  rw [tB_word] at hB
  have : ([1, 2] : List ℕ) = [2, 1] := by
    rw [hA, hB]; rfl
  exact absurd this (by decide)

/-- ⚑ **`bound_shape_fails`** — for an injective content scheme, no commitment `c` is opened by the
words of both satisfying traces of one public statement: the bound shape cannot be discharged by
this descriptor. -/
theorem bound_shape_fails {D : Type} (commit : List ℕ → D) (hinj : Function.Injective commit) :
    ¬ ∃ c : D, ∀ t : VmTrace,
      Satisfied2Public hash0 loopDesc (fun _ => 0) (fun _ => (0, 0)) [] t → commit (readWord t) = c := by
  rintro ⟨c, hc⟩
  have h := hinj ((hc tA tA_satisfies).trans (hc tB tB_satisfies).symm)
  rw [tA_word, tB_word] at h
  exact absurd h (by decide)

/-- The actual public-data validator rejects the two competing source-state rows. -/
theorem loopTbl_functionalB_false : functionalB loopTbl = false := rfl

/-- The loop table is not functional (so `word_public_of_functional` is silent on it, as it must be). -/
theorem loopTbl_not_functional : ¬ Functional loopTbl := by
  intro h
  have := h [0, 1, 0] (by simp [loopTbl]) [0, 2, 0] (by simp [loopTbl]) rfl
  exact absurd this (by decide)

/-! ## §5 — axiom tripwires. -/

#assert_all_clean [lookupLog_eq, isTrail_of_chain, row_decl, tableRouting_trail, trail_unique,
  word_public_of_functional, demoTbl_functional, demo_trail, memLog_loop, mapLog_loop,
  loop_satisfies, tA_satisfies, tB_satisfies, loopTbl_graph, both_meet_unbound, tA_word, tB_word,
  word_not_public, bound_shape_fails, loopTbl_not_functional, functionalB_eq_decide, functionalB_sound,
  two_rows_functionalB, two_rows_functional, loopTbl_functionalB_false]

/-- info: 'Dregg2.Circuit.Emit.DfaRoutingTableBound.functionalB_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms functionalB_sound
/-- info: 'Dregg2.Circuit.Emit.DfaRoutingTableBound.two_rows_functionalB' depends on axioms: [propext] -/
#guard_msgs in
#print axioms two_rows_functionalB
/-- info: 'Dregg2.Circuit.Emit.DfaRoutingTableBound.two_rows_functional' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms two_rows_functional
/-- info: 'Dregg2.Circuit.Emit.DfaRoutingTableBound.loopTbl_functionalB_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms loopTbl_functionalB_false
/-- info: 'Dregg2.Circuit.Emit.DfaRoutingTableBound.trail_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trail_unique
/-- info: 'Dregg2.Circuit.Emit.DfaRoutingTableBound.word_public_of_functional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms word_public_of_functional

/-- info: 'Dregg2.Circuit.Emit.DfaRoutingTableBound.functionalB_eq_decide' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms functionalB_eq_decide

end Dregg2.Circuit.Emit.DfaRoutingTableBound
