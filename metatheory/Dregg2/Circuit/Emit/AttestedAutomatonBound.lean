/-
# Dregg2.Circuit.Emit.AttestedAutomatonBound — the attested (8-felt welded) automaton: the whole-run
chaining corollary, and the word statement it cannot make (L2).

Lane E, `docs/automata/SUBSTRATE-DECISION.md` §5.2. 2026-11-06.

## The family

`AttestedAutomatonWeld8.weldDesc` under the 8-lane denotation `AttestedAutomatonLanes8.Satisfied2Lanes8`:
rows `(current, symbol, next, root₀..root₇)`, one map READ per row at key `2·current + symbol` against
the row's 8-felt root group, the group constant across rows and pinned to `pi[2..9]`, continuity,
`current` pinned to `pi[initial]` on the first row and `next` to `pi[final]` on the last, and range
lookups `current < 2^15`, `symbol < 2`. Lanes8's theorems are PER ROW (`weld8_forged_edge_refused`,
`weld8_accepted_run_is_committed_run`); its header names the chaining corollary as the next theorem.

## What is proved

  * `row_nat` — every accepted row's cells are naturals (`current < 2^15`, `symbol < 2`), from the
    range lookups against faithful range tables.
  * ⚑ `weld8_run_classifies` — if every row is an edge of `d`, the public final state is
    `classifyFrom d q₀ (readWord t)`: the continuity window and the two boundary pins, lifted to ℕ
    by the range bounds and PI canonicality, thread the rows into `d`'s deterministic run.
  * ⚑ `weld8_run_or_collides` — THE WHOLE-RUN COROLLARY: for a public root group committing `d`
    (`CommitsAutomaton8By S8 m (pubRoot t) d`), either the public final state is the classification
    of the word the trace reads, or some row's heap collides with the committing heap at the named
    pair (`MapRootColl`, floor-free).
  * `weld8_run_accepts_or_collides` — from `d.start` to `d.accepts`: if `pi[initial] = d.start` and
    `pi[final]` is accepting, the word's run is an accepting run of `d`, or the named collision.

## The word is not bound (falsifier, §3, kernel-checked)

The PIs are `(initial, final, root₀..root₇)`: the AUTOMATON is committed, the word is not. At the toy
chip, the runs of the constant-zero automaton on `[0, 1]` and on `[1, 0]` both satisfy
`Satisfied2Lanes8` with the SAME public inputs (`pubs_equal`) and both meet the classification
(`both_classify`); `word_not_public` and `bound_shape_fails`: no function of the public inputs is the
read word, and no commitment under an injective scheme is opened by both. The content-bound
statement `∃ w, commit w = c ∧ run accepts w ∧ traceWord = w` is therefore NOT available for this
family.

## Content binding requires a full-width route

The legacy descriptor audited here has no route or length public inputs. Its successor must bind
all eight root lanes as the route seed and publish all eight final route lanes plus the length.
A scalar entry/fold chain would reintroduce a scalar collision-security bottleneck. The approved
shared decorator appends eight accumulator columns, eight output columns and an index; each row
absorbs domain, index, current, symbol, next, accumulator8 and three zero pads in one arity-16
chip lookup. This file's legacy falsifiers remain controls for that separate shape.

## NOT claimed
  * The denotation is Lanes8's DENSE model (its header): not the deployed padded-IMT root.
  * The collision disjunct names the fixed `RowHeaps` family's heap at an actually bad edge,
    preserving sortedness, length, public root and exact key/value opening. Accepted traces have
    such families (`rowHeaps_nonempty`); packaging them uses choice, not an executable extractor.
    The residual is false on the honest run even for a constant chip (`T1_no_row_collision`).
  * `hdstep : ∀ s y, d.step s y < ASTATES` (the committed automaton's targets are in range) and the
    canonicality of `pi[initial]`, `pi[final]` are hypotheses.

## Axiom hygiene
`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.AttestedAutomatonLanes8

namespace Dregg2.Circuit.Emit.AttestedAutomatonBound

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv VmRange siteHoldsAll)
open Dregg2.Crypto
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Substrate
open Dregg2.Circuit.DeployedCapTree (Digest8)
open Dregg2.Circuit.DeployedHeapTree (Heap8Scheme)
open Dregg2.Circuit.MapMerkleRoot (mapRoot8 MapRootColl zeroDigest8)
open Dregg2.Crypto.DfaAcceptanceAir (TableDfa Row classifyFrom symbols Continuous
  lastNext_eq_classifyFrom)
open Dregg2.Circuit.Emit.DfaRoutingTableEmit
  (CURRENT SYMBOL NEXT PI_INITIAL PI_FINAL envAt_loc envAt_nxt contWindowBody cont_eq
   ofNat_eq_of_modEq)
open Dregg2.Circuit.Emit.AttestedAutomatonEmit (ASYM ASTATES keyOf attContinuity attB1 attB2)
open Dregg2.Circuit.Emit.AttestedAutomatonWeld8
open Dregg2.Circuit.Emit.AttestedAutomatonLanes8

set_option autoImplicit false

/-- The word a trace reads. -/
def readWord (t : VmTrace) : List ℕ := t.rows.map fun a => (a SYMBOL).toNat

/-- A row read as a model row over naturals. -/
def mkRowN (a : Assignment) : Row ℕ ℕ ℤ :=
  { state := (a CURRENT).toNat, sym := (a SYMBOL).toNat, next := (a NEXT).toNat
  , entryHash := 0, running := 0 }

section Run
variable {S8 : Heap8Scheme} {hash : List ℤ → ℤ} {name : String} {minit : ℤ → ℤ}
  {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- Every accepted row's `current` and `symbol` are naturals below `2^15` and `2`. -/
theorem row_nat (h : Satisfied2Lanes8 S8 hash (weldDesc name) minit mfin maddrs t)
    (htf : WeldRangeTablesFaithful t.tf) {i : Nat} (hi : i < t.rows.length) :
    (t.rows[i]'hi) CURRENT = Int.ofNat ((t.rows[i]'hi) CURRENT).toNat ∧
      ((t.rows[i]'hi) CURRENT).toNat < ASTATES ∧
    (t.rows[i]'hi) SYMBOL = Int.ofNat ((t.rows[i]'hi) SYMBOL).toNat ∧
      ((t.rows[i]'hi) SYMBOL).toNat < ASYM := by
  obtain ⟨⟨c0, c1⟩, ⟨s0, s1⟩⟩ := lanes8_row_bounded S8 hash name minit mfin maddrs t h htf i hi
  rw [envAt_loc hi] at c0 c1 s0 s1
  refine ⟨by simp [Int.toNat_of_nonneg c0], ?_, by simp [Int.toNat_of_nonneg s0], ?_⟩
  · simp only [ASTATES]; norm_num at c1; omega
  · simp only [ASYM]; norm_num at s1; omega

/-- ⚑ **`weld8_run_classifies`** — every row an edge of `d` ⇒ the public final state is the
classification of the read word from the public initial state. -/
theorem weld8_run_classifies (h : Satisfied2Lanes8 S8 hash (weldDesc name) minit mfin maddrs t)
    (htf : WeldRangeTablesFaithful t.tf) (hne : t.rows ≠ [])
    (d : TableDfa Nat Nat) (hdstep : ∀ s y, d.step s y < ASTATES)
    (hhon : ∀ i (hi : i < t.rows.length), (t.rows[i]'hi) NEXT
      = Int.ofNat (d.step ((t.rows[i]'hi) CURRENT).toNat ((t.rows[i]'hi) SYMBOL).toNat))
    (q0 : ℕ) (hq0 : q0 < 2013265921) (hpi : t.pub PI_INITIAL = Int.ofNat q0)
    (fN : ℕ) (hfN : fN < 2013265921) (hpf : t.pub PI_FINAL = Int.ofNat fN) :
    fN = classifyFrom d q0 (readWord t) := by
  have hpos : 0 < t.rows.length := List.length_pos_of_ne_nil hne
  have hlt : t.rows.length - 1 < t.rows.length := Nat.sub_lt hpos Nat.one_pos
  have hAst : ASTATES < 2013265921 := by decide
  -- model rows
  have htable : ∀ r ∈ t.rows.map mkRowN, r.next = d.step r.state r.sym := by
    intro r hr
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    simp only [mkRowN, hhon i hi]
    rfl
  have hcont : Continuous (t.rows.map mkRowN) := by
    have key : ∀ (l : List Assignment),
        (∀ i (_ : i + 1 < l.length), ((l[i + 1]) CURRENT).toNat = ((l[i]) NEXT).toNat) →
        Continuous (l.map mkRowN) := by
      intro l
      induction l with
      | nil => intro _; trivial
      | cons a rest ih =>
        intro hc
        cases rest with
        | nil => trivial
        | cons b bs =>
          refine ⟨?_, ih (fun i hi => ?_)⟩
          · have := hc 0 (by simp); simpa [mkRowN] using this
          · have := hc (i + 1) (by simp only [List.length_cons] at hi ⊢; omega); simpa using this
    apply key
    intro i hi1
    have hi : i < t.rows.length := Nat.lt_of_succ_lt hi1
    have hc := h.rowConstraints i hi attContinuity (weldCont_mem name)
    have hwin : WindowConstraint.holdsAt (envAt t i) (i + 1 == t.rows.length)
        ⟨contWindowBody, true⟩ := hc
    simp only [WindowConstraint.holdsAt, if_true] at hwin
    have hw := hwin (by simpa using Nat.ne_of_lt hi1)
    obtain ⟨hc1, hb1, _, _⟩ := row_nat h htf hi1
    have hx : (envAt t i).nxt CURRENT = Int.ofNat ((t.rows[i + 1]'hi1) CURRENT).toNat := by
      rw [envAt_nxt hi1]; exact hc1
    have hy : (envAt t i).loc NEXT = Int.ofNat
        (d.step ((t.rows[i]'hi) CURRENT).toNat ((t.rows[i]'hi) SYMBOL).toNat) := by
      rw [envAt_loc hi]; exact hhon i hi
    have hst := hdstep ((t.rows[i]'hi) CURRENT).toNat ((t.rows[i]'hi) SYMBOL).toNat
    have heq := cont_eq hw hx hy (by omega) (by omega)
    rw [heq, hhon i hi]; rfl
  have hhead : ∀ r₀, (t.rows.map mkRowN).head? = some r₀ → r₀.state = q0 := by
    intro r₀ h₀
    simp only [List.head?_map, Option.map_eq_some_iff] at h₀
    obtain ⟨a, hah, rfl⟩ := h₀
    have h0 : t.rows[0]'hpos = a := by
      rw [List.head?_eq_some_head hne] at hah
      rw [← Option.some.inj hah, List.head_eq_getElem hne]
    have hc := h.rowConstraints 0 hpos attB1 (weldB1_mem name)
    have hpin : (0 == 0) = true → (envAt t 0).loc CURRENT
        ≡ (envAt t 0).pub PI_INITIAL [ZMOD 2013265921] := hc
    have hm := hpin rfl
    obtain ⟨hc0, hb0, _, _⟩ := row_nat h htf hpos
    rw [envAt_loc hpos, hc0] at hm
    have : ((t.rows[0]'hpos) CURRENT).toNat = q0 :=
      ofNat_eq_of_modEq (by omega) hq0 (by simpa [envAt, hpi] using hm)
    rw [← h0]; exact this
  have hlast? : (t.rows.map mkRowN).getLast? = some (mkRowN (t.rows.getLast hne)) := by
    rw [List.getLast?_map, List.getLast?_eq_some_getLast hne]; rfl
  have hcl := lastNext_eq_classifyFrom d q0 (t.rows.map mkRowN) htable hcont hhead _ hlast?
  have hsyms : symbols (t.rows.map mkRowN) = readWord t := by
    simp [symbols, readWord, mkRowN, Function.comp_def]
  rw [hsyms] at hcl
  -- the final pin
  have hc := h.rowConstraints (t.rows.length - 1) hlt attB2 (weldB2_mem name)
  have hlast : (t.rows.length - 1 + 1 == t.rows.length) = true := by
    rw [Nat.sub_add_cancel hpos]; exact beq_self_eq_true _
  have hpin : (t.rows.length - 1 + 1 == t.rows.length) = true → (envAt t (t.rows.length - 1)).loc NEXT
      ≡ (envAt t (t.rows.length - 1)).pub PI_FINAL [ZMOD 2013265921] := hc
  have hm := hpin hlast
  rw [envAt_loc hlt, hhon _ hlt] at hm
  have hfe : d.step ((t.rows[t.rows.length - 1]'hlt) CURRENT).toNat
      ((t.rows[t.rows.length - 1]'hlt) SYMBOL).toNat = fN :=
    ofNat_eq_of_modEq (by
      have := hdstep ((t.rows[t.rows.length - 1]'hlt) CURRENT).toNat
        ((t.rows[t.rows.length - 1]'hlt) SYMBOL).toNat
      omega) hfN (by simpa [envAt, hpf] using hm)
  rw [← hfe, ← hcl]
  show d.step _ _ = ((t.rows.getLast hne) NEXT).toNat
  rw [List.getLast_eq_getElem hne, hhon _ hlt]
  rfl

/-- Explicit opening witnesses indexed by the actual trace row. Supplying this family fixes
which heap the collision extractor examines; an unrelated preimage cannot substitute. -/
structure RowHeaps (S8 : Heap8Scheme) (t : VmTrace) where
  heap : Fin t.rows.length → Heap.FeltHeap
  sorted : ∀ i, Heap.SortedKeys (heap i)
  length : ∀ i, (heap i).length = 2 ^ MAP_TREE_DEPTH
  root : ∀ i, mapRoot8 S8 MAP_TREE_DEPTH (heap i) = pubRoot t
  opening : ∀ i, Heap.get (heap i)
    (2 * (t.rows[i]) CURRENT + (t.rows[i]) SYMBOL) = some ((t.rows[i]) NEXT)

/-- Acceptance supplies an opening family. Choice packages the existing witnesses; it does not
claim that existential denotation implements a computational heap extractor. -/
theorem rowHeaps_nonempty
    (h : Satisfied2Lanes8 S8 hash (weldDesc name) minit mfin maddrs t)
    (hcan : LaneCanonical t) : Nonempty (RowHeaps S8 t) := by
  classical
  have hopen := fun i : Fin t.rows.length =>
    lanes8_row_opens_public S8 hash name minit mfin maddrs t h hcan i i.isLt
  choose heap hs hl hr hg using hopen
  exact ⟨⟨heap, hs, hl, hr, fun i => by simpa only [envAt_loc i.isLt] using hg i⟩⟩

/-- The bad edge and collision use the SAME row's supplied heap, retaining every opening fact. -/
def RowCollision (S8 : Heap8Scheme) (t : VmTrace) (d : TableDfa Nat Nat)
    (openings : RowHeaps S8 t) (m : Heap.FeltHeap) : Prop :=
  ∃ i : Fin t.rows.length,
    (t.rows[i]) NEXT ≠ Int.ofNat (d.step ((t.rows[i]) CURRENT).toNat ((t.rows[i]) SYMBOL).toNat) ∧
    Heap.SortedKeys (openings.heap i) ∧
    (openings.heap i).length = 2 ^ MAP_TREE_DEPTH ∧
    mapRoot8 S8 MAP_TREE_DEPTH (openings.heap i) = pubRoot t ∧
    Heap.get (openings.heap i) (2 * (t.rows[i]) CURRENT + (t.rows[i]) SYMBOL)
      = some ((t.rows[i]) NEXT) ∧
    MapRootColl S8 MAP_TREE_DEPTH (openings.heap i) m

/-- Whole-run classification or a collision on a specific bad row's explicit opening heap. -/
theorem weld8_run_or_collides (h : Satisfied2Lanes8 S8 hash (weldDesc name) minit mfin maddrs t)
    (openings : RowHeaps S8 t) (htf : WeldRangeTablesFaithful t.tf) (hne : t.rows ≠ [])
    (d : TableDfa Nat Nat) (hdstep : ∀ s y, d.step s y < ASTATES)
    {m : Heap.FeltHeap} (hd : CommitsAutomaton8By S8 m (pubRoot t) d)
    (q0 : ℕ) (hq0 : q0 < 2013265921) (hpi : t.pub PI_INITIAL = Int.ofNat q0)
    (fN : ℕ) (hfN : fN < 2013265921) (hpf : t.pub PI_FINAL = Int.ofNat fN) :
    fN = classifyFrom d q0 (readWord t) ∨
      RowCollision S8 t d openings m := by
  by_cases hhon : ∀ i (hi : i < t.rows.length), (t.rows[i]'hi) NEXT
      = Int.ofNat (d.step ((t.rows[i]'hi) CURRENT).toNat ((t.rows[i]'hi) SYMBOL).toNat)
  · exact Or.inl (weld8_run_classifies h htf hne d hdstep hhon q0 hq0 hpi fN hfN hpf)
  · right
    push Not at hhon
    obtain ⟨i, hi, hbad⟩ := hhon
    obtain ⟨hc0, hb0, hs0, hb1⟩ := row_nat h htf hi
    let j : Fin t.rows.length := ⟨i, hi⟩
    refine ⟨j, hbad, openings.sorted j, openings.length j, openings.root j,
      openings.opening j, ?_⟩
    rcases Dregg2.Circuit.MapMerkleRoot.mapRoot8_binds_or_collides S8 MAP_TREE_DEPTH
        (openings.length j) hd.2.1 ((openings.root j).trans hd.2.2.1.symm) with heq | hc
    · exfalso
      have hg := openings.opening j
      rw [heq] at hg
      have hkey : 2 * (t.rows[i]'hi) CURRENT + (t.rows[i]'hi) SYMBOL =
          ((keyOf ((t.rows[i]'hi) CURRENT).toNat ((t.rows[i]'hi) SYMBOL).toNat : ℕ) : ℤ) := by
        rw [hc0, hs0]
        simp [keyOf]
      change Heap.get m (2 * (t.rows[i]'hi) CURRENT + (t.rows[i]'hi) SYMBOL) =
        some ((t.rows[i]'hi) NEXT) at hg
      rw [hkey, hd.2.2.2 _ _ hb0 hb1] at hg
      exact hbad (Option.some.inj hg.symm)
    · exact hc

/-- ⚑ **`weld8_run_accepts_or_collides`** — from `d.start` to `d.accepts`: an accepting public final
state means the read word's run of the committed automaton accepts, or the named collision. -/
theorem weld8_run_accepts_or_collides
    (h : Satisfied2Lanes8 S8 hash (weldDesc name) minit mfin maddrs t)
    (openings : RowHeaps S8 t) (htf : WeldRangeTablesFaithful t.tf) (hne : t.rows ≠ [])
    (d : TableDfa Nat Nat) (hdstep : ∀ s y, d.step s y < ASTATES)
    {m : Heap.FeltHeap} (hd : CommitsAutomaton8By S8 m (pubRoot t) d)
    (hst : d.start < 2013265921) (hpi : t.pub PI_INITIAL = Int.ofNat d.start)
    (fN : ℕ) (hfN : fN < 2013265921) (hpf : t.pub PI_FINAL = Int.ofNat fN) (hacc : d.accepts fN) :
    d.accepts (Dregg2.Crypto.DfaAcceptanceAir.classify d (readWord t)) ∨
      RowCollision S8 t d openings m := by
  rcases weld8_run_or_collides h openings htf hne d hdstep hd d.start hst hpi fN hfN hpf with he | hc
  · left
    show d.accepts (classifyFrom d d.start (readWord t))
    rw [← he]; exact hacc
  · exact Or.inr hc

end Run

/-! ## §2 — Non-vacuity: the chaining fires on the constructed witness. -/

/-- The constant-zero automaton (every edge goes to state `0`, `0` accepts). -/
def zeroD : TableDfa Nat Nat := ⟨fun _ _ => 0, 0, fun s => s = 0⟩

def T1 : VmTrace := weldWit8 zeroD zeroDigest8 0 [0, 1]
def T2 : VmTrace := weldWit8 zeroD zeroDigest8 0 [1, 0]

theorem zeroD_step : ∀ s y, zeroD.step s y < ASTATES := fun _ _ => show 0 < ASTATES by decide

theorem T_satisfies (hash : List ℤ → ℤ) (name : String) (w : List ℕ) (hw : w ≠ [])
    (hsym : ∀ y ∈ w, y < ASYM) :
    Satisfied2Lanes8 constChip hash (weldDesc name) (fun _ => 0) (fun _ => (0, 0)) []
      (weldWit8 zeroD zeroDigest8 0 w) :=
  (lanes8_constChip_iff hash zeroD zeroDigest8 zeroD_step 0 (by decide) w hw hsym name).mpr rfl

theorem T1_satisfies (hash : List ℤ → ℤ) (name : String) :
    Satisfied2Lanes8 constChip hash (weldDesc name) (fun _ => 0) (fun _ => (0, 0)) [] T1 :=
  T_satisfies hash name _ (by simp) (by decide)
theorem T2_satisfies (hash : List ℤ → ℤ) (name : String) :
    Satisfied2Lanes8 constChip hash (weldDesc name) (fun _ => 0) (fun _ => (0, 0)) [] T2 :=
  T_satisfies hash name _ (by simp) (by decide)

theorem T1_word : readWord T1 = [0, 1] := rfl
theorem T2_word : readWord T2 = [1, 0] := rfl

/-- The two traces publish the SAME public inputs (initial `0`, final `0`, the zero root group). -/
theorem pubs_equal : T1.pub = T2.pub := rfl

theorem T1_honest : ∀ i (hi : i < T1.rows.length), (T1.rows[i]'hi) NEXT
    = Int.ofNat (zeroD.step ((T1.rows[i]'hi) CURRENT).toNat ((T1.rows[i]'hi) SYMBOL).toNat) := by
  intro i hi
  have hi2 : i < 2 := hi
  interval_cases i <;> rfl

theorem T2_honest : ∀ i (hi : i < T2.rows.length), (T2.rows[i]'hi) NEXT
    = Int.ofNat (zeroD.step ((T2.rows[i]'hi) CURRENT).toNat ((T2.rows[i]'hi) SYMBOL).toNat) := by
  intro i hi
  have hi2 : i < 2 := hi
  interval_cases i <;> rfl

theorem T_tf (w : List ℕ) : WeldRangeTablesFaithful (weldWit8 zeroD zeroDigest8 0 w).tf :=
  attTf8_faithful _

/-- The explicit opening-family hypothesis is inhabited by the same accepted witness. -/
theorem T1_openings_nonempty (hash : List ℤ → ℤ) (name : String) :
    Nonempty (RowHeaps constChip T1) :=
  rowHeaps_nonempty (T1_satisfies hash name)
    (weldWit8_laneCanonical zeroD zeroDigest8
      (fun _ => ⟨(by decide : (0 : ℤ) ≤ 0), (by decide : (0 : ℤ) < 2013265921)⟩) 0 [0, 1])

/-- The residual is false on the honest run even under a constant (maximally colliding) chip.
An unrelated heap collision therefore cannot satisfy it. No collision-resistance premise occurs. -/
theorem T1_no_row_collision (openings : RowHeaps constChip T1) (m : Heap.FeltHeap) :
    ¬ RowCollision constChip T1 zeroD openings m := by
  rintro ⟨i, hbad, _⟩
  exact hbad (T1_honest i i.isLt)

/-- ⚑ Both runs MEET the whole-run classification (the chaining corollary fires). -/
theorem both_classify (hash : List ℤ → ℤ) (name : String) :
    (0 : ℕ) = classifyFrom zeroD 0 (readWord T1) ∧ (0 : ℕ) = classifyFrom zeroD 0 (readWord T2) :=
  ⟨weld8_run_classifies (T1_satisfies hash name) (T_tf _) (by simp [T1, weldWit8, rowsW])
      zeroD zeroD_step T1_honest 0 (by decide) rfl 0 (by decide) rfl,
   weld8_run_classifies (T2_satisfies hash name) (T_tf _) (by simp [T2, weldWit8, rowsW])
      zeroD zeroD_step T2_honest 0 (by decide) rfl 0 (by decide) rfl⟩

/-- The whole-run corollary's hypotheses are jointly inhabited on `T1` (the public root group
commits `zeroD` at the toy chip), and its conclusion holds. -/
theorem T1_run_or_collides (hash : List ℤ → ℤ) (name : String)
    (openings : RowHeaps constChip T1) :
    (0 : ℕ) = classifyFrom zeroD 0 (readWord T1) ∨
      RowCollision constChip T1 zeroD openings (autoHeapW zeroD) := by
  have hpub : pubRoot T1 = zeroDigest8 := by
    funext l
    show weldPub 0 (classifyFrom zeroD 0 [0, 1]) zeroDigest8 (PI_W8ROOT l) = zeroDigest8 l
    rw [weldPub_root]
  have hd : CommitsAutomaton8By constChip (autoHeapW zeroD) (pubRoot T1) zeroD := by
    rw [hpub, ← autoRoot8_constChip zeroD]
    exact autoRoot8_commits constChip zeroD
  exact weld8_run_or_collides (T1_satisfies hash name)
    openings (T_tf _) (by simp [T1, weldWit8, rowsW]) zeroD zeroD_step hd 0 (by decide) rfl 0 (by decide) rfl

/-! ## §3 — The falsifier: one public statement, two words. -/

/-- ⚑ **`word_not_public`** — no function of the public inputs is the read word. -/
theorem word_not_public (hash : List ℤ → ℤ) (name : String) :
    ¬ ∃ f : Assignment → List ℕ, ∀ t : VmTrace,
      Satisfied2Lanes8 constChip hash (weldDesc name) (fun _ => 0) (fun _ => (0, 0)) [] t →
        readWord t = f t.pub := by
  rintro ⟨f, hf⟩
  have h1 := hf T1 (T1_satisfies hash name)
  have h2 := hf T2 (T2_satisfies hash name)
  rw [T1_word] at h1
  rw [T2_word, ← pubs_equal, ← h1] at h2
  exact absurd h2 (by decide)

/-- ⚑ **`bound_shape_fails`** — for an injective content scheme, no commitment is opened by the
words of both satisfying traces of one public statement. -/
theorem bound_shape_fails (hash : List ℤ → ℤ) (name : String) {D : Type}
    (commit : List ℕ → D) (hinj : Function.Injective commit) :
    ¬ ∃ c : D, ∀ t : VmTrace,
      Satisfied2Lanes8 constChip hash (weldDesc name) (fun _ => 0) (fun _ => (0, 0)) [] t →
        t.pub = T1.pub → commit (readWord t) = c := by
  rintro ⟨c, hc⟩
  have h := hinj ((hc T1 (T1_satisfies hash name) rfl).trans
    (hc T2 (T2_satisfies hash name) pubs_equal.symm).symm)
  rw [T1_word, T2_word] at h
  exact absurd h (by decide)

/-! ## §4 — axiom tripwires. -/

/-- info: 'Dregg2.Circuit.Emit.AttestedAutomatonBound.weld8_run_or_collides' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms weld8_run_or_collides

/-- info: 'Dregg2.Circuit.Emit.AttestedAutomatonBound.T1_no_row_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms T1_no_row_collision

#assert_all_clean [rowHeaps_nonempty, row_nat, weld8_run_classifies, weld8_run_or_collides,
  weld8_run_accepts_or_collides, zeroD_step, T_satisfies, T1_satisfies, T2_satisfies, T1_word,
  T2_word, pubs_equal, T1_honest, T2_honest, T1_openings_nonempty, T1_no_row_collision, T_tf, both_classify, T1_run_or_collides, word_not_public,
  bound_shape_fails]

end Dregg2.Circuit.Emit.AttestedAutomatonBound
