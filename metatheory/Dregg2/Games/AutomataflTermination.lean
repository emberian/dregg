/-
# AutomataflTermination — M3 of the multi-round conflict braid: THE TERMINATION BOUND

⚑ SUBSTRATE. This file is **pure spec-side Lean**: it reasons about
`Dregg2.Games.AutomataflRules.roundStep` / `runTurn` and nothing else. It authors **no AIR, no
gadget, no constraint** — the Leg C descriptor (M1/M2) is Lean-authored AIR living under
`Dregg2.Circuit.Emit.Automatafl*`, and this file is the SPEC-side half its refinement theorem
will be pushed through. Nothing here is Rust and nothing here should become Rust.

## What this closes (design doc §5, `docs/reference/AUTOMATAFL-MULTIROUND-BRAID-DESIGN.md`)

The conflict re-entry protocol RECURSES: a clash marks the conflicted coordinate(s), the
conflicted seats re-enter, repeat until clean. For the braid fold (M7) to be a fixed-depth
verifiable object, the recursion needs a **bound**. The argument:

1. **marks strictly grows on every clash round.** `roundStep`'s `.again` branch sets
   `marks := (marks ++ cs).dedup` with `cs ≠ []`, and `cs ∩ marks = ∅` because
   * `cs ⊆ candidates all` — the conflicted coordinates are move ENDPOINTS. For the
     fork/collide clash this is immediate (`clashCoords` filters `candidates`); for the
     MERGE/confluence clash it is `unresolved_subset_candidates` below, which is the real
     content: a contested LANDING square is reached by walking `edgeMap` edges, and every
     edge's head is some move's `.to` (`stopWalk_mem`). So the merge case is **PROVEN, not
     scoped**.
   * every move in `all = locked ++ fresh` is `marks`-legal — `fresh` by `roundStep`'s own
     `moveLegalB rs.board rs.marks` filter, `locked` by the `RoundWF` invariant, which
     `roundStep` re-establishes because it DROPS every locked move a new mark touches.
2. **marks ⊆ the `n²` board coordinates**, since every mark is an endpoint of a legal (hence
   in-bounds) move. So `|marks| ≤ n²`.
3. Hence a turn takes at most `n² − |marks|` clash rounds (`againDepth_le`), and `runTurn`
   fed a trace of length `> n²` ALWAYS reaches a `.resolved` outcome (`runTurn_fuel_bound`).

**There is no stuck state.** `runTurn` returns `none` for exactly one reason: the submission
trace ran out while the turn was still awaiting re-entry. `roundStep` is total and always
returns `.again` or `.resolved` — even a round in which every submission is illegal is not
stuck, it is CLEAN (`fresh = []`, `all = locked`), and a round with no moves at all resolves
trivially (`clashCoords [] = []`, `unresolved [] = []`). So "out of fuel" is a statement about
the TRACE the prover supplies, never about the game wedging.

## What M7 (the braid fold) consumes

```lean
theorem againDepth_le (cfg : GameConfig) (g : GoalAssignment) (rs : RoundState)
    (trace : List (List Move)) (hwf : RoundWF rs) :
    againDepth cfg g rs trace + rs.marks.length ≤ rs.board.size * rs.board.size
```

— the number of Leg C leaves in a turn's braid, bounded by `n²` (121 at n=11), with the
`openRound` corollary `againDepth_le_openRound : againDepth … ≤ b.size * b.size`.
-/
import Dregg2.Games.AutomataflRules
import Mathlib.Data.List.Perm.Subperm

namespace Dregg2.Games.AutomataflRules

open Dregg2.Games.Automatafl

set_option autoImplicit false

/-! ## §1  The board coordinate enumeration — the `n²` ceiling -/

/-- Every coordinate of an `n × n` board. -/
def boardCoords (n : Nat) : List Coord :=
  (List.range n).flatMap (fun x => (List.range n).map (fun y => ⟨x, y⟩))

theorem mem_boardCoords {n : Nat} {c : Coord} : c ∈ boardCoords n ↔ c.x < n ∧ c.y < n := by
  unfold boardCoords
  constructor
  · intro h
    obtain ⟨x, hx, hmem⟩ := List.mem_flatMap.mp h
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hmem
    exact ⟨List.mem_range.mp hx, List.mem_range.mp hy⟩
  · intro ⟨hx, hy⟩
    refine List.mem_flatMap.mpr ⟨c.x, List.mem_range.mpr hx, ?_⟩
    exact List.mem_map.mpr ⟨c.y, List.mem_range.mpr hy, rfl⟩

theorem length_boardCoords (n : Nat) : (boardCoords n).length = n * n := by
  unfold boardCoords
  simp [List.length_flatMap]

/-- A `Nodup` list of in-bounds coordinates is no longer than the board. -/
theorem length_le_of_inBounds {b : Board} {l : List Coord}
    (hnd : l.Nodup) (hin : ∀ c ∈ l, b.inBounds c) : l.length ≤ b.size * b.size := by
  have hsub : l ⊆ boardCoords b.size := by
    intro c hc
    exact mem_boardCoords.mpr (hin c hc)
  have := (List.subperm_of_subset hnd hsub).length_le
  rwa [length_boardCoords] at this

/-! ## §2  The conflicted coordinates are MOVE ENDPOINTS

Both clash clauses land inside `candidates ms`. The fork/collide clause is immediate;
the merge/confluence clause (`unresolved`) is the work — a contested landing is reached by
walking the move graph, and every edge head is some move's destination. -/

/-- `allEqOpt` returns a member of its list. -/
theorem allEqOpt_mem {l : List Coord} {d : Coord} (h : allEqOpt l = some d) : d ∈ l := by
  cases l with
  | nil => simp [allEqOpt] at h
  | cons x xs =>
    simp only [allEqOpt, List.head?_cons] at h
    split at h
    · cases h; exact List.mem_cons_self
    · exact absurd h (by simp)

/-- Every edge of the move graph points at some move's DESTINATION. -/
theorem edgeMap_mem_to {b : Board} {ms : List Move} {c e : Coord}
    (h : edgeMap b ms c = some e) : e ∈ ms.map (·.to) := by
  unfold edgeMap edgeOf at h
  have hmem := allEqOpt_mem h
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hmem
  exact List.mem_map.mpr ⟨m, List.mem_of_mem_filter hm, rfl⟩

/-- The forward walk stops either where it started or on some move's destination. -/
theorem stopWalk_mem {b : Board} {ms : List Move} :
    ∀ (f : Nat) {c d : Coord},
      stopWalk (edgeMap b ms) (carAt b) f c = some d → d = c ∨ d ∈ ms.map (·.to) := by
  intro f
  induction f with
  | zero => intro c d h; simp [stopWalk] at h
  | succ f ih =>
    intro c d h
    simp only [stopWalk] at h
    split at h
    · simp only [Option.some.injEq] at h; exact Or.inl h.symm
    · rename_i e he
      have hemem : e ∈ ms.map (·.to) := edgeMap_mem_to he
      split at h
      · simp only [Option.some.injEq] at h
        exact Or.inr (h ▸ hemem)
      · rcases ih h with h1 | h2
        · exact Or.inr (h1 ▸ hemem)
        · exact Or.inr h2

/-- A landing square of a candidate coordinate is itself a candidate coordinate. -/
theorem landMap_mem_candidates {b : Board} {ms : List Move} {c : Coord}
    (hc : c ∈ candidates ms) : landMap b ms c ∈ candidates ms := by
  unfold landMap landOf
  split
  · cases hs : stopWalk (edgeMap b ms) (carAt b) (ms.length + 1) c with
    | none => simpa using hc
    | some d =>
      simp only [Option.getD_some]
      rcases stopWalk_mem _ hs with h | h
      · exact h ▸ hc
      · exact List.mem_append_right _ h
  · exact hc

/-- **The fork/collide clash coordinates are move endpoints.** -/
theorem clashCoords_subset_candidates (b : Board) (ms : List Move) :
    ∀ c ∈ clashCoords b ms, c ∈ candidates ms := by
  intro c hc
  unfold clashCoords at hc
  exact List.mem_of_mem_filter (List.mem_dedup.mp hc)

/-- **The MERGE/confluence clash coordinates are move endpoints too** — this is the step the
design doc flagged as owed (§5.2, §9.1). A contested landing is `landMap` of a mover, a mover
is some move's source, and `landMap` never leaves `candidates`. -/
theorem unresolved_subset_candidates (b : Board) (ms : List Move) :
    ∀ c ∈ unresolved b ms, c ∈ candidates ms := by
  intro c hc
  unfold unresolved at hc
  obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp (List.mem_dedup.mp hc)
  have hmov : c₀ ∈ movers b ms := List.mem_of_mem_filter hc₀
  have hfrm : c₀ ∈ ms.map (·.frm) := by
    unfold movers moverList at hmov
    exact List.mem_dedup.mp (List.mem_of_mem_filter hmov)
  exact landMap_mem_candidates (List.mem_append_left _ hfrm)

/-! ## §3  The round, decomposed

`roundStep`'s `let`s are zeta-transparent, so these definitions are DEFINITIONALLY the round's
own intermediates (`roundStep_eq` is `rfl`) — no re-authoring, no mirror. -/

/-- The submissions that actually enter the round: from a waiting seat, and `marks`-legal. -/
def roundFresh (rs : RoundState) (subs : List Move) : List Move :=
  subs.filter (fun m => rs.waiting.contains m.who && moveLegalB rs.board rs.marks m)

/-- The round's full move list: the locked moves that stand, plus the fresh ones. -/
def roundAll (rs : RoundState) (subs : List Move) : List Move :=
  rs.locked ++ roundFresh rs subs

/-- The round's conflicted coordinates: fork/collide, else merge/confluence. -/
def roundCs (rs : RoundState) (subs : List Move) : List Coord :=
  if (clashCoords rs.board (roundAll rs subs)).isEmpty then
    unresolved rs.board (roundAll rs subs)
  else clashCoords rs.board (roundAll rs subs)

/-- The re-entry state a clash round produces. -/
def roundAgainState (rs : RoundState) (subs : List Move) : RoundState :=
  { board := rs.board
    marks := (rs.marks ++ roundCs rs subs).dedup
    locked := (roundAll rs subs).filter
                (fun m => !((roundCs rs subs).contains m.frm || (roundCs rs subs).contains m.to))
    waiting := (((roundAll rs subs).filter
                (fun m => (roundCs rs subs).contains m.frm || (roundCs rs subs).contains m.to)).map
                (·.who)).dedup }

theorem roundStep_eq (cfg : GameConfig) (g : GoalAssignment) (rs : RoundState)
    (subs : List Move) :
    roundStep cfg g rs subs =
      if (roundCs rs subs).isEmpty then
        (let mid := resolveMoves rs.board (roundAll rs subs)
         let after := automatonStepCfg cfg mid
         .resolved after (winOnEntry mid after g))
      else .again (roundAgainState rs subs) := rfl

/-- A round that re-enters produced EXACTLY `roundAgainState`, on a genuinely nonempty `cs`. -/
theorem roundStep_again_inv {cfg : GameConfig} {g : GoalAssignment} {rs rs' : RoundState}
    {subs : List Move} (h : roundStep cfg g rs subs = .again rs') :
    rs' = roundAgainState rs subs ∧ roundCs rs subs ≠ [] := by
  rw [roundStep_eq] at h
  split at h
  · exact absurd h (by simp)
  · rename_i hne
    refine ⟨by injection h with h; exact h.symm, ?_⟩
    intro hnil
    exact hne (by simp [hnil])

/-! ## §4  The RoundState invariant

`roundStep` filters FRESH submissions for `marks`-legality but takes LOCKED moves on faith —
they were legal when they were submitted. The invariant that makes that faith true is that
`roundStep` DROPS every locked move a newly-marked coordinate touches. -/

/-- A well-formed mid-turn state: `marks` is duplicate-free and on the board, and every locked
move is legal against the CURRENT marks. -/
structure RoundWF (rs : RoundState) : Prop where
  marksNodup : rs.marks.Nodup
  marksInBounds : ∀ c ∈ rs.marks, rs.board.inBounds c
  lockedLegal : ∀ m ∈ rs.locked, MoveLegal rs.board rs.marks m

theorem roundWF_openRound (b : Board) (seats : List Pid) : RoundWF (openRound b seats) where
  marksNodup := by simp [openRound]
  marksInBounds := by simp [openRound]
  lockedLegal := by simp [openRound]

/-- Under the invariant, EVERY move of the round — locked or fresh — is `marks`-legal. -/
theorem roundAll_legal {rs : RoundState} (hwf : RoundWF rs) (subs : List Move) :
    ∀ m ∈ roundAll rs subs, MoveLegal rs.board rs.marks m := by
  intro m hm
  rcases List.mem_append.mp hm with h | h
  · exact hwf.lockedLegal m h
  · have := List.of_mem_filter h
    have hleg : moveLegalB rs.board rs.marks m = true := by
      simpa using (Bool.and_eq_true _ _ |>.mp this).2
    exact (moveLegalB_iff _ _ _).mp hleg

/-- Hence no move endpoint of the round is already marked … -/
theorem candidates_not_mem_marks {rs : RoundState} (hwf : RoundWF rs) (subs : List Move) :
    ∀ c ∈ candidates (roundAll rs subs), c ∉ rs.marks := by
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp h
    exact (roundAll_legal hwf subs m hm).2.2.2.2.2.1
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp h
    exact (roundAll_legal hwf subs m hm).2.2.2.2.2.2

/-- … and every move endpoint is in bounds. -/
theorem candidates_inBounds {rs : RoundState} (hwf : RoundWF rs) (subs : List Move) :
    ∀ c ∈ candidates (roundAll rs subs), rs.board.inBounds c := by
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp h
    exact (roundAll_legal hwf subs m hm).2.2.1
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp h
    exact (roundAll_legal hwf subs m hm).2.2.2.1

/-- **The conflicted coordinates are move endpoints — BOTH clauses.** -/
theorem roundCs_subset_candidates (rs : RoundState) (subs : List Move) :
    ∀ c ∈ roundCs rs subs, c ∈ candidates (roundAll rs subs) := by
  intro c hc
  unfold roundCs at hc
  split at hc
  · exact unresolved_subset_candidates _ _ c hc
  · exact clashCoords_subset_candidates _ _ c hc

/-- **THE DISJOINTNESS.** A newly conflicted coordinate was never already marked. -/
theorem roundCs_disjoint_marks {rs : RoundState} (hwf : RoundWF rs) (subs : List Move) :
    ∀ c ∈ roundCs rs subs, c ∉ rs.marks := fun c hc =>
  candidates_not_mem_marks hwf subs c (roundCs_subset_candidates rs subs c hc)

theorem roundCs_inBounds {rs : RoundState} (hwf : RoundWF rs) (subs : List Move) :
    ∀ c ∈ roundCs rs subs, rs.board.inBounds c := fun c hc =>
  candidates_inBounds hwf subs c (roundCs_subset_candidates rs subs c hc)

/-! ## §5  Marks strictly grow -/

/-- Adding a nonempty, disjoint block to a duplicate-free list strictly lengthens it. -/
theorem dedup_append_length_lt {marks cs : List Coord}
    (hnd : marks.Nodup) (hne : cs ≠ []) (hdisj : ∀ c ∈ cs, c ∉ marks) :
    marks.length < ((marks ++ cs).dedup).length := by
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil cs hne
  have hnd' : (c :: marks).Nodup := List.nodup_cons.mpr ⟨hdisj c hc, hnd⟩
  have hsub : (c :: marks) ⊆ (marks ++ cs).dedup := by
    intro x hx
    refine List.mem_dedup.mpr ?_
    rcases List.mem_cons.mp hx with rfl | h
    · exact List.mem_append_right _ hc
    · exact List.mem_append_left _ h
  have := (List.subperm_of_subset hnd' hsub).length_le
  simp only [List.length_cons] at this
  omega

/-- ⚑ **M3 (1): A CLASH ROUND STRICTLY GROWS `marks`.** -/
theorem roundStep_marks_strict_growth {cfg : GameConfig} {g : GoalAssignment}
    {rs rs' : RoundState} {subs : List Move} (hwf : RoundWF rs)
    (h : roundStep cfg g rs subs = .again rs') :
    rs.marks.length < rs'.marks.length := by
  obtain ⟨rfl, hne⟩ := roundStep_again_inv h
  exact dedup_append_length_lt hwf.marksNodup hne (roundCs_disjoint_marks hwf subs)

/-- The board is FROZEN across a clash round (so `n` is the same next round). -/
theorem roundStep_again_board {cfg : GameConfig} {g : GoalAssignment} {rs rs' : RoundState}
    {subs : List Move} (h : roundStep cfg g rs subs = .again rs') :
    rs'.board = rs.board := by
  obtain ⟨rfl, _⟩ := roundStep_again_inv h; rfl

/-- ⚑ **The invariant is PRESERVED** — this is what makes the growth argument inductive. -/
theorem roundStep_again_wf {cfg : GameConfig} {g : GoalAssignment} {rs rs' : RoundState}
    {subs : List Move} (hwf : RoundWF rs) (h : roundStep cfg g rs subs = .again rs') :
    RoundWF rs' := by
  obtain ⟨rfl, _⟩ := roundStep_again_inv h
  refine ⟨List.nodup_dedup _, ?_, ?_⟩
  · intro c hc
    rcases List.mem_append.mp (List.mem_dedup.mp hc) with h1 | h1
    · exact hwf.marksInBounds c h1
    · exact roundCs_inBounds hwf subs c h1
  · intro m hm
    have hmall : m ∈ roundAll rs subs := List.mem_of_mem_filter hm
    have hdrop : m.frm ∉ roundCs rs subs ∧ m.to ∉ roundCs rs subs := by
      simpa using List.of_mem_filter hm
    obtain ⟨hd1, hd2, hd3, hd4, hd5, hd6, hd7⟩ := roundAll_legal hwf subs m hmall
    refine ⟨hd1, hd2, hd3, hd4, hd5, ?_, ?_⟩
    · intro hmem
      rcases List.mem_append.mp (List.mem_dedup.mp hmem) with h1 | h1
      · exact hd6 h1
      · exact hdrop.1 h1
    · intro hmem
      rcases List.mem_append.mp (List.mem_dedup.mp hmem) with h1 | h1
      · exact hd7 h1
      · exact hdrop.2 h1

/-! ## §6  The `n²` ceiling and the fuel bound -/

/-- ⚑ **M3 (2): `marks` never exceeds the board.** -/
theorem marks_length_le_board {rs : RoundState} (hwf : RoundWF rs) :
    rs.marks.length ≤ rs.board.size * rs.board.size :=
  length_le_of_inBounds hwf.marksNodup hwf.marksInBounds

/-- ⚑ **THE DESCENDING MEASURE, literally.** `n² − |marks|` strictly decreases across every
clash round — the `termination_by` clause of the re-entry recursion. -/
theorem roundStep_measure_decreases {cfg : GameConfig} {g : GoalAssignment}
    {rs rs' : RoundState} {subs : List Move} (hwf : RoundWF rs)
    (h : roundStep cfg g rs subs = .again rs') :
    rs'.board.size * rs'.board.size - rs'.marks.length
      < rs.board.size * rs.board.size - rs.marks.length := by
  have hgrow := roundStep_marks_strict_growth hwf h
  have hle := marks_length_le_board (roundStep_again_wf hwf h)
  have hle0 := marks_length_le_board hwf
  rw [roundStep_again_board h] at hle ⊢
  omega

/-- How many `.again` (clash) rounds a submission trace actually takes before resolving. This
is the number of Leg C leaves in the turn's braid. -/
def againDepth (cfg : GameConfig) (g : GoalAssignment) (rs : RoundState) :
    List (List Move) → Nat
  | []           => 0
  | subs :: rest =>
    match roundStep cfg g rs subs with
    | .resolved _ _ => 0
    | .again rs'    => 1 + againDepth cfg g rs' rest

/-- ⚑ **M3 (3): THE FOLD-FUEL LEMMA — the braid is at most `n²` clash rounds deep.**

This is the exact statement M7 consumes: the number of Leg C leaves in one turn's braid,
bounded by the board size, uniformly in the submission trace. -/
theorem againDepth_le (cfg : GameConfig) (g : GoalAssignment) :
    ∀ (trace : List (List Move)) (rs : RoundState), RoundWF rs →
      againDepth cfg g rs trace + rs.marks.length ≤ rs.board.size * rs.board.size := by
  intro trace
  induction trace with
  | nil => intro rs hwf; simpa [againDepth] using marks_length_le_board hwf
  | cons subs rest ih =>
    intro rs hwf
    rw [againDepth]
    split
    · simpa using marks_length_le_board hwf
    · rename_i rs' hstep
      have hgrow := roundStep_marks_strict_growth hwf hstep
      have hwf' := roundStep_again_wf hwf hstep
      have hboard := roundStep_again_board hstep
      have := ih rs' hwf'
      rw [hboard] at this
      omega

/-- The `openRound` corollary: a turn opens with no marks, so its braid is at most `n²` deep
(121 at n = 11). -/
theorem againDepth_le_openRound (cfg : GameConfig) (g : GoalAssignment) (b : Board)
    (seats : List Pid) (trace : List (List Move)) :
    againDepth cfg g (openRound b seats) trace ≤ b.size * b.size := by
  have := againDepth_le cfg g trace (openRound b seats) (roundWF_openRound b seats)
  simpa [openRound] using this

/-- ⚑ **M3 (3'): `runTurn` with enough fuel ALWAYS resolves.** There is no stuck state: the
only way `runTurn` returns `none` is a trace shorter than the forced clash sequence, and that
sequence is shorter than `n² − |marks|`. -/
theorem runTurn_terminates (cfg : GameConfig) (g : GoalAssignment) :
    ∀ (trace : List (List Move)) (rs : RoundState), RoundWF rs →
      rs.board.size * rs.board.size < rs.marks.length + trace.length →
      ∃ bw, runTurn cfg g rs trace = some bw := by
  intro trace
  induction trace with
  | nil =>
    intro rs hwf hfuel
    exact absurd (marks_length_le_board hwf) (by simp at hfuel; omega)
  | cons subs rest ih =>
    intro rs hwf hfuel
    rw [runTurn]
    cases hstep : roundStep cfg g rs subs with
    | resolved b w => exact ⟨(b, w), rfl⟩
    | again rs' =>
      have hgrow := roundStep_marks_strict_growth hwf hstep
      have hwf' := roundStep_again_wf hwf hstep
      have hboard := roundStep_again_board hstep
      refine ih rs' hwf' ?_
      rw [hboard]
      simp only [List.length_cons] at hfuel
      omega

/-- ⚑ **THE FUEL CONSTANT: `n² + 1` submission rounds always suffice.** -/
theorem runTurn_fuel_bound (cfg : GameConfig) (g : GoalAssignment) (b : Board)
    (seats : List Pid) (trace : List (List Move)) (h : b.size * b.size < trace.length) :
    ∃ bw, runTurn cfg g (openRound b seats) trace = some bw :=
  runTurn_terminates cfg g trace (openRound b seats) (roundWF_openRound b seats)
    (by simpa [openRound] using h)

/-- The contrapositive, in the form the prover-side schedule wants: if a trace ran out, it was
shorter than the bound — so a trace of length `n² + 1` is enough for EVERY turn. -/
theorem runTurn_none_length_le (cfg : GameConfig) (g : GoalAssignment) (b : Board)
    (seats : List Pid) (trace : List (List Move))
    (h : runTurn cfg g (openRound b seats) trace = none) :
    trace.length ≤ b.size * b.size := by
  by_contra hlt
  obtain ⟨bw, hbw⟩ := runTurn_fuel_bound cfg g b seats trace (by omega)
  rw [h] at hbw
  exact absurd hbw (by simp)

/-! ## §7  NON-VACUITY — the theorems fire on real clash rounds

The witnesses are `AutomataflRules`' own audit boards (`d5Board` = the D4b fork witness,
`mgBoard` = the D5 merge/confluence witness), so these canaries are pinned to the same
conformance evidence the spec is. -/

section Canaries

private def cfgC : GameConfig := ⟨.column⟩
private def noG : GoalAssignment := ⟨[]⟩

/-! ### The fork/collide clash: one round, marks 0 → 1 -/

-- round 1: players 0 and 1 fork at (0,0); player 2 targets (0,0). Everyone re-enters.
private def r1state : RoundState := openRound d5Board [0, 1, 2]

#guard (roundStep cfgC noG r1state [d5A, d5B, d5C]).isAgain = true
#guard r1state.marks.length = 0
#guard (roundAgainState r1state [d5A, d5B, d5C]).marks = [(⟨0, 0⟩ : Coord)]
#guard (roundAgainState r1state [d5A, d5B, d5C]).marks.length = 1   -- STRICTLY grew

-- the disjointness is REAL, not vacuous: (0,0) was not already marked …
#guard r1state.marks.contains ⟨0, 0⟩ = false
-- … and next round it IS, so a submission naming it is filtered out of `fresh`.
private def r2state : RoundState := roundAgainState r1state [d5A, d5B, d5C]

#guard r2state.marks.contains ⟨0, 0⟩ = true
#guard roundFresh r2state [stillMarked] = ([] : List Move)   -- source still marked ⇒ dropped

/-! ### A SECOND clash round grows marks again: 1 → 2 -/

-- both re-entrants now fork on (0,4) instead.
private def f2A : Move := ⟨0, ⟨0, 4⟩, ⟨0, 2⟩⟩
private def f2B : Move := ⟨1, ⟨0, 4⟩, ⟨2, 4⟩⟩

#guard (roundStep cfgC noG r2state [f2A, f2B]).isAgain = true
#guard (roundAgainState r2state [f2A, f2B]).marks = [(⟨0, 0⟩ : Coord), ⟨0, 4⟩]
#guard (roundAgainState r2state [f2A, f2B]).marks.length = 2   -- STRICTLY grew again
-- the board is FROZEN across both clash rounds
#guard (roundAgainState r2state [f2A, f2B]).board.size = 5

/-! ### The MERGE/confluence clash — the case the design doc flagged, PROVEN above -/

-- fork/collide is silent; `unresolved` fires at the confluence square (2,0).
#guard clashCoords mgBoard [m1, m2, m3, m4] = ([] : List Coord)
#guard roundCs (openRound mgBoard [0, 1, 2, 3]) [m1, m2, m3, m4] = [(⟨2, 0⟩ : Coord)]
-- (2,0) IS a move endpoint — `unresolved_subset_candidates` is not vacuous here
#guard (candidates (roundAll (openRound mgBoard [0, 1, 2, 3]) [m1, m2, m3, m4])).contains ⟨2, 0⟩
        = true
#guard (roundAgainState (openRound mgBoard [0, 1, 2, 3]) [m1, m2, m3, m4]).marks.length = 1
-- and the merge round genuinely LOCKS the non-conflicted moves (so `lockedLegal` is loaded)
#guard (roundAgainState (openRound mgBoard [0, 1, 2, 3]) [m1, m2, m3, m4]).locked = [m1, m3]

/-! ### The depth counter agrees with the actual game, and respects the bound -/

-- one clash round, then a clean one: depth 1, and the turn resolves.
#guard againDepth cfgC noG r1state [[d5A, d5B, d5C], [reenter, stillMarked]] = 1
#guard (runTurn cfgC noG r1state [[d5A, d5B, d5C], [reenter, stillMarked]]).isSome = true
-- a clean first round: depth 0.
#guard againDepth cfgC noG (openRound forkBoard [0, 1]) [[fkA, fkSame]] = 0
-- two clash rounds: depth 2.
#guard againDepth cfgC noG r1state [[d5A, d5B, d5C], [f2A, f2B], []] = 2
-- the bound is 5·5 = 25 on these size-5 witnesses, and the depths obey it.
#guard d5Board.size * d5Board.size = 25
#guard againDepth cfgC noG r1state [[d5A, d5B, d5C], [f2A, f2B], []] ≤ 25

-- the CEILING is real: `boardCoords` counts n² coordinates (121 at the deployed n = 11).
#guard (boardCoords 11).length = 121
#guard (boardCoords 5).length = 25

/-! ### ⚑ MUTATION CANARY — `RoundWF` is LOAD-BEARING, not decoration

Drop the invariant (hand the round a LOCKED move whose endpoint is ALREADY marked — exactly
what `roundStep` prevents by dropping newly-conflicted locked moves) and the conclusion of
`roundStep_marks_strict_growth` becomes FALSE: the round still re-enters, but `cs` is a
coordinate that was already in `marks`, so `(marks ++ cs).dedup` has the SAME length and the
measure `n² − |marks|` does not descend. -/

private def illFormed : RoundState :=
  { board := d5Board, marks := [⟨0, 0⟩], locked := [d5A, d5B], waiting := [] }

-- d5A and d5B both source the ALREADY-MARKED square (0,0): `RoundWF.lockedLegal` is violated.
#guard (moveLegalB illFormed.board illFormed.marks d5A) = false
#guard (moveLegalB illFormed.board illFormed.marks d5B) = false
-- the round DOES re-enter …
#guard (roundStep cfgC noG illFormed []).isAgain = true
-- … on a coordinate that was already marked …
#guard roundCs illFormed [] = [(⟨0, 0⟩ : Coord)]
#guard illFormed.marks.contains ⟨0, 0⟩ = true
-- … so marks does NOT grow: 1 → 1. The theorem's hypothesis is what rules this out.
#guard illFormed.marks.length = 1
#guard (roundAgainState illFormed []).marks.length = 1

/-- The fuel theorem FIRES on a real board: 26 rounds always resolve a 5×5 turn. -/
example : ∃ bw, runTurn cfgC noG (openRound d5Board [0, 1, 2])
    (List.replicate 26 [d5A, d5B, d5C]) = some bw :=
  runTurn_fuel_bound cfgC noG d5Board [0, 1, 2] _ (by decide)

/-- And the strict-growth theorem fires on the audit's own fork witness. -/
example : (r1state.marks).length < (roundAgainState r1state [d5A, d5B, d5C]).marks.length :=
  roundStep_marks_strict_growth (cfg := cfgC) (g := noG) (rs := r1state) (subs := [d5A, d5B, d5C])
    (roundWF_openRound _ _) (by rw [roundStep_eq]; rfl)

end Canaries

/-! ## §8  Axiom hygiene -/

#assert_all_clean [
  mem_boardCoords,
  length_boardCoords,
  length_le_of_inBounds,
  allEqOpt_mem,
  edgeMap_mem_to,
  stopWalk_mem,
  landMap_mem_candidates,
  clashCoords_subset_candidates,
  unresolved_subset_candidates,
  roundStep_eq,
  roundStep_again_inv,
  roundWF_openRound,
  roundAll_legal,
  candidates_not_mem_marks,
  candidates_inBounds,
  roundCs_subset_candidates,
  roundCs_disjoint_marks,
  dedup_append_length_lt,
  roundStep_marks_strict_growth,
  roundStep_again_board,
  roundStep_again_wf,
  marks_length_le_board,
  roundStep_measure_decreases,
  againDepth_le,
  againDepth_le_openRound,
  runTurn_terminates,
  runTurn_fuel_bound,
  runTurn_none_length_le
]

end Dregg2.Games.AutomataflRules
