/-
# `AutomataflMarks` — THE MARKS COMMITMENT (multi-round braid milestone **M0**)

`docs/reference/AUTOMATAFL-MULTIROUND-BRAID-DESIGN.md` §2.1, §7 (M0). The keystone every later
milestone threads through: the RoundState window
`[ boardPack(RFC) ‖ marksPack(RFC) ‖ lockedVec(P·5) ‖ waitingInd(P) ‖ auto(2) ]` carries `marks`
across a clash round, and THIS file is the `marksPack(RFC)` half — emitted, transported and proven
injective, **hash-free**.

⚑ **SUBSTRATE, SAID OUT LOUD.** This is **LEAN-AUTHORED AIR**. The `{0,1}` range gates, the base-4
pack gates and the packed-felt PI bindings below are `VmConstraint2` values emitted here; Rust only
fills traces. Nothing in `dregg-automatafl/src/{air,moves,builder}.rs` is extended — it stays DEBT.

## The insight, verified rather than asserted

`marks` (the set of conflicted coordinates, illegal as src AND dst for ALL — `AutomataflRules.lean`
`MoveLegal`'s `m.frm ∉ marks ∧ m.to ∉ marks`) is an `n²` `{0,1}` **indicator board**. And
`AutomataflCommit.packBoardConstraintsAt n cellCol feltCol` is **parametric in the cell column**, so
the marks indicator packs with the IDENTICAL call into `feltCount n` felts (9 at `n = 11`) and its
injectivity is the IDENTICAL `packCell_inj` — the alphabet `{0,1}` is a subset of the board alphabet
`{0,1,2,3}`. Concretely, in this file:

* `marksPackConstraintsAt`/`marksCommitConstraintsAt` are *definitionally* `packBoardConstraintsAt`/
  `commitBoardConstraintsAt` (`marksPack_is_boardPack`, `rfl`), and
* `marksPack_pi_of_mem` is derived FROM the already-proven board transport
  `AutomataflCommitRefine.pack_pi_of_mem` through the one-line decode bridge
  `marksCode_eq_boardCode`.

So the marks commitment is a **free reuse of the proven board machinery, not new crypto**. What is
genuinely NEW is the *tighter* alphabet: `marksRangeCellsAt` emits `assert_member(cell, {0,1})`, not
`{0,1,2,3}`. The `#guard` canary in §8 shows the board gate ACCEPTS the code `2` that the marks gate
REFUSES — the tightening bites.

## What lands here (the M0 gate from the design doc)

| # | object | status |
|---|---|---|
| 1 | `marksDecodeAt` — the marks indicator board decoded off a row's cell columns | emitted-side decode, mirrors `boardDecodeCommitAt` |
| 2 | `marksCommitFamilyAt` — `{0,1}` gates ‖ pack gates ‖ PI bindings; `automataflMarksDesc n` | LEAN-AUTHORED AIR |
| 3 | `marksPack_pi_of_sat` — the emitted PI window IS the pack of the decoded indicator | PROVEN over `Satisfied2` |
| 4 | `marks_pack_injective` — equal marks-pack windows ⇒ cell-wise equal marks | PROVEN, `pack_injective_modp`, NO hash / NO chip table |
| 5 | `marks_window_eq_imp_mem_iff` — the SPEC correspondence to `RoundState.marks : List Coord` | PROVEN (membership ⟺ indicator = 1) |

## Honest scope

* This is **descriptor-side prep**. It is NOT wired into a Leg C descriptor — that is M1 — and there
  is no golden on disk and no `EmitByName` registration.
* The correspondence to `RoundState.marks` is a **set** correspondence on the board's `n²` coords: a
  `List Coord` also carries order and duplicates, which no `n²` indicator can recover and which the
  spec never reads (`MoveLegal` asks only `∉`). `clashCoords_inBounds` shows a round's fresh marks
  never fall off the board, so the indicator loses nothing the rules use.
* The pack is hash-free, so it adds NO new crypto floor — but it inherits the deployed FRI floor and
  the witness-generation perimeter like everything else in this tree.
-/
import Dregg2.Circuit.Emit.AutomataflCommitRefine
import Dregg2.Games.AutomataflRules

namespace Dregg2.Circuit.Emit.AutomataflMarks

open Dregg2.Circuit.Emit.AutomataflCommit
open Dregg2.Circuit.Emit.AutomataflCommitRefine
open Dregg2.Circuit.Emit.AutomataflStepRefine (Canon StepCanon canon_loc)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (pPrimeInt)
open Dregg2.Games.Automatafl (Board Coord Move Particle)
open Dregg2.Circuit (Assignment)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## §1 — The marks indicator board (the semantic object the pack commits to). -/

/-- The mark-indicator board: an `n × n` grid of booleans, `true` exactly on the conflicted
coordinates. This is `RoundState.marks : List Coord` viewed as the CHARACTERISTIC FUNCTION of the
marked set — the only thing `MoveLegal` reads of it (`m.frm ∉ marks ∧ m.to ∉ marks`). -/
structure MarksBoard where
  size   : Nat
  marked : Coord → Bool

/-- Indicator at a cell, `false` outside the board (the exact analogue of `Board.cellAt`'s
route-to-vacuum). -/
def MarksBoard.markAt (M : MarksBoard) (c : Coord) : Bool :=
  if c.x < M.size ∧ c.y < M.size then M.marked c else false

/-- The `{0,1}` felt code of an indicator bit. This is the marks alphabet — a SUBSET of the board
alphabet `{VAC=0, REP=1, ATT=2, AUTO=3}`, which is precisely why the board pack machinery applies
verbatim. -/
def markBit (b : Bool) : ℤ := if b then 1 else 0

/-- The felt→bit inverse (total; pinned to the alphabet by `markBit_bitToBool`). -/
def bitToBool (z : ℤ) : Bool := decide (z = 1)

@[simp] theorem markBit_true : markBit true = 1 := rfl
@[simp] theorem markBit_false : markBit false = 0 := rfl

/-- `markBit` is injective — indicator-code agreement gives indicator agreement (the marks twin of
`particleCode_inj`). -/
theorem markBit_inj {b1 b2 : Bool} (h : markBit b1 = markBit b2) : b1 = b2 := by
  cases b1 <;> cases b2 <;> first | rfl | exact absurd h (by decide)

/-- `bitToBool` inverts `markBit` on the alphabet `{0,1}`. -/
theorem markBit_bitToBool {z : ℤ} (h : z = 0 ∨ z = 1) : markBit (bitToBool z) = z := by
  rcases h with h | h <;> subst h <;> decide

/-- The marks board's cell-code column: the indicator bit of the in-bounds cell at linear index
`idx` (coord `(idx%n, idx/n)`), `0` on the pad indices `[n², 15·⌈n²/15⌉)`. Deliberately the same
shape as `AutomataflCommit.boardCode`, so `packCells` applies unchanged. -/
def marksCode (M : MarksBoard) (n : Nat) (idx : Nat) : ℤ :=
  if idx < n * n then markBit (M.markAt ⟨idx % n, idx / n⟩) else 0

/-- **The marks alphabet is `{0,1}` — strictly tighter than the board's `{0,1,2,3}`.** -/
theorem marksCode_mem01 (M : MarksBoard) (n idx : Nat) :
    marksCode M n idx = 0 ∨ marksCode M n idx = 1 := by
  unfold marksCode markBit
  split
  · split <;> simp
  · exact Or.inl rfl

/-- … and therefore lands inside the board alphabet, which is the `pack_injective` precondition.
THIS is the containment that makes the reuse sound. -/
theorem marksCode_mem (M : MarksBoard) (n idx : Nat) :
    0 ≤ marksCode M n idx ∧ marksCode M n idx < 4 := by
  rcases marksCode_mem01 M n idx with h | h <;> rw [h] <;> exact ⟨by decide, by decide⟩

theorem marksCode_inbounds (M : MarksBoard) (n x y : Nat) (hx : x < n) (hy : y < n) :
    marksCode M n (y * n + x) = markBit (M.markAt ⟨x, y⟩) := by
  have hlt : y * n + x < n * n :=
    calc y * n + x < y * n + n := by omega
      _ = (y + 1) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul (by omega) (le_refl n)
  unfold marksCode
  rw [if_pos hlt, idx_mod n x y hx, idx_div n x y hx]

/-- **The marks pack** — `⌈n²/15⌉` felts over the indicator's code column, by the SAME `packCells`
the board uses. At `n = 11` this is 9 felts. -/
def packMarks (M : MarksBoard) (n : Nat) : List ℤ := packCells (marksCode M n) (feltCount n)

/-- The number of window lanes a marks commitment occupies — what M5's RoundState window widens by
(twice: `marksIn ‖ marksOut`). -/
def marksWindowLanes (n : Nat) : Nat := feltCount n

/-- **`packMarks_injective` — the marks seam corollary, PURE Lean, NO crypto.** Two indicator
boards with equal packed felt-tuples agree at every in-bounds coordinate. Same base-4 positional
argument as `packBoard_injective`; the only difference is that the alphabet precondition comes from
`marksCode_mem` instead of `boardCode_mem`. -/
theorem packMarks_injective (n : Nat) (M1 M2 : MarksBoard) (heq : packMarks M1 n = packMarks M2 n) :
    ∀ x y : Nat, x < n → y < n → M1.markAt ⟨x, y⟩ = M2.markAt ⟨x, y⟩ := by
  unfold packMarks at heq
  have hcodes := pack_injective (marksCode M1 n) (marksCode M2 n) (feltCount n)
    (fun i _ => marksCode_mem M1 n i) (fun i _ => marksCode_mem M2 n i) heq
  intro x y hx hy
  have hlt : y * n + x < n * n :=
    calc y * n + x < y * n + n := by omega
      _ = (y + 1) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul (by omega) (le_refl n)
  have hidx : y * n + x < 15 * feltCount n := lt_of_lt_of_le hlt (sq_le_feltCount n)
  have hc := hcodes (y * n + x) hidx
  rw [marksCode_inbounds M1 n x y hx hy, marksCode_inbounds M2 n x y hx hy] at hc
  exact markBit_inj hc

/-! ## §2 — THE SPEC CORRESPONDENCE: `RoundState.marks : List Coord` ⟷ the indicator.

`AutomataflRules.RoundState.marks` is a `List Coord`. `marksBoardOf` is the bridge, and
`marksBoardOf_markAt_iff` / `marksCode_eq_one_iff_mem` are the statement M1 (Leg C) and M6 (Leg R's
`moveLegalB` marks conjunct) consume: **membership in the spec list ⟺ the indicator cell is 1**. -/

/-- The indicator board of a spec marks list on an `n × n` board. -/
def marksBoardOf (n : Nat) (marks : List Coord) : MarksBoard where
  size   := n
  marked := fun c => decide (c ∈ marks)

/-- The indicator of a whole `RoundState` (its own board's `size` is the `n`). -/
def marksBoardOfRS (rs : Dregg2.Games.AutomataflRules.RoundState) : MarksBoard :=
  marksBoardOf rs.board.size rs.marks

/-- **THE CORRESPONDENCE (Bool form): indicator = 1 ⟺ the coord is in the spec's marks list.** -/
theorem marksBoardOf_markAt_iff (n : Nat) (marks : List Coord) (c : Coord)
    (hx : c.x < n) (hy : c.y < n) :
    (marksBoardOf n marks).markAt c = true ↔ c ∈ marks := by
  simp [MarksBoard.markAt, marksBoardOf, hx, hy]

/-- **THE CORRESPONDENCE (felt form)**: the packed cell code at linear index `y·n + x` is `1`
exactly when `(x,y)` is a marked coordinate, `0` exactly when it is not. This is the statement the
Leg-C legality gate `legal[w] = validMove ∧ ¬marksIn[frm] ∧ ¬marksIn[to]` refines against. -/
theorem marksCode_eq_one_iff_mem (n : Nat) (marks : List Coord) (x y : Nat)
    (hx : x < n) (hy : y < n) :
    marksCode (marksBoardOf n marks) n (y * n + x) = 1 ↔ (⟨x, y⟩ : Coord) ∈ marks := by
  rw [marksCode_inbounds _ n x y hx hy]
  constructor
  · intro h
    have hb : (marksBoardOf n marks).markAt ⟨x, y⟩ = true := by
      by_contra hne
      rw [Bool.not_eq_true] at hne
      rw [hne] at h; exact absurd h (by decide)
    exact (marksBoardOf_markAt_iff n marks ⟨x, y⟩ hx hy).mp hb
  · intro h
    rw [(marksBoardOf_markAt_iff n marks ⟨x, y⟩ hx hy).mpr h]; rfl

theorem marksCode_eq_zero_iff_not_mem (n : Nat) (marks : List Coord) (x y : Nat)
    (hx : x < n) (hy : y < n) :
    marksCode (marksBoardOf n marks) n (y * n + x) = 0 ↔ (⟨x, y⟩ : Coord) ∉ marks := by
  constructor
  · intro h hmem
    have h1 := (marksCode_eq_one_iff_mem n marks x y hx hy).mpr hmem
    rw [h] at h1; exact absurd h1 (by decide)
  · intro h
    rcases marksCode_mem01 (marksBoardOf n marks) n (y * n + x) with h0 | h1
    · exact h0
    · exact absurd ((marksCode_eq_one_iff_mem n marks x y hx hy).mp h1) h

/-- **`marks_window_eq_imp_mem_iff` — WHAT THE ROUNDSTATE SEAM BUYS, at the SPEC level.** Two marks
LISTS whose packed windows agree (mod `p`) are the SAME SET on the board: `c ∈ m1 ↔ c ∈ m2` at every
in-bounds coordinate. NO hash, NO chip-table soundness — the window equality IS marks equality, by
base-4 injectivity (`pack_injective_modp`). This is the theorem that makes `C_k.OUT == C_{k+1}.IN`
carry `marks` and not merely "some 9 felts". -/
theorem marks_window_eq_imp_mem_iff (n : Nat) (m1 m2 : List Coord)
    (heq : ∀ j, j < feltCount n →
      packCell (marksCode (marksBoardOf n m1) n) j
        ≡ packCell (marksCode (marksBoardOf n m2) n) j [ZMOD 2013265921]) :
    ∀ c : Coord, c.x < n → c.y < n → (c ∈ m1 ↔ c ∈ m2) := by
  have hcodes := pack_injective_modp
    (marksCode (marksBoardOf n m1) n) (marksCode (marksBoardOf n m2) n) (feltCount n)
    (fun i _ => marksCode_mem _ n i) (fun i _ => marksCode_mem _ n i)
    (fun j hj => heq j hj)
  intro c hx hy
  have hlt : c.y * n + c.x < n * n :=
    calc c.y * n + c.x < c.y * n + n := by omega
      _ = (c.y + 1) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul (by omega) (le_refl n)
  have hidx : c.y * n + c.x < 15 * feltCount n := lt_of_lt_of_le hlt (sq_le_feltCount n)
  have hcc := hcodes (c.y * n + c.x) hidx
  constructor
  · intro hm
    have h1 := (marksCode_eq_one_iff_mem n m1 c.x c.y hx hy).mpr hm
    exact (marksCode_eq_one_iff_mem n m2 c.x c.y hx hy).mp (by rw [← hcc]; exact h1)
  · intro hm
    have h1 := (marksCode_eq_one_iff_mem n m2 c.x c.y hx hy).mpr hm
    exact (marksCode_eq_one_iff_mem n m1 c.x c.y hx hy).mp (by rw [hcc]; exact h1)

/-! ### §2.1 — A round's fresh marks never fall off the board.

The indicator is an `n²` object, so the correspondence above is stated at in-bounds coordinates. The
two lemmas here show that is not a restriction on `roundStep`'s output: `cs` is drawn from the moves'
own endpoints (`clashCoords ⊆ candidates`), and a round's moves are in-bounds. -/

open Dregg2.Games.AutomataflRules (clashCoords candidates)

theorem clashCoords_subset_candidates (b : Board) (ms : List Move) {c : Coord}
    (h : c ∈ clashCoords b ms) : c ∈ candidates ms := by
  unfold clashCoords at h
  exact (List.mem_filter.mp (List.mem_dedup.mp h)).1

theorem candidates_inBounds (b : Board) (ms : List Move)
    (hms : ∀ m ∈ ms, b.inBounds m.frm ∧ b.inBounds m.to) {c : Coord}
    (h : c ∈ candidates ms) : b.inBounds c := by
  unfold candidates at h
  rcases List.mem_append.mp h with h | h
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp h; exact (hms m hm).1
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp h; exact (hms m hm).2

/-- **The fresh marks of a clash round are ON the board.** So the `n²` `{0,1}` indicator is a
FAITHFUL carrier of `roundStep`'s `.again` `marks ++ cs` (up to the set/list distinction the rules
never read). -/
theorem clashCoords_inBounds (b : Board) (ms : List Move)
    (hms : ∀ m ∈ ms, b.inBounds m.frm ∧ b.inBounds m.to) {c : Coord}
    (h : c ∈ clashCoords b ms) : c.x < b.size ∧ c.y < b.size :=
  candidates_inBounds b ms hms (clashCoords_subset_candidates b ms h)

/-! ## §3 — THE EMITTED FAMILY (LEAN-AUTHORED AIR).

Three gate families at an ARBITRARY cell / felt column base and PI base — the same three degrees of
freedom `AutomataflCommit` §6.1b gives the board commitment, so a Leg C descriptor carrying BOTH
`marksIn` and `marksOut` in one row emits this family twice at its own bases. -/

/-- **THE TIGHTER ALPHABET.** `assert_member(cell, {0,1})` per marks cell — one factor NARROWER than
`boardRangeCells`' `{0,1,2,3}`. This is what makes "the marks cells are indicator bits" a THEOREM of
the descriptor (`marksAlpha_of_mem`) rather than an assumption, and it is the only place the marks
family differs from the board family. Degree 2. -/
def marksRangeCellsAt (n : Nat) (cellCol : Nat → Nat) : List VmConstraint2 :=
  (List.range (n * n)).map (fun c => (.base (.gate (memberExpr (cellCol c) [0, 1])) : VmConstraint2))

/-- **THE FREE REUSE.** The `⌈n²/15⌉` degree-1 base-4 pack gates over the marks cells — literally
`AutomataflCommit.packBoardConstraintsAt`, because that family is parametric in the cell column. -/
def marksPackConstraintsAt (n : Nat) (cellCol feltCol : Nat → Nat) : List VmConstraint2 :=
  packBoardConstraintsAt n cellCol feltCol

/-- Bind the `⌈n²/15⌉` packed marks felts to the PI window `[piBase, piBase + ⌈n²/15⌉)` — literally
`AutomataflCommit.commitBoardConstraintsAt`. -/
def marksCommitConstraintsAt (n : Nat) (feltCol : Nat → Nat) (piBase : Nat) : List VmConstraint2 :=
  commitBoardConstraintsAt n feltCol piBase

/-- The reuse, stated as a checkable identity rather than a claim in prose. -/
theorem marksPack_is_boardPack (n : Nat) (cellCol feltCol : Nat → Nat) :
    marksPackConstraintsAt n cellCol feltCol = packBoardConstraintsAt n cellCol feltCol := rfl

theorem marksCommit_is_boardCommit (n : Nat) (feltCol : Nat → Nat) (piBase : Nat) :
    marksCommitConstraintsAt n feltCol piBase = commitBoardConstraintsAt n feltCol piBase := rfl

/-- **`marksCommitFamilyAt` — the whole marks commitment at one base.** `{0,1}` gates ‖ pack gates ‖
packed-felt PI bindings. This is the object M1's Leg C descriptor splices in (twice: `marksIn` at
`PI[38 …)`, `marksOut` at `PI[38+RFC …)`). -/
def marksCommitFamilyAt (n : Nat) (cellCol feltCol : Nat → Nat) (piBase : Nat) : List VmConstraint2 :=
  marksRangeCellsAt n cellCol ++ marksPackConstraintsAt n cellCol feltCol
    ++ marksCommitConstraintsAt n feltCol piBase

/-! ### §3.1 — The standalone descriptor (the object §4–§6 are proven over). -/

/-- Marks cell column `i` (the working representation is 1 felt / cell). -/
def MARKS_CELL (i : Nat) : Nat := i
/-- The packed marks felts sit right after the `n²` indicator cells. -/
def MARKS_FELT_BASE (n : Nat) : Nat := n * n
/-- Packed marks felt column `j`. -/
def MARKS_FELT (n j : Nat) : Nat := MARKS_FELT_BASE n + j
/-- PI base for the packed marks felts (the standalone layout mirrors `COMMIT_PI_BASE`). -/
def MARKS_PI_BASE : Nat := 16

/-- **`automataflMarksDesc n` — the standalone marks commitment.** `n²` indicator cells + `⌈n²/15⌉`
packed felts; constraints = `{0,1}` range gates · base-4 pack gates · packed-felt PI bindings. No
tables, no hash sites, no lookups: the whole commitment is degree-≤2 gates plus boundary bindings. -/
def automataflMarksDesc (n : Nat) : EffectVmDescriptor2 :=
  { name        := "dregg-automatafl-marks-optA"
  , traceWidth  := MARKS_FELT_BASE n + feltCount n
  , piCount     := MARKS_PI_BASE + feltCount n
  , tables      := []
  , constraints := marksCommitFamilyAt n MARKS_CELL (MARKS_FELT n) MARKS_PI_BASE
  , hashSites   := []
  , ranges      := [] }

/-! ## §4 — The decode, and the `{0,1}` gate extraction. -/

/-- **`marksDecodeAt` — the emitted-side decode**, the exact mirror of
`AutomataflCommitRefine.boardDecodeCommitAt`: cell `(x,y)`'s indicator bit is the felt-decode of
`loc[cellCol (y·n + x)]`. -/
def marksDecodeAt (n : Nat) (cellCol : Nat → Nat) (e : VmRowEnv) : MarksBoard where
  size   := n
  marked := fun c => bitToBool (e.loc (cellCol (c.y * n + c.x)))

/-- The standalone-layout instance. -/
def marksDecode (n : Nat) (e : VmRowEnv) : MarksBoard := marksDecodeAt n MARKS_CELL e

/-- **The `{0,1}` gate DERIVES the indicator alphabet.** A canonical cell whose two-factor
membership gate `x·(x−1)` vanishes mod `p` is `0` or `1` — the marks twin of `mem3_of_gate` /
`mem4_of_gate`, one factor narrower. Same primality argument. -/
theorem mem2_of_gate {a : Assignment} {c : Nat}
    (h : (memberExpr c [0, 1]).eval a ≡ 0 [ZMOD 2013265921]) (hc : Canon (a c)) :
    a c = 0 ∨ a c = 1 := by
  have e : (memberExpr c [0, 1]).eval a = a c * (a c + -1) := rfl
  rw [e] at h
  have hd : (2013265921 : ℤ) ∣ a c * (a c + -1) := Int.modEq_zero_iff_dvd.mp (by simpa using h)
  obtain ⟨hc0, hc1⟩ := hc
  rcases pPrimeInt.dvd_mul.mp hd with h1 | h1
  · obtain ⟨k, hk⟩ := h1; left; omega
  · obtain ⟨k, hk⟩ := h1; right; omega

/-- **The circuit cell IS the decoded indicator cell** (on the `{0,1}` alphabet); pad indices are
`0`. Mirrors `AutomataflCommitRefine.boardCode_decode_eqAt`. -/
theorem marksCode_decode_eqAt (n : Nat) (cellCol : Nat → Nat) (e : VmRowEnv) (idx : Nat)
    (hmem : idx < n * n → (e.loc (cellCol idx) = 0 ∨ e.loc (cellCol idx) = 1)) :
    marksCode (marksDecodeAt n cellCol e) n idx
      = if idx < n * n then e.loc (cellCol idx) else 0 := by
  unfold marksCode
  by_cases hlt : idx < n * n
  · rw [if_pos hlt, if_pos hlt]
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp at hlt
      · exact h
    have hxlt : idx % n < n := Nat.mod_lt _ hn
    have hylt : idx / n < n := Nat.div_lt_of_lt_mul hlt
    have hidx : (idx / n) * n + idx % n = idx := by rw [Nat.mul_comm]; exact Nat.div_add_mod idx n
    have hmark : (marksDecodeAt n cellCol e).markAt ⟨idx % n, idx / n⟩
        = bitToBool (e.loc (cellCol idx)) := by
      simp [MarksBoard.markAt, marksDecodeAt, hxlt, hylt, hidx]
    rw [hmark, markBit_bitToBool (hmem hlt)]
  · rw [if_neg hlt, if_neg hlt]

/-- **THE BRIDGE THAT MAKES THE REUSE LITERAL.** On the `{0,1}` alphabet the marks code column and
the BOARD code column of the same circuit columns are the SAME function — both are "the column value
in bounds, `0` on the pad". So every board-pack theorem transfers to marks by rewriting, with no
second copy of the base-4 argument. -/
theorem marksCode_eq_boardCode (n : Nat) (cellCol : Nat → Nat) (e : VmRowEnv) (idx : Nat)
    (halpha : ∀ i, i < n * n → (e.loc (cellCol i) = 0 ∨ e.loc (cellCol i) = 1)) :
    marksCode (marksDecodeAt n cellCol e) n idx
      = boardCode (boardDecodeCommitAt n cellCol e) n idx := by
  rw [marksCode_decode_eqAt n cellCol e idx (fun h => halpha idx h),
      boardCode_decode_eqAt n cellCol e idx
        (fun h => by rcases halpha idx h with h' | h' <;> simp [h'])]

/-- Per-felt form of the bridge. -/
theorem packCell_marksCode_eqAt (n j : Nat) (cellCol : Nat → Nat) (e : VmRowEnv)
    (halpha : ∀ i, i < n * n → (e.loc (cellCol i) = 0 ∨ e.loc (cellCol i) = 1)) :
    packCell (marksCode (marksDecodeAt n cellCol e) n) j
      = packCell (boardCode (boardDecodeCommitAt n cellCol e) n) j := by
  unfold packCell
  refine congrArg horner4 ?_
  refine List.map_congr_left ?_
  intro i _
  exact marksCode_eq_boardCode n cellCol e (15 * j + i) halpha

/-! ## §5 — THE TRANSPORT: the emitted PI window IS the pack of the decoded marks indicator. -/

section Transport
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
  {t : VmTrace} {n : Nat}

section Host
variable {D : EffectVmDescriptor2}

/-- **`marksAlpha_of_mem`** — a descriptor carrying the `{0,1}` gate at `cellCol idx` forces that
column into the indicator alphabet on a satisfying canonical trace. -/
theorem marksAlpha_of_mem (hsat : Satisfied2 hash D minit mfin maddrs t)
    (hc : StepCanon t) (hlen : 1 < t.rows.length) (cellCol : Nat → Nat) (idx : Nat)
    (hg : (.base (.gate (memberExpr (cellCol idx) [0, 1])) : VmConstraint2) ∈ D.constraints) :
    (envAt t 0).loc (cellCol idx) = 0 ∨ (envAt t 0).loc (cellCol idx) = 1 :=
  mem2_of_gate (gate_of_mem hsat 0 (by omega) hg) (canon_loc hc 0 _)

/-- **`marksPack_pi_of_mem` — THE MARKS TRANSPORT, host form.** For any descriptor emitting the
re-pointed pack gate for felt `j`, the matching `.piBinding`, and the `{0,1}` gates on its marks
cells, the published `PI[piBase+j]` IS (mod `p`) the `j`-th packed felt of the MARKS INDICATOR
decoded off those very columns.

Derived FROM the board transport `AutomataflCommitRefine.pack_pi_of_mem` through
`packCell_marksCode_eqAt` — no re-derivation, no second base-4 argument. NO hash, NO chip-table
soundness hypothesis: one degree-1 gate plus a boundary binding. -/
theorem marksPack_pi_of_mem (hsat : Satisfied2 hash D minit mfin maddrs t)
    (hlen : 1 < t.rows.length) (cellCol feltCol : Nat → Nat) (piBase j : Nat)
    (halpha : ∀ i, i < n * n →
      ((envAt t 0).loc (cellCol i) = 0 ∨ (envAt t 0).loc (cellCol i) = 1))
    (hpack : linGate (packTermsAt n j cellCol feltCol) 0 ∈ D.constraints)
    (hpi : (.base (.piBinding VmRow.first (feltCol j) (piBase + j)) : VmConstraint2)
      ∈ D.constraints) :
    t.pub (piBase + j)
      ≡ packCell (marksCode (marksDecodeAt n cellCol (envAt t 0)) n) j [ZMOD 2013265921] := by
  rw [packCell_marksCode_eqAt n j cellCol (envAt t 0) halpha]
  exact pack_pi_of_mem hsat hlen cellCol feltCol piBase j
    (fun i hi => by rcases halpha i hi with h | h <;> simp [h]) hpack hpi

end Host

/-! ### §5.1 — Membership of the three ingredients in the standalone descriptor. -/

theorem marks_range_mem (idx : Nat) (hidx : idx < n * n) :
    (.base (.gate (memberExpr (MARKS_CELL idx) [0, 1])) : VmConstraint2)
      ∈ (automataflMarksDesc n).constraints := by
  show _ ∈ marksRangeCellsAt n MARKS_CELL ++ marksPackConstraintsAt n MARKS_CELL (MARKS_FELT n)
    ++ marksCommitConstraintsAt n (MARKS_FELT n) MARKS_PI_BASE
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_map.mpr ⟨idx, List.mem_range.mpr hidx, rfl⟩))

theorem marks_pack_mem (j : Nat) (hj : j < feltCount n) :
    linGate (packTermsAt n j MARKS_CELL (MARKS_FELT n)) 0 ∈ (automataflMarksDesc n).constraints := by
  show _ ∈ marksRangeCellsAt n MARKS_CELL ++ marksPackConstraintsAt n MARKS_CELL (MARKS_FELT n)
    ++ marksCommitConstraintsAt n (MARKS_FELT n) MARKS_PI_BASE
  exact List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))

theorem marks_pi_mem (j : Nat) (hj : j < feltCount n) :
    (.base (.piBinding VmRow.first (MARKS_FELT n j) (MARKS_PI_BASE + j)) : VmConstraint2)
      ∈ (automataflMarksDesc n).constraints := by
  show _ ∈ marksRangeCellsAt n MARKS_CELL ++ marksPackConstraintsAt n MARKS_CELL (MARKS_FELT n)
    ++ marksCommitConstraintsAt n (MARKS_FELT n) MARKS_PI_BASE
  exact List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)

/-- The indicator alphabet, off the emitted `{0,1}` gates of the standalone descriptor. -/
theorem marksAlpha_of_sat (hsat : Satisfied2 hash (automataflMarksDesc n) minit mfin maddrs t)
    (hc : StepCanon t) (hlen : 1 < t.rows.length) (idx : Nat) (hidx : idx < n * n) :
    (envAt t 0).loc (MARKS_CELL idx) = 0 ∨ (envAt t 0).loc (MARKS_CELL idx) = 1 :=
  marksAlpha_of_mem hsat hc hlen MARKS_CELL idx (marks_range_mem idx hidx)

/-- **`marksPack_pi_of_sat` — THE MARKS TRANSPORT (the exact analogue of
`AutomataflResolveRefine.resolve_midPack_pi_of_sat`).** On a satisfying canonical trace of the
emitted marks descriptor, the published marks window `PI[16+j]` IS (mod `p`) the `j`-th packed felt
of the marks indicator board decoded off the descriptor's own cell columns. Every ingredient —
alphabet, pack gate, PI binding — is EXTRACTED from the emitted object; none is assumed. -/
theorem marksPack_pi_of_sat (hsat : Satisfied2 hash (automataflMarksDesc n) minit mfin maddrs t)
    (hc : StepCanon t) (hlen : 1 < t.rows.length) (j : Nat) (hj : j < feltCount n) :
    t.pub (MARKS_PI_BASE + j)
      ≡ packCell (marksCode (marksDecode n (envAt t 0)) n) j [ZMOD 2013265921] :=
  marksPack_pi_of_mem hsat hlen MARKS_CELL (MARKS_FELT n) MARKS_PI_BASE j
    (fun i hi => marksAlpha_of_sat hsat hc hlen i hi) (marks_pack_mem j hj) (marks_pi_mem j hj)

/-- **`marks_forge_rejected` — the transport BITES.** No satisfying canonical witness can publish a
marks window that is not the genuine pack of its own indicator cells. Contrapositive of
`marksPack_pi_of_sat`; the M1 canary "a forged `marksOut` is UNSAT" is this at the Leg C bases. -/
theorem marks_forge_rejected (hsat : Satisfied2 hash (automataflMarksDesc n) minit mfin maddrs t)
    (hc : StepCanon t) (hlen : 1 < t.rows.length) (j : Nat) (hj : j < feltCount n)
    (hforge : ¬ (t.pub (MARKS_PI_BASE + j)
      ≡ packCell (marksCode (marksDecode n (envAt t 0)) n) j [ZMOD 2013265921])) : False :=
  hforge (marksPack_pi_of_sat hsat hc hlen j hj)

end Transport

/-! ## §6 — INJECTIVITY: equal marks windows ⇒ cell-wise equal marks. HASH-FREE.

This is the property that makes the RoundState seam `left.OUT == right.IN` mean "the same marks",
with NO collision-resistance assumption and NO chip-table soundness — the same base-4 argument
(`pack_injective_modp`) the board window rides. -/

/-- **`marks_pack_congr_injective` — the pure form** (the marks twin of
`AutomataflCommitRefine.seam_of_pack_congr`). Two indicator boards whose packed windows are
congruent mod `p` to equal published values agree at every in-bounds coordinate. -/
theorem marks_pack_congr_injective {n : Nat} (M1 M2 : MarksBoard) (v1 v2 : Nat → ℤ)
    (h1 : ∀ j, j < feltCount n → v1 j ≡ packCell (marksCode M1 n) j [ZMOD 2013265921])
    (h2 : ∀ j, j < feltCount n → v2 j ≡ packCell (marksCode M2 n) j [ZMOD 2013265921])
    (heq : ∀ j, j < feltCount n → v1 j = v2 j) :
    ∀ x y : Nat, x < n → y < n → M1.markAt ⟨x, y⟩ = M2.markAt ⟨x, y⟩ := by
  have hcodes : ∀ i, i < 15 * feltCount n → marksCode M1 n i = marksCode M2 n i := by
    refine pack_injective_modp (marksCode M1 n) (marksCode M2 n) (feltCount n)
      (fun i _ => marksCode_mem _ n i) (fun i _ => marksCode_mem _ n i) ?_
    intro j hj
    exact ((h1 j hj).symm.trans ((heq j hj) ▸ h2 j hj))
  intro x y hx hy
  have hlt : y * n + x < n * n :=
    calc y * n + x < y * n + n := by omega
      _ = (y + 1) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul (by omega) (le_refl n)
  have hidx : y * n + x < 15 * feltCount n := lt_of_lt_of_le hlt (sq_le_feltCount n)
  have hcc := hcodes (y * n + x) hidx
  rw [marksCode_inbounds M1 n x y hx hy, marksCode_inbounds M2 n x y hx hy] at hcc
  exact markBit_inj hcc

/-- **`marks_pack_injective` — THE M5 CONSUMABLE.** Two satisfying canonical witnesses of the marks
descriptor whose published marks windows are EQUAL have cell-wise-agreeing decoded marks indicators.
This is exactly what the RoundState-window connect (`C_k.OUT == C_{k+1}.IN` on the marks lanes)
enforces, and it is discharged with NO hash and NO chip-table soundness: `marksPack_pi_of_sat` both
sides feeding `pack_injective_modp`. -/
theorem marks_pack_injective {hash : List ℤ → ℤ} {n : Nat}
    {minit1 : ℤ → ℤ} {mfin1 : ℤ → ℤ × Nat} {maddrs1 : List ℤ} {t1 : VmTrace}
    {minit2 : ℤ → ℤ} {mfin2 : ℤ → ℤ × Nat} {maddrs2 : List ℤ} {t2 : VmTrace}
    (hsat1 : Satisfied2 hash (automataflMarksDesc n) minit1 mfin1 maddrs1 t1)
    (hc1 : StepCanon t1) (hlen1 : 1 < t1.rows.length)
    (hsat2 : Satisfied2 hash (automataflMarksDesc n) minit2 mfin2 maddrs2 t2)
    (hc2 : StepCanon t2) (hlen2 : 1 < t2.rows.length)
    (hpi : ∀ j, j < feltCount n →
      t1.pub (MARKS_PI_BASE + j) = t2.pub (MARKS_PI_BASE + j)) :
    ∀ x y : Nat, x < n → y < n →
      (marksDecode n (envAt t1 0)).markAt ⟨x, y⟩ = (marksDecode n (envAt t2 0)).markAt ⟨x, y⟩ :=
  marks_pack_congr_injective (n := n) _ _
    (fun j => t1.pub (MARKS_PI_BASE + j)) (fun j => t2.pub (MARKS_PI_BASE + j))
    (fun j hj => marksPack_pi_of_sat hsat1 hc1 hlen1 j hj)
    (fun j hj => marksPack_pi_of_sat hsat2 hc2 hlen2 j hj)
    (fun j hj => hpi j hj)

/-! ## §7 — Non-vacuity canaries at `n = 3` and `n = 11` (`#guard`). -/

open Dregg2.Games.AutomataflRules

/-! ### §7.1 — `n = 3`: one felt; empty / one-coord / differing marks sets. -/

/-- `n = 3`: the EMPTY marks set (a fresh turn's `openRound`). -/
def marks3Empty : MarksBoard := marksBoardOf 3 []
/-- `n = 3`: ONE conflicted coordinate `(1,1)` — linear index `1·3+1 = 4`, weight `4^4 = 256`. -/
def marks3One : MarksBoard := marksBoardOf 3 [⟨1, 1⟩]
/-- `n = 3`: a DIFFERENT single coordinate `(2,0)` — linear index `2`, weight `4^2 = 16`. -/
def marks3One' : MarksBoard := marksBoardOf 3 [⟨2, 0⟩]
/-- `n = 3`: both. -/
def marks3Two : MarksBoard := marksBoardOf 3 [⟨1, 1⟩, ⟨2, 0⟩]

#guard feltCount 3 = 1
#guard packMarks marks3Empty 3 = [0]
#guard packMarks marks3One 3 = [256]
#guard packMarks marks3One' 3 = [16]
#guard packMarks marks3Two 3 = [272]
-- THE INJECTIVITY CANARIES: every one of these sets has its OWN commitment.
#guard packMarks marks3Empty 3 ≠ packMarks marks3One 3
#guard packMarks marks3One 3 ≠ packMarks marks3One' 3
#guard packMarks marks3One 3 ≠ packMarks marks3Two 3        -- differ in EXACTLY one cell
-- the correspondence, computed: indicator = 1 exactly on the marked coords.
#guard marks3Two.markAt ⟨1, 1⟩ = true
#guard marks3Two.markAt ⟨2, 0⟩ = true
#guard marks3Two.markAt ⟨0, 0⟩ = false
#guard marks3Two.markAt ⟨9, 9⟩ = false                       -- off-board reads false
#guard marksCode marks3Two 3 4 = 1
#guard marksCode marks3Two 3 0 = 0

/-! ### §7.2 — `n = 11` (the deployed board): nine felts, and the LAST-CELL canary. -/

def marks11Empty : MarksBoard := marksBoardOf 11 []
/-- `(5,5)` — linear index `5·11+5 = 60 = 15·4`, so felt 4, digit 0: weight `1`. -/
def marks11One : MarksBoard := marksBoardOf 11 [⟨5, 5⟩]
/-- `(5,5)` and `(10,10)` — the LAST cell, linear index `120 = 15·8`: felt 8, digit 0. -/
def marks11Two : MarksBoard := marksBoardOf 11 [⟨5, 5⟩, ⟨10, 10⟩]

#guard feltCount 11 = 9
#guard marksWindowLanes 11 = 9
#guard (packMarks marks11Empty 11).length = 9
#guard packMarks marks11Empty 11 = [0, 0, 0, 0, 0, 0, 0, 0, 0]
#guard packMarks marks11One 11 = [0, 0, 0, 0, 1, 0, 0, 0, 0]
#guard packMarks marks11Two 11 = [0, 0, 0, 0, 1, 0, 0, 0, 1]
#guard packMarks marks11Empty 11 ≠ packMarks marks11One 11
-- ONE differing cell — and it is the LAST cell of the 11×11 board, the exact blind spot the retired
-- `board_root8` leaf had (it absorbed cells [0..8) only). The marks pack SEPARATES them.
#guard packMarks marks11One 11 ≠ packMarks marks11Two 11
#guard (packMarks marks11One 11).getD 8 0 ≠ (packMarks marks11Two 11).getD 8 0
-- and the change is LOCALIZED, not a hash smear: felt 4 is untouched.
#guard (packMarks marks11One 11).getD 4 0 = (packMarks marks11Two 11).getD 4 0
#guard marks11Two.markAt ⟨10, 10⟩ = true
#guard marks11Two.markAt ⟨10, 9⟩ = false

/-! ### §7.3 — SPEC-CONNECTED: the marks of an ACTUAL `roundStep` clash pack, and separate.

Not a hand-made indicator — `d4Marks`/`d5Marks` are read straight off `roundStep`'s `.again`
RoundState on the rules file's own audit witnesses (a collide at `(2,0)`, a fork at `(0,0)` on a
5×5 board). Their commitments differ from each other and from the empty (round-1) marks set. -/

-- the rules file's own `mv`/`cfgCol`/`noGoals` are `private`; these are the same values.
private def cfgColM : GameConfig := ⟨.column⟩
private def noGoalsM : GoalAssignment := ⟨[]⟩
private def mkMv (w : Dregg2.Games.Automatafl.Pid) (a d : Coord) : Move := ⟨w, a, d⟩

/-- The marks `roundStep` produces on the D4a COLLIDE witness: `[(2,0)]`. -/
def d4Marks : List Coord :=
  (roundStep cfgColM noGoalsM (openRound collBoard [0, 1, 2]) [d4A, d4B, d4C]).marks
/-- The marks `roundStep` produces on the D4b FORK witness: `[(0,0)]`. -/
def d5Marks : List Coord :=
  (roundStep cfgColM noGoalsM (openRound d5Board [0, 1, 2]) [d5A, d5B, d5C]).marks

#guard feltCount 5 = 2
#guard d4Marks = [(⟨2, 0⟩ : Coord)]
#guard d5Marks = [(⟨0, 0⟩ : Coord)]
-- the spec's `.again` marks COMMIT: `(2,0)` ⇒ index 2 ⇒ 4² = 16; `(0,0)` ⇒ index 0 ⇒ 4⁰ = 1.
#guard packMarks (marksBoardOf 5 d4Marks) 5 = [16, 0]
#guard packMarks (marksBoardOf 5 d5Marks) 5 = [1, 0]
#guard packMarks (marksBoardOf 5 d4Marks) 5 ≠ packMarks (marksBoardOf 5 []) 5
#guard packMarks (marksBoardOf 5 d4Marks) 5 ≠ packMarks (marksBoardOf 5 d5Marks) 5
-- and the marked coordinate is exactly the one the RULES say is now illegal as src AND dst.
#guard (marksBoardOf 5 d4Marks).markAt ⟨2, 0⟩ = true
#guard moveLegalB collBoard d4Marks (mkMv 2 ⟨2, 0⟩ ⟨2, 4⟩) = false    -- marked SOURCE
#guard moveLegalB collBoard d4Marks (mkMv 0 ⟨0, 0⟩ ⟨2, 0⟩) = false    -- marked DESTINATION

/-! ### §7.4 — THE TIGHTER ALPHABET BITES (the one place marks ≠ board).

The board range gate accepts the code `2` (ATT). The marks range gate REFUSES it. Without this
tightening a prover could put a `2` in a marks cell, and `marksCode`'s `{0,1}` decode — hence the
whole indicator reading — would be a lie. -/

/-- A row whose cell 0 holds the indicator bit `1` (marked). -/
def demoMarksLoc : Assignment := fun c => if c = 0 then 1 else 0
/-- A row whose cell 0 holds the BOARD code `2` (ATT) — legal on a board, ILLEGAL as an indicator. -/
def demoTwoLoc : Assignment := fun c => if c = 0 then 2 else 0

#guard (memberExpr 0 [0, 1]).eval demoMarksLoc = 0            -- an indicator bit passes …
#guard (memberExpr 0 [0, 1]).eval demoTwoLoc ≠ 0              -- … the code 2 is REFUSED …
#guard (memberExpr 0 [0, 1, 2, 3]).eval demoTwoLoc = 0        -- … which the BOARD gate ACCEPTS.

/-! **THE FALSIFIER — the `{0,1}` gate is LOAD-BEARING, not decoration.** Take the row above with the
out-of-alphabet code `2` in marks cell 0 and its own HONEST pack `packed_0 = 2` in the felt column
(`MARKS_FELT 3 0 = 9`). The pack gate is satisfied — a `2` packs as happily as a `1`. But
`marksDecodeAt` reads that cell as UNMARKED (`bitToBool 2 = false`), so the pack of the DECODED
indicator is `0 ≠ 2`: `marksPack_pi_of_sat`'s conclusion is FALSE on this row. Only the `{0,1}` gate
excludes it. Drop `marksRangeCellsAt` from the family and the transport theorem stops being true. -/
def demoTwoRow : Assignment := fun c => if c = 0 then 2 else if c = 9 then 2 else 0

#guard linComb (packTermsAt 3 0 MARKS_CELL (MARKS_FELT 3)) demoTwoRow = 0   -- pack gate: SATISFIED
#guard (marksDecode 3 ⟨demoTwoRow, demoTwoRow, demoTwoRow, fun _ => 0⟩).markAt ⟨0, 0⟩ = false
#guard packCell (marksCode (marksDecode 3 ⟨demoTwoRow, demoTwoRow, demoTwoRow, fun _ => 0⟩) 3) 0 = 0
#guard demoTwoRow (MARKS_FELT 3 0)
  ≠ packCell (marksCode (marksDecode 3 ⟨demoTwoRow, demoTwoRow, demoTwoRow, fun _ => 0⟩) 3) 0
-- and the `{0,1}` gate is EXACTLY what refuses it.
#guard (memberExpr (MARKS_CELL 0) [0, 1]).eval demoTwoRow ≠ 0

/-! ### §7.5 — Emitted shapes (the family is the size the design doc budgets). -/

#guard (marksRangeCellsAt 3 MARKS_CELL).length = 9
#guard (marksRangeCellsAt 11 MARKS_CELL).length = 121
#guard (marksPackConstraintsAt 11 MARKS_CELL (MARKS_FELT 11)).length = 9
#guard (marksCommitConstraintsAt 11 (MARKS_FELT 11) MARKS_PI_BASE).length = 9
#guard (marksCommitFamilyAt 11 MARKS_CELL (MARKS_FELT 11) MARKS_PI_BASE).length = 139
#guard (automataflMarksDesc 11).traceWidth = 130              -- 121 indicator cells + 9 felts
#guard (automataflMarksDesc 11).piCount = 25                  -- 16 door prefix + 9 marks felts
#guard (automataflMarksDesc 11).constraints.length = 139      -- 121 {0,1} + 9 pack + 9 commit
#guard (automataflMarksDesc 11).tables.length = 0
#guard (automataflMarksDesc 11).hashSites.length = 0          -- HASH-FREE, by construction
#guard (automataflMarksDesc 3).traceWidth = 10
#guard (automataflMarksDesc 3).constraints.length = 11

/-- The genuine pack gate vanishes on a row whose felt column carries the true pack, and BITES on a
forged one — the same two-sided witness `AutomataflCommitRefine` §5 gives the board. `n = 3`, one
mark at cell 0, so `packed_0 = 1`; the felt column is `MARKS_FELT 3 0 = 9`. -/
def demoMarks3Loc : Assignment := fun c => if c = 0 then 1 else if c = 9 then 1 else 0
/-- Same row, felt FORGED to `7 ≠ 1`. -/
def demoMarks3Forge : Assignment := fun c => if c = 0 then 1 else if c = 9 then 7 else 0

#guard linComb (packTermsAt 3 0 MARKS_CELL (MARKS_FELT 3)) demoMarks3Loc = 0
#guard linComb (packTermsAt 3 0 MARKS_CELL (MARKS_FELT 3)) demoMarks3Forge = 6
#guard (sumExpr (((packTermsAt 3 0 MARKS_CELL (MARKS_FELT 3)).filter
  (fun t => t.1 != 0)).map varTerm)).eval demoMarks3Loc = 0
#guard (sumExpr (((packTermsAt 3 0 MARKS_CELL (MARKS_FELT 3)).filter
  (fun t => t.1 != 0)).map varTerm)).eval demoMarks3Forge ≠ 0
-- the decoded indicator of that genuine row IS the one-mark board, and its pack is the felt.
#guard (marksDecode 3 ⟨demoMarks3Loc, demoMarks3Loc, demoMarks3Loc, fun _ => 0⟩).markAt ⟨0, 0⟩ = true
#guard (marksDecode 3 ⟨demoMarks3Loc, demoMarks3Loc, demoMarks3Loc, fun _ => 0⟩).markAt ⟨1, 0⟩ = false
#guard packCell (marksCode (marksDecode 3 ⟨demoMarks3Loc, demoMarks3Loc, demoMarks3Loc, fun _ => 0⟩) 3) 0 = 1

/-! ## §8 — Axiom hygiene: everything rests only on the kernel triple. -/

#assert_axioms markBit_inj
#assert_axioms markBit_bitToBool
#assert_axioms marksCode_mem01
#assert_axioms marksCode_mem
#assert_axioms marksCode_inbounds
#assert_axioms packMarks_injective
#assert_axioms marksBoardOf_markAt_iff
#assert_axioms marksCode_eq_one_iff_mem
#assert_axioms marksCode_eq_zero_iff_not_mem
#assert_axioms marks_window_eq_imp_mem_iff
#assert_axioms clashCoords_subset_candidates
#assert_axioms candidates_inBounds
#assert_axioms clashCoords_inBounds
#assert_axioms marksPack_is_boardPack
#assert_axioms marksCommit_is_boardCommit
#assert_axioms mem2_of_gate
#assert_axioms marksCode_decode_eqAt
#assert_axioms marksCode_eq_boardCode
#assert_axioms packCell_marksCode_eqAt
#assert_axioms marksAlpha_of_mem
#assert_axioms marksPack_pi_of_mem
#assert_axioms marks_range_mem
#assert_axioms marks_pack_mem
#assert_axioms marks_pi_mem
#assert_axioms marksAlpha_of_sat
#assert_axioms marksPack_pi_of_sat
#assert_axioms marks_forge_rejected
#assert_axioms marks_pack_congr_injective
#assert_axioms marks_pack_injective

/-! ## §9 — THE INTERFACE THE LATER MILESTONES CONSUME.

**M1 (the Leg C descriptor)** splices the emitted family in TWICE, at its own column/PI bases:

```lean
  marksCommitFamilyAt n marksInCell  marksInFelt  (AUTO_PI_BASE n + 2)          -- marksIn
  marksCommitFamilyAt n marksOutCell marksOutFelt (AUTO_PI_BASE n + 2 + feltCount n)  -- marksOut
```

and gets back, on its own `Satisfied2`, with membership discharged by `List.mem_append_*` into its
own constraint list (exactly the `AutomataflCommitRefine` §6 Leg-A pattern):

* `marksAlpha_of_mem` — the cells ARE indicator bits (from the emitted `{0,1}` gate);
* `marksPack_pi_of_mem` — the published window IS the pack of the decoded indicator;
* `marksDecodeAt n marksInCell (envAt t 0)` — the decode Leg C's refinement statement quantifies
  over, and `marksCode_eq_one_iff_mem` / `marksCode_eq_zero_iff_not_mem` to line it up against
  `roundStep`'s `rs.marks : List Coord` in the `moveLegalB` gate `¬inMarksFrm ∧ ¬inMarksTo`;
* `marksBoardOf` / `marksBoardOfRS` — the spec-side indicator of a `RoundState`, so
  `legC_sat_imp_roundAgainN`'s conclusion can be stated as an equality of indicators;
* `clashCoords_inBounds` — the fresh marks `cs` land on the `n²` grid, so the indicator is faithful.

**M5 (the RoundState window)** needs only two things from here:

* `marksWindowLanes n = feltCount n` — the lane count to widen `[board ‖ auto]` by (twice: `marksIn`
  and `marksOut`); `9` at `n = 11`, `#guard`ed;
* `marks_pack_injective` (trace form) / `marks_pack_congr_injective` (pure form) —
  **lane equality IS marks equality**, discharged by `pack_injective_modp`, with NO hash and NO
  chip-table soundness. This is what keeps the seam `C_k.OUT == C_{k+1}.IN` hash-free.

**M6 (Leg R off `marks = []`)** consumes `marks_window_eq_imp_mem_iff`: the carried window pins the
marked SET, which is all `MoveLegal`'s `m.frm ∉ marks ∧ m.to ∉ marks` reads.

**NOT provided here** (and not claimed): a Leg C descriptor, a golden on disk, an `EmitByName`
registration, the `csCell` / `marksOut = marksIn ∨ cs` gates, or any statement about `locked` /
`waiting` (those are not board-shaped — design doc §2.3). -/

end Dregg2.Circuit.Emit.AutomataflMarks
