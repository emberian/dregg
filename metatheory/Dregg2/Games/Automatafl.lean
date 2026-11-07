/-
# Dregg2.Games.Automatafl — the automatafl board-transition, modeled as a pure
transition + the load-bearing properties, + the AIR-refinement obligation the
verified board-transition circuit is emitted against.

automatafl (o1Labs / Corey Richardson, `~/dev/automatafl/logic/`) is an original
SIMULTANEOUS-MOVE cellular-automaton game on an N×N grid of particles
`{Repulsor, Attractor, Automaton, Vacuum}`.  ONE turn is:

    N secret moves  →  reveal together  →  conflict-resolve  →  apply-all
                    →  the Automaton ("Daemon") takes one autonomous step  →  win-check

This module is Phase E of the verified-game portfolio (docs/VERIFIED-GAME-PORTFOLIO.md):
model the rules as a pure `applyTurn : Board → List Move → Board`, PROVE the
load-bearing properties, and STATE the AIR-refinement contract
(`automatafl_air_refines_applyTurn`) — the game-level analogue of the
`evalSimpleCtx_*_iff` constraint twins (Dregg2/Exec/Program.lean) and the
`RotatedLayout.Legal` / `rotated184_legal` construction obligation
(Dregg2/Circuit/Emit/RotatedLayout.lean).

STANDALONE by design: no imports beyond the Lean prelude, so this type-checks even
when the shared metatheory tree is mid-broken by another terminal, and stays fast.
It touches NO crypto/floor Lean and NO cell/circuit/Rust.

────────────────────────────────────────────────────────────────────────────────
HONEST SCOPE — what is PROVEN vs STATED, and how faithfully phase (3) is modeled.

PROVEN, non-vacuously, over the pure model:
  (1) MOVE-VALIDITY is DECIDABLE — `MoveValid` (the `propose_move` predicate) has a
      `Decidable` instance and a Bool twin `moveValidB` with `moveValidB_iff`.
  (2) The AUTOMATON DECISION is TOTAL + DETERMINISTIC — `automatonMove` is a total
      function (`automatonMove_deterministic`: any two names for its value agree); its
      comparison is trichotomous so the priority cascade always resolves
      (`decisionCmp_total`); and the chosen offset is at most ONE cardinal step
      (`automatonOffset_bounded`), from which the Automaton stays in bounds
      (`automatonStep_preserves_inBounds`).
  (4) WIN-CHECK is decidable + a `Good`-style safety — `winner` is a decidable
      function and `winner_sound` proves a win can only fire when the Automaton is
      genuinely on a declared goal square (no spurious win); `applyTurn` preserves
      the in-bounds invariant of the Automaton (`applyTurn_preserves_inBounds`).

MODELED FAITHFULLY + termination PROVEN, determinism as functionality, fairness STATED:
  (3) RESOLUTION — `applyMoves` models occlusion (raycast with sources passable),
      chain-following through vacated squares (the "caterpillar"), dead-ends, and
      cycle stasis (2-cycles "always stay").  It is a TOTAL Lean function, so Lean's
      termination checker discharges TERMINATION by construction (`followChain`
      recurses on a strictly-decreasing fuel), and being a function it is
      deterministic given the move list.  The general FAIRNESS obligation
      (order-independence of the result, PHILOSOPHY.md §"Principle of Fairness") is
      STATED as `Fairness` / `applyMoves_fair_obligation` — proven for the empty/
      singleton case, deferred in general.  RESIDUALS (labeled, per the iterative
      method): full Tarjan-SCC >2-cycle *rotation* (modeled as stasis), the four
      `MergeResolutionMode`s, and multi-piece merge tie-breaks are not yet modeled.

STATED (the emitted-circuit contract, Lane-D-gated):
  `automatafl_air_refines_applyTurn` — the board-transition AIR admits
  `(old, moves, new)` IFF `new = applyTurn old moves`.  The AIR side is abstract
  (`BoardTransitionAIR`) now; `applyTurnAIR` witnesses the contract is satisfiable
  (non-vacuous), and the hand-authored Custom leaf discharges `Refines` later.
────────────────────────────────────────────────────────────────────────────────
-/

namespace Dregg2.Games.Automatafl

/-! ## §1  State: particles, coordinates, the board, moves -/

/-- The four particle kinds on the grid (`src/board.rs::Particle`). -/
inductive Particle
  | repulsor | attractor | automaton | vacuum
deriving DecidableEq, Repr

/-- Vacuum is the only pass-through-by-default particle. -/
def Particle.isVacuum : Particle → Bool
  | .vacuum => true
  | _       => false

/-- A grid coordinate (`src/types.rs::Coord`, here over `Nat`). -/
structure Coord where
  x : Nat
  y : Nat
deriving DecidableEq, Repr

/-- A player id (`Pid`). -/
abbrev Pid := Nat

/-- A revealed move: who moved a piece from `frm` to `to` (`src/types.rs::Move`). -/
structure Move where
  who : Pid
  frm : Coord
  to  : Coord
deriving DecidableEq, Repr

/-- The board.  `cells` is total (out-of-bounds reads route to vacuum via
`cellAt`); the Automaton's location is tracked in `automaton` AND registered as a
`.automaton` particle at that cell (so it occludes and can be raycast from).
`useColumnRule` selects the equal-priority Y-preference (README: default on). -/
structure Board where
  size          : Nat
  cells         : Coord → Particle
  automaton     : Coord
  conflictAt    : Coord → Bool := fun _ => false
  useColumnRule : Bool := true

/-- In-bounds test (`Board::inbounds`). -/
def Board.inBounds (b : Board) (c : Coord) : Prop := c.x < b.size ∧ c.y < b.size

instance (b : Board) (c : Coord) : Decidable (b.inBounds c) := by
  unfold Board.inBounds; exact inferInstance

/-- Particle at a cell, vacuum outside the board. -/
def Board.cellAt (b : Board) (c : Coord) : Particle :=
  if c.x < b.size ∧ c.y < b.size then b.cells c else .vacuum

/-- `Board::is_automaton`. -/
def Board.isAutomaton (b : Board) (c : Coord) : Prop := c = b.automaton
instance (b : Board) (c : Coord) : Decidable (b.isAutomaton c) := by
  unfold Board.isAutomaton; exact inferInstance

/-- `Board::is_conflict`. -/
def Board.isConflict (b : Board) (c : Coord) : Prop := b.conflictAt c = true
instance (b : Board) (c : Coord) : Decidable (b.isConflict c) := by
  unfold Board.isConflict; exact inferInstance

/-- Build a board from an association list of placed particles; the Automaton cell
is marked automatically.  Used for `#guard` witnesses. -/
def mkBoard (size : Nat) (placed : List (Coord × Particle)) (auto : Coord)
    (col : Bool := true) : Board where
  size := size
  automaton := auto
  useColumnRule := col
  cells := fun c =>
    if c = auto then .automaton
    else (placed.find? (fun p => p.1 = c)).elim .vacuum (·.2)

/-! ## §2  Property (1): move-validity is DECIDABLE

The `propose_move` predicate, minus the pure state-machine flow (round/lock state):
distinct, rook-aligned, both endpoints in-bounds, neither endpoint the Automaton,
neither endpoint conflicted.  (Source may be vacuum — optimistic chain moves.) -/

/-- The board-level validity predicate for a single move (`Game::propose_move`). -/
def MoveValid (b : Board) (m : Move) : Prop :=
  m.frm ≠ m.to
  ∧ (m.frm.x = m.to.x ∨ m.frm.y = m.to.y)
  ∧ b.inBounds m.frm ∧ b.inBounds m.to
  ∧ ¬ b.isAutomaton m.frm ∧ ¬ b.isAutomaton m.to
  ∧ ¬ b.isConflict m.frm ∧ ¬ b.isConflict m.to

/-- **PROPERTY (1).** Move validity is decidable. -/
instance moveValid_decidable (b : Board) (m : Move) : Decidable (MoveValid b m) := by
  unfold MoveValid; exact inferInstance

/-- The Bool evaluator twin of `MoveValid` (the shape the lowering teeth check). -/
def moveValidB (b : Board) (m : Move) : Bool := decide (MoveValid b m)

/-- **The decidability twin** (the `evalSimpleCtx_*_iff` idiom): the Bool check
accepts IFF the proposition holds.  Non-vacuous: `MoveValid` is a genuine
conjunction of the eight `propose_move` clauses, not `True`. -/
theorem moveValidB_iff (b : Board) (m : Move) : moveValidB b m = true ↔ MoveValid b m := by
  unfold moveValidB; exact decide_eq_true_iff

/-! ## §3  Property (2): the Automaton decision — TOTAL + DETERMINISTIC

The Daemon raycasts the four cardinals, scores each axis by priority
(`UnbalancedPair 30 > FromRepulsor 20 > TowardAttractor 10 > None 0`) with distance
tie-breaks, and moves AT MOST one step (`src/automaton.rs`). -/

/-- Cardinal directions. -/
inductive Dir | xp | xn | yp | yn deriving DecidableEq, Repr

/-- Unit step of a direction (`Delta::XP` etc.). -/
def Dir.delta : Dir → Int × Int
  | .xp => (1, 0) | .xn => (-1, 0) | .yp => (0, 1) | .yn => (0, -1)

/-- A raycast result: the first non-vacuum particle hit (or vacuum at the wall) and
the step index at which iteration terminated (`src/types.rs::Raycast`, `dist`). -/
structure Raycast where
  what : Particle
  dist : Nat
deriving Repr

/-- Fuel-bounded raycast (`Board::raycast`): step outward from `(x,y)` along
`(dx,dy)`; stop at the first non-vacuum particle (recording its distance) or when
the ray leaves the board (recording vacuum + the OOB step index).  Terminates
structurally on `fuel`; seeded with `fuel = size + 1` ⇒ the board boundary is
always reached. -/
def raycastFuel (b : Board) (x y dx dy : Int) (dist fuel : Nat) : Raycast :=
  match fuel with
  | 0        => { what := .vacuum, dist := dist }
  | fuel + 1 =>
    let x' := x + dx
    let y' := y + dy
    if 0 ≤ x' ∧ x' < b.size ∧ 0 ≤ y' ∧ y' < b.size then
      let p := b.cellAt ⟨x'.toNat, y'.toNat⟩
      if p.isVacuum then raycastFuel b x' y' dx dy (dist + 1) fuel
      else { what := p, dist := dist + 1 }
    else
      { what := .vacuum, dist := dist + 1 }

/-- Raycast from a coordinate along a direction. -/
def Board.raycast (b : Board) (from_ : Coord) (d : Dir) : Raycast :=
  raycastFuel b from_.x from_.y d.delta.1 d.delta.2 0 (b.size + 1)

/-- The Daemon's per-axis decision (`src/automaton.rs::AutomatonDecision`).  `pos`
= the Automaton would move in the positive direction of the axis. -/
inductive Decision
  | unbalancedPair (pos : Bool) (attDist repDist : Nat)
  | fromRepulsor   (pos : Bool) (repDist : Nat)
  | towardAttractor (pos : Bool) (attDist : Nat)
  | none
deriving Repr

/-- Priority number (`AutomatonDecision::priority`); higher wins. -/
def Decision.priority : Decision → Nat
  | .unbalancedPair .. => 30
  | .fromRepulsor ..   => 20
  | .towardAttractor .. => 10
  | .none              => 0

/-- The one-step offset a decision induces along `base` (`AutomatonDecision::delta`):
`+base` if `pos`, `-base` otherwise; `None` ⇒ no move. -/
def Decision.delta : Decision → Int × Int → Int × Int
  | .unbalancedPair p .. , base => if p then base else (-base.1, -base.2)
  | .fromRepulsor p .. ,   base => if p then base else (-base.1, -base.2)
  | .towardAttractor p .. , base => if p then base else (-base.1, -base.2)
  | .none,                 _    => (0, 0)

/-- `evaluate_axis` (`src/automaton.rs`): the faithful priority match.  `pos` is the
ray in the axis-positive direction, `neg` the negative.  Every `dist > 1` guard
ensures there is ≥1 empty square before the particle (room to step). -/
def evaluateAxis (pos neg : Raycast) : Decision :=
  match pos.what, neg.what with
  | .attractor, .repulsor =>
      if pos.dist > 1 then .unbalancedPair true pos.dist neg.dist else .none
  | .repulsor, .attractor =>
      if neg.dist > 1 then .unbalancedPair false neg.dist pos.dist else .none
  | .repulsor, .repulsor =>
      if pos.dist ≠ neg.dist then .fromRepulsor (pos.dist > neg.dist) (min pos.dist neg.dist)
      else .none
  | .repulsor, .vacuum =>
      if neg.dist > 1 then .fromRepulsor false pos.dist else .none
  | .vacuum, .repulsor =>
      if pos.dist > 1 then .fromRepulsor true neg.dist else .none
  | .attractor, .attractor =>
      if pos.dist ≠ neg.dist ∧ min pos.dist neg.dist > 1 then
        .towardAttractor (pos.dist < neg.dist) (min pos.dist neg.dist)
      else .none
  | .attractor, .vacuum =>
      if pos.dist > 1 then .towardAttractor true pos.dist else .none
  | .vacuum, .attractor =>
      if neg.dist > 1 then .towardAttractor false neg.dist else .none
  | _, _ => .none

/-- Distance tie-break: SMALLER distance ranks GREATER (`chose_smaller_distance` =
`cmp.reverse`). -/
def revCmp (a b : Nat) : Ordering := (compare a b).swap

/-- The intra-priority tie-break (`src/automaton.rs::tiebreaker`). -/
def tiebreak : Decision → Decision → Ordering
  | .unbalancedPair _ a1 r1, .unbalancedPair _ a2 r2 => (revCmp a1 a2).then (revCmp r1 r2)
  | .fromRepulsor _ r1,      .fromRepulsor _ r2      => revCmp r1 r2
  | .towardAttractor _ a1,   .towardAttractor _ a2   => revCmp a1 a2
  | _, _ => .eq

/-- The full decision order (`impl Ord for AutomatonDecision`): priority first, then
the tie-break. -/
def decisionCmp (a b : Decision) : Ordering :=
  (compare a.priority b.priority).then (tiebreak a b)

/-- **The comparison is TOTAL (trichotomous)** — every pair of decisions compares to
exactly one of `lt/eq/gt`, so the priority cascade in `automatonOffset` ALWAYS
resolves to a single branch (this is the "ties resolve" content of property (2)). -/
theorem decisionCmp_total (a b : Decision) :
    decisionCmp a b = .lt ∨ decisionCmp a b = .eq ∨ decisionCmp a b = .gt := by
  cases decisionCmp a b <;> simp

/-- Select the offset from the two axis decisions and the column-rule flag (a single
flat match: winner along its axis, or on a tie the column rule (prefer Y) / freeze). -/
def chooseOffset (xDec yDec : Decision) (col : Bool) : Int × Int :=
  match decisionCmp xDec yDec, col with
  | .gt, _     => xDec.delta (1, 0)
  | .lt, _     => yDec.delta (0, 1)
  | .eq, true  => yDec.delta (0, 1)
  | .eq, false => (0, 0)

/-- The Daemon's chosen offset (`Game::automaton_move`): compare the two axis
decisions; move along the winner; on a tie apply the column rule.  TOTAL. -/
def automatonOffset (b : Board) : Int × Int :=
  chooseOffset
    (evaluateAxis (b.raycast b.automaton .xp) (b.raycast b.automaton .xn))
    (evaluateAxis (b.raycast b.automaton .yp) (b.raycast b.automaton .yn))
    b.useColumnRule

/-- A `delta` along a unit base is one of the five cardinal offsets (incl. zero). -/
theorem Decision.delta_mem (d : Decision) (base : Int × Int)
    (hb : base = (1, 0) ∨ base = (0, 1)) :
    d.delta base = (1, 0) ∨ d.delta base = (-1, 0) ∨ d.delta base = (0, 1)
      ∨ d.delta base = (0, -1) ∨ d.delta base = (0, 0) := by
  rcases hb with hb | hb <;> subst hb <;>
    cases d <;> simp only [Decision.delta] <;>
    first
    | decide
    | (split <;> decide)

/-- The selected offset is one of the five cardinal offsets (incl. zero). -/
theorem chooseOffset_mem (x y : Decision) (col : Bool) :
    chooseOffset x y col = (1, 0) ∨ chooseOffset x y col = (-1, 0) ∨ chooseOffset x y col = (0, 1)
      ∨ chooseOffset x y col = (0, -1) ∨ chooseOffset x y col = (0, 0) := by
  unfold chooseOffset
  split <;>
    first
      | exact Decision.delta_mem _ _ (Or.inl rfl)
      | exact Decision.delta_mem _ _ (Or.inr rfl)
      | exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

/-- The chosen offset is one of the five cardinal offsets (incl. zero). -/
theorem automatonOffset_cases (b : Board) :
    automatonOffset b = (1, 0) ∨ automatonOffset b = (-1, 0) ∨ automatonOffset b = (0, 1)
      ∨ automatonOffset b = (0, -1) ∨ automatonOffset b = (0, 0) :=
  chooseOffset_mem _ _ _

/-- **PROPERTY (2), the load-bearing content.** The Automaton moves AT MOST one step
in a cardinal direction: the chosen offset has Manhattan length ≤ 1. -/
theorem automatonOffset_bounded (b : Board) :
    (automatonOffset b).1.natAbs + (automatonOffset b).2.natAbs ≤ 1 := by
  rcases automatonOffset_cases b with h | h | h | h | h <;> rw [h] <;> decide

/-- Relocate the Automaton onto `nc`, clearing its old cell to vacuum. -/
def stepTo (b : Board) (nc : Coord) : Board :=
  { b with
    automaton := nc,
    cells := fun c => if c = nc then .automaton
                      else if c = b.automaton then .vacuum
                      else b.cells c }

/-- The Automaton step (`Game::update_automaton` + `Board::do_move`): move onto the
one-step target IFF it is in bounds, a genuine move, and vacuum ("the Automaton can
never move into an occupied square").  Otherwise the board is unchanged. -/
def automatonStep (b : Board) : Board :=
  let off := automatonOffset b
  if 0 ≤ (b.automaton.x : Int) + off.1 ∧ (b.automaton.x : Int) + off.1 < b.size
      ∧ 0 ≤ (b.automaton.y : Int) + off.2 ∧ (b.automaton.y : Int) + off.2 < b.size
      ∧ (off.1 ≠ 0 ∨ off.2 ≠ 0)
      ∧ b.cellAt ⟨((b.automaton.x : Int) + off.1).toNat,
                  ((b.automaton.y : Int) + off.2).toNat⟩ = .vacuum then
    stepTo b ⟨((b.automaton.x : Int) + off.1).toNat, ((b.automaton.y : Int) + off.2).toNat⟩
  else b

/-- The step never changes the board size. -/
theorem automatonStep_size (b : Board) : (automatonStep b).size = b.size := by
  simp only [automatonStep]; split <;> rfl

/-- **PROPERTY (2), determinism.** The next Automaton location is uniquely determined:
`automatonMove` is a TOTAL function, so any two names for its value coincide. -/
def automatonMove (b : Board) : Coord := (automatonStep b).automaton

theorem automatonMove_deterministic (b : Board) (c₁ c₂ : Coord)
    (h₁ : c₁ = automatonMove b) (h₂ : c₂ = automatonMove b) : c₁ = c₂ :=
  h₁.trans h₂.symm

/-- **PROPERTY (2), safety.** The Automaton stays in bounds across its step: the
guard only relocates it onto an in-bounds vacuum cell. -/
theorem automatonStep_preserves_inBounds (b : Board)
    (hb : b.inBounds b.automaton) :
    (automatonStep b).inBounds (automatonStep b).automaton := by
  unfold Board.inBounds
  rw [automatonStep_size]
  simp only [automatonStep]
  split
  · rename_i h
    obtain ⟨hx0, hxs, hy0, hys, _, _⟩ := h
    refine ⟨?_, ?_⟩
    · simp only [stepTo]; omega
    · simp only [stepTo]; omega
  · exact hb

/-! ## §4  Property (3): conflict-resolution + apply-all (SCC resolution)

Modeled faithfully for occlusion / chains / dead-ends / cycle-stasis; TERMINATION is
discharged by Lean's checker (fuel-decreasing recursion); determinism = being a
function; general FAIRNESS is STATED (`Fairness`). -/

/-- The interior coordinates strictly between two axis-aligned endpoints (exclusive),
for the occlusion check. -/
def interior (frm to : Coord) : List Coord :=
  if frm.x = to.x then
    let lo := min frm.y to.y
    let hi := max frm.y to.y
    (List.range (hi - lo - 1)).map (fun k => ⟨frm.x, lo + 1 + k⟩)
  else
    let lo := min frm.x to.x
    let hi := max frm.x to.x
    (List.range (hi - lo - 1)).map (fun k => ⟨lo + 1 + k, frm.y⟩)

/-- "at least two distinct elements" (order-free conflict detector). -/
def hasTwoDistinct {α} [DecidableEq α] (l : List α) : Bool :=
  l.any (fun a => l.any (fun c => a ≠ c))

/-- Source conflict: one source, ≥2 distinct destinations (`resolve_conflicts`, fork). -/
def frmConflict (ms : List Move) (m : Move) : Bool :=
  hasTwoDistinct ((ms.filter (fun m' => m'.frm = m.frm)).map (·.to))

/-- Destination conflict: one destination, ≥2 distinct NON-VACUUM sources
(`resolve_conflicts`, collision; `DetectAndConflict` mode). -/
def toConflict (b : Board) (ms : List Move) (m : Move) : Bool :=
  hasTwoDistinct
    ((ms.filter (fun m' => m'.to = m.to ∧ ¬ (b.cellAt m'.frm).isVacuum)).map (·.frm))

/-- Conflict resolution (`Game::resolve_conflicts`): drop every move that touches a
conflicted source or destination.  Identical `(src,dst)` moves are NOT a conflict
(they share a single destination, so `hasTwoDistinct` is false). -/
def conflictResolve (b : Board) (ms : List Move) : List Move :=
  ms.filter (fun m => ¬ frmConflict ms m ∧ ¬ toConflict b ms m)

/-- A move is occluded if some interior cell holds a non-vacuum particle that is NOT
itself a moving source (sources are `mark_passable`-d). -/
def occluded (b : Board) (srcs : List Coord) (m : Move) : Bool :=
  (interior m.frm m.to).any
    (fun c => ¬ (b.cellAt c).isVacuum ∧ ¬ srcs.contains c)

/-- The move graph as a partial function: a source's (unique, post-conflict)
destination among the non-occluded moves. -/
def nextOf (b : Board) (moved : List Move) (srcs : List Coord) (c : Coord) : Option Coord :=
  (moved.find? (fun m => m.frm = c ∧ ¬ occluded b srcs m)).map (·.to)

/-- Chain-follow (`apply_moves` Phase 4): from a piece's source, follow move edges
through vacated squares; land on the next PIECE-source (the "caterpillar") ONLY when
that piece's own move EXECUTES, stop at a dead-end, or stay on a detected cycle
(2-cycle "always stay", the conservative model for >2-cycles).
Terminates: `fuel` strictly decreases.

**THE AUTHOR'S RULE** (ember, verbatim): *"designating a move to an occupied square is
fine, it just fails to execute, it doesn't generate a conflict and shouldn't."*  So a
move whose destination is held by a piece that does NOT vacate FAILS TO EXECUTE: the
mover stays on its own source and keeps its particle.  It is NOT a conflict — nothing
is fork/collide-flagged, `conflictResolve` is untouched.

**DEFECT #8, FIXED HERE.**  This branch used to read `else if pieceSrcs.contains nxt
then nxt` — it asked only "is `nxt` a source holding a piece?", never whether that
piece actually LEAVES.  With the leader occluded (`nextC nxt = none`, so it stays) the
follower still landed on `nxt`; both journeys then had the same destination,
`journeys.find?` awarded the cell to the leader (source order), and the follower's
source was cleared with its particle appearing NOWHERE.  **The reference DESTROYED a
piece.**  The `(nextC nxt).isSome` guard is the fix: no edge out of `nxt` ⇒ the leader
cannot move ⇒ the follower's move fails ⇒ it returns `start`.

**LABELLED RESIDUAL (the other half of the class, NOT fixed here).**  `pieceSrcs` lists
only sources that carry; a destination held by a piece that is not a MOVING SOURCE at
all is still landed on and still overwritten.  Closing that needs the OCCUPANCY of the
board (not just the source list) inside the chain, and it makes the emitted descriptor
DISAGREE with the reference at every board size — see
`AutomataflConserve.landsOnStayer_witness` for the machine-checked witness and
`Dregg2.Circuit.Emit.AutomataflResolveCapstone` §6 for the descriptor side. -/
def followChain (nextC : Coord → Option Coord) (pieceSrcs : List Coord)
    (start : Coord) (visited : List Coord) (fuel : Nat) : Coord :=
  match fuel with
  | 0        => start
  | fuel + 1 =>
    match nextC start with
    | .none     => start
    | .some nxt =>
      if visited.contains nxt then start
      else if pieceSrcs.contains nxt then (if (nextC nxt).isSome then nxt else start)
      else match nextC nxt with
        | .none   => nxt
        | .some _ => followChain nextC pieceSrcs nxt (start :: visited) fuel

/-- **THE INVARIANT DEFECT #8's FIX EARNS, at arbitrary board size and move count.**
A chain never lands on a carrying source that has NO outgoing edge.  Equivalently: if
the follower moves at all, the piece it lands on had a move of its own to execute.
This is the general (`n`-free, `m`-free) statement of the author's rule for the branch
`followChain` controls; the pre-fix definition REFUTES it (`AutomataflConserve`). -/
theorem followChain_landing_has_edge (nextC : Coord → Option Coord) (pieceSrcs : List Coord) :
    ∀ (fuel : Nat) (start : Coord) (visited : List Coord),
      followChain nextC pieceSrcs start visited fuel ≠ start →
      pieceSrcs.contains (followChain nextC pieceSrcs start visited fuel) = true →
      (nextC (followChain nextC pieceSrcs start visited fuel)).isSome = true := by
  intro fuel
  induction fuel with
  | zero => intro start visited h _; exact absurd rfl h
  | succ f ih =>
    intro start visited
    rw [followChain]
    cases hstart : nextC start with
    | none => intro h _; exact absurd rfl h
    | some nxt =>
      dsimp only
      by_cases hv : visited.contains nxt = true
      · rw [if_pos hv]; intro h _; exact absurd rfl h
      · rw [if_neg hv]
        by_cases hp : pieceSrcs.contains nxt = true
        · rw [if_pos hp]
          by_cases hnn : (nextC nxt).isSome = true
          · rw [if_pos hnn]; intro _ _; exact hnn
          · rw [if_neg hnn]; intro h _; exact absurd rfl h
        · rw [if_neg hp]
          cases hnn : nextC nxt with
          | none => intro _ h; exact absurd h hp
          | some w =>
            dsimp only
            intro _ hps
            by_cases hd : followChain nextC pieceSrcs nxt (start :: visited) f = nxt
            · rw [hd, hnn]; rfl
            · exact ih nxt (start :: visited) hd hps

/-- A resolved journey: a piece carried from `src` to `dest`. -/
structure Journey where
  src      : Coord
  dest     : Coord
  particle : Particle
deriving Repr

/-- **PROPERTY (3), the resolution function** (`Game::apply_moves`, faithful subset).
Builds the non-occluded move graph, computes each piece's destination by chain-follow,
and rewrites the board: sources cleared, pieces placed at their destinations.
TOTAL ⇒ TERMINATES by construction; a function ⇒ deterministic given `moves`. -/
def applyMoves (b : Board) (moves : List Move) : Board :=
  let srcs      := moves.map (·.frm)
  let nextC     := nextOf b moves srcs
  -- sources actually carrying a piece at turn start
  let pieceSrcs := srcs.filter (fun c => ¬ (b.cellAt c).isVacuum)
  let fuel      := moves.length + 1
  let journeys  : List Journey :=
    pieceSrcs.map (fun s =>
      { src := s, dest := followChain nextC pieceSrcs s [] fuel, particle := b.cellAt s })
  let clearedSrc (c : Coord) : Bool := pieceSrcs.contains c
  { b with
    conflictAt := fun _ => false,
    cells := fun c =>
      match journeys.find? (fun j => j.dest = c) with
      | .some j => j.particle
      | .none   => if clearedSrc c then .vacuum else b.cellAt c }

/-- **PROPERTY (3), determinism-as-functionality** — trivial but recorded: the
resolution is a function, so equal inputs give equal outputs. -/
theorem applyMoves_deterministic (b : Board) (ms : List Move) :
    applyMoves b ms = applyMoves b ms := rfl

/-- **PROPERTY (3), the STATED fairness obligation** (PHILOSOPHY.md, "Principle of
Fairness": move success and order are independent of any ordering on players or on
the move list — the resolution is PERMUTATION-INVARIANT).  Stated as a named `Prop`;
it is the deferred residual (general permutation-invariance needs the full SCC
decomposition + a canonical merge order).  The §8 witnesses (pinned as named theorems in
`AutomataflFixtures.lean`) exhibit concrete real resolutions (single move, chain,
fork-conflict, full turn) for non-vacuity. -/
def FairnessObligation : Prop :=
  ∀ (b : Board) (ms₁ ms₂ : List Move), ms₁.Perm ms₂ →
    ∀ c : Coord, (applyMoves b ms₁).cellAt c = (applyMoves b ms₂).cellAt c

/-! ## §5  Property (4): win-check — decidable + `Good`-style safety -/

/-- Win check (`try_complete_round`): the owner of the goal the Automaton now sits
on, if any.  Direct recursion for a clean safety proof. -/
def winnerAux (a : Coord) : List (Coord × Pid) → Option Pid
  | []            => .none
  | (c, p) :: rest => if c = a then .some p else winnerAux a rest

def winner (b : Board) (goals : List (Coord × Pid)) : Option Pid :=
  winnerAux b.automaton goals

/-- Win is decidable (an `Option`; `hasWon` is its `isSome`). -/
def hasWon (b : Board) (goals : List (Coord × Pid)) : Bool := (winner b goals).isSome

/-- **PROPERTY (4), the `Good`-style safety.** A win can only fire when the Automaton
is genuinely on a declared goal square owned by the winner — no spurious win. -/
theorem winner_sound (b : Board) (goals : List (Coord × Pid)) (p : Pid)
    (h : winner b goals = .some p) :
    ∃ c, (c, p) ∈ goals ∧ b.automaton = c := by
  unfold winner at h
  induction goals with
  | nil => simp [winnerAux] at h
  | cons g gs ih =>
    obtain ⟨c, q⟩ := g
    simp only [winnerAux] at h
    by_cases hc : c = b.automaton
    · rw [if_pos hc] at h
      injection h with hq
      subst hq
      exact ⟨c, List.mem_cons_self, hc.symm⟩
    · rw [if_neg hc] at h
      obtain ⟨c', hmem, ha⟩ := ih h
      exact ⟨c', List.mem_cons_of_mem _ hmem, ha⟩

/-! ## §6  The pure turn transition -/

/-- **THE PURE TRANSITION** (`Game::try_complete_round`): validity-filter →
conflict-resolve → apply-all → Automaton step.  (Win-check is a read-only predicate
`winner` over the resulting board, not a mutation.) -/
def applyTurn (b : Board) (ms : List Move) : Board :=
  automatonStep (applyMoves b (conflictResolve b (ms.filter (moveValidB b))))

/-- **`resolveMid` — THE `old → mid` HALF OF THE TURN, NAMED.**

`applyTurn` is the composition of two halves, and the two Lean-authored automatafl AIRs refine one
half each: `AutomataflResolveEmit` (Leg R) adjudicates `old → mid` and `AutomataflStepEmit` (Leg A)
runs `mid → new`. Until now only the second half had a name (`automatonStep`), so Leg R's capstone
had to spell its target out as an inline composition. This is that composition, named — the
validity filter, the conflict resolution, and the (occlusion-aware, chain-following) rewrite:

    resolveMid b ms = applyMoves b (conflictResolve b (ms.filter (moveValidB b)))

It is DEFINITIONALLY the inner term of `applyTurn`; `applyTurn_factors` records that, so the two
capstones compose: Leg R gives `boardDecode mid = resolveMid (boardDecode old) ms`, Leg A gives
`boardDecode new = automatonStep (boardDecode mid)`, and the factorization closes them into
`applyTurn`. `applyTurn`'s semantics are UNCHANGED — this def is introduced by `rfl`. -/
def resolveMid (b : Board) (ms : List Move) : Board :=
  applyMoves b (conflictResolve b (ms.filter (moveValidB b)))

/-- **THE FACTORIZATION.** `applyTurn = automatonStep ∘ resolveMid` — the seam at which the Leg R
and Leg A refinements meet. Definitional, so rewriting with it never changes what is proven. -/
theorem applyTurn_factors (b : Board) (ms : List Move) :
    applyTurn b ms = automatonStep (resolveMid b ms) := rfl

/-- `resolveMid`, like `applyMoves`, never relocates the Automaton. -/
theorem resolveMid_automaton (b : Board) (ms : List Move) :
    (resolveMid b ms).automaton = b.automaton := rfl

/-- `applyMoves` never relocates the Automaton (validity forbids `to = automaton`;
sources are never the Automaton cell), so its location field is untouched. -/
theorem applyMoves_automaton (b : Board) (ms : List Move) :
    (applyMoves b ms).automaton = b.automaton := rfl

/-- **PROPERTY (4), the invariant preserved across the whole turn.** If the Automaton
starts in bounds it ends in bounds — the `Good` safety invariant of `applyTurn`. -/
theorem applyTurn_preserves_inBounds (b : Board) (ms : List Move)
    (hb : b.inBounds b.automaton) :
    (applyTurn b ms).inBounds (applyTurn b ms).automaton := by
  unfold applyTurn
  apply automatonStep_preserves_inBounds
  rw [applyMoves_automaton]
  exact hb

/-! ## §7  The AIR-refinement obligation (STATED — the emitted-circuit contract)

The game-level analogue of the `evalSimpleCtx_*_iff` constraint twins and the
`RotatedLayout.Legal` construction obligation.  The board-transition AIR is abstract
now; the hand-authored Custom leaf (Lane-D-gated) discharges `Refines` later. -/

/-- An abstract board-transition circuit: its arithmetization admits triples
`(old_board, moves, new_board)`. -/
structure BoardTransitionAIR where
  admits : Board → List Move → Board → Prop

/-- **THE CONTRACT** the verified circuit is emitted against: the AIR admits
`(b, ms, nb)` IFF `nb` is exactly the pure transition applied. -/
def BoardTransitionAIR.Refines (air : BoardTransitionAIR) : Prop :=
  ∀ b ms nb, air.admits b ms nb ↔ nb = applyTurn b ms

/-- The reference realization — the AIR whose admission IS `applyTurn`.  It witnesses
`Refines` is SATISFIABLE (the obligation is non-vacuous, exactly as `rotated184_legal`
witnesses `Legal` is inhabited). -/
def applyTurnAIR : BoardTransitionAIR where
  admits := fun b ms nb => nb = applyTurn b ms

theorem applyTurnAIR_refines : applyTurnAIR.Refines := fun _ _ _ => Iff.rfl

/-- **`automatafl_air_refines_applyTurn` — THE STATED AIR-REFINEMENT OBLIGATION.**
Any board-transition AIR that satisfies the emitted-circuit contract `Refines`
accepts `(old, moves, new)` exactly when `new = applyTurn old moves`.  The Lane-D
Custom leaf supplies the `air.Refines` witness (its construction + proof are
deferred); `applyTurnAIR_refines` shows the contract is inhabited today. -/
theorem automatafl_air_refines_applyTurn
    (air : BoardTransitionAIR) (hair : air.Refines)
    (b : Board) (ms : List Move) (nb : Board) :
    air.admits b ms nb ↔ nb = applyTurn b ms :=
  hair b ms nb

/-! ## §8  Non-vacuity witnesses — real board transitions

A 5×5 board, Automaton at (2,2), an attractor two north at (2,4).  The Daemon
should step one square toward it, to (2,3).

⚑ **THE WITNESSES NO LONGER EVALUATE IN THIS MODULE (2026-08-08).** This module is in the
`Dregg2.FFI` closure — the crypto archive's build — and the 18 `#guard`s that used to run at
elaboration here made every game-fixture regression a hard failure of every Rust proving
target. The witness boards and moves STAY here; the EVALUATION — each fact as a NAMED theorem
per GUARD-DISCIPLINE, `native_decide` + `#assert_compiled` — lives in
`AutomataflFixtures.lean`, rooted in the central guard library: a plain `lake build` still runs
every pin, and a stale fixture reds the guard library instead of the archive. Every pinned
expression mentions only PUBLIC names, so the pins moved verbatim. -/

/-- Automaton at (2,2); attractor at (2,4); everything else vacuum. -/
def demoBoard : Board :=
  mkBoard 5 [(⟨2, 4⟩, .attractor)] ⟨2, 2⟩

/-- A repulsor board: repulsor one step south at (2,1) with empty space north — the
Daemon flees north (FromRepulsor). -/
def repBoard : Board := mkBoard 5 [(⟨2, 1⟩, .repulsor)] ⟨2, 2⟩

/-- A move-resolution witness: player moves the attractor from (0,0) to (0,3) on an
otherwise-empty 5×5 board (Automaton parked in a corner out of the way). -/
def moveBoard : Board := mkBoard 5 [(⟨0, 0⟩, .attractor)] ⟨4, 4⟩
def demoMove : Move := { who := 0, frm := ⟨0, 0⟩, to := ⟨0, 3⟩ }

-- Conflict detection witnesses: two distinct destinations from one source = a fork conflict.
def forkA : Move := { who := 0, frm := ⟨0, 0⟩, to := ⟨0, 3⟩ }
def forkB : Move := { who := 1, frm := ⟨0, 0⟩, to := ⟨3, 0⟩ }

/-! ## §8b  CELL-WISE CONGRUENCE for the Automaton step — the SEAM LEMMA.

The two Lean-authored automatafl AIRs meet at the mid board, and what the fold-level `mid_root`
public input enforces is a CELL-WISE agreement (`∀ in-bounds c, b₁.cellAt c = b₂.cellAt c`), NOT a
`Board` equality: `Board` carries function fields (`cells`, `conflictAt`), so two boards that agree
everywhere a player can observe are still not `Eq` without funext plus agreement OFF the board.
Composing the two capstones therefore needs `automatonStep` to RESPECT that agreement. It does, and
these lemmas prove it: `automatonStep` reads the board only through `size`, `automaton`,
`useColumnRule` and `cellAt` — `raycastFuel` guards every read with the in-bounds test, and `stepTo`
rewrites cells positionally. -/

/-- The raycast reads the board only at IN-BOUNDS cells (its own guard), so it cannot distinguish
two boards of equal size that agree on `cellAt` in bounds. -/
theorem raycastFuel_congr (b₁ b₂ : Board) (hs : b₁.size = b₂.size)
    (hc : ∀ c : Coord, c.x < b₁.size → c.y < b₁.size → b₁.cellAt c = b₂.cellAt c)
    (dx dy : Int) : ∀ (fuel : Nat) (x y : Int) (dist : Nat),
      raycastFuel b₁ x y dx dy dist fuel = raycastFuel b₂ x y dx dy dist fuel := by
  intro fuel
  induction fuel with
  | zero => intro x y dist; rfl
  | succ f ih =>
    intro x y dist
    simp only [raycastFuel, hs]
    by_cases hb : 0 ≤ x + dx ∧ x + dx < (b₂.size : Int) ∧ 0 ≤ y + dy ∧ y + dy < (b₂.size : Int)
    · rw [if_pos hb, if_pos hb]
      have hx : ((x + dx).toNat) < b₁.size := by
        have := hb.2.1; omega
      have hy : ((y + dy).toNat) < b₁.size := by
        have := hb.2.2.2; omega
      have hcell : b₁.cellAt ⟨(x + dx).toNat, (y + dy).toNat⟩
          = b₂.cellAt ⟨(x + dx).toNat, (y + dy).toNat⟩ := hc _ hx hy
      simp only [hcell]
      split
      · exact ih _ _ _
      · rfl
    · rw [if_neg hb, if_neg hb]

/-- The four cardinal rays agree. -/
theorem raycast_congr (b₁ b₂ : Board) (hs : b₁.size = b₂.size)
    (hc : ∀ c : Coord, c.x < b₁.size → c.y < b₁.size → b₁.cellAt c = b₂.cellAt c)
    (from_ : Coord) (d : Dir) : b₁.raycast from_ d = b₂.raycast from_ d := by
  simp only [Board.raycast, hs]
  exact raycastFuel_congr b₁ b₂ hs hc _ _ _ _ _ _

/-- Hence the Daemon's chosen offset agrees. -/
theorem automatonOffset_congr (b₁ b₂ : Board) (hs : b₁.size = b₂.size)
    (ha : b₁.automaton = b₂.automaton) (hu : b₁.useColumnRule = b₂.useColumnRule)
    (hc : ∀ c : Coord, c.x < b₁.size → c.y < b₁.size → b₁.cellAt c = b₂.cellAt c) :
    automatonOffset b₁ = automatonOffset b₂ := by
  simp only [automatonOffset, ha, hu, raycast_congr b₁ b₂ hs hc]

/-- **THE SEAM LEMMA.** Two boards agreeing on size, automaton, column rule and every IN-BOUNDS cell
step to boards that agree on every in-bounds cell (and on size and automaton). This is exactly the
congruence the whole-turn composition needs, because the Leg R → Leg A seam is a cell-wise
agreement, not a `Board` equality. -/
theorem automatonStep_congr (b₁ b₂ : Board) (hs : b₁.size = b₂.size)
    (ha : b₁.automaton = b₂.automaton) (hu : b₁.useColumnRule = b₂.useColumnRule)
    (hc : ∀ c : Coord, c.x < b₁.size → c.y < b₁.size → b₁.cellAt c = b₂.cellAt c) :
    (automatonStep b₁).size = (automatonStep b₂).size
    ∧ (automatonStep b₁).automaton = (automatonStep b₂).automaton
    ∧ ∀ c : Coord, c.x < b₁.size → c.y < b₁.size →
        (automatonStep b₁).cellAt c = (automatonStep b₂).cellAt c := by
  have hoff := automatonOffset_congr b₁ b₂ hs ha hu hc
  -- after this rewrite the two guards differ ONLY in `b₁.cellAt` vs `b₂.cellAt` at the SAME target
  simp only [automatonStep, hoff, hs, ha]
  have hcellNC : ∀ nx ny : Int, 0 ≤ nx → nx < (b₂.size : Int) → 0 ≤ ny → ny < (b₂.size : Int) →
      b₁.cellAt ⟨nx.toNat, ny.toNat⟩ = b₂.cellAt ⟨nx.toNat, ny.toNat⟩ := by
    intro nx ny h3 h1 h4 h2
    exact hc ⟨nx.toNat, ny.toNat⟩ (by simp only [hs]; omega) (by simp only [hs]; omega)
  by_cases hg : 0 ≤ (b₂.automaton.x : Int) + (automatonOffset b₂).1
      ∧ (b₂.automaton.x : Int) + (automatonOffset b₂).1 < (b₂.size : Int)
      ∧ 0 ≤ (b₂.automaton.y : Int) + (automatonOffset b₂).2
      ∧ (b₂.automaton.y : Int) + (automatonOffset b₂).2 < (b₂.size : Int)
      ∧ ((automatonOffset b₂).1 ≠ 0 ∨ (automatonOffset b₂).2 ≠ 0)
      ∧ b₂.cellAt ⟨((b₂.automaton.x : Int) + (automatonOffset b₂).1).toNat,
                   ((b₂.automaton.y : Int) + (automatonOffset b₂).2).toNat⟩ = .vacuum
  · have hg₁ : 0 ≤ (b₂.automaton.x : Int) + (automatonOffset b₂).1
        ∧ (b₂.automaton.x : Int) + (automatonOffset b₂).1 < (b₂.size : Int)
        ∧ 0 ≤ (b₂.automaton.y : Int) + (automatonOffset b₂).2
        ∧ (b₂.automaton.y : Int) + (automatonOffset b₂).2 < (b₂.size : Int)
        ∧ ((automatonOffset b₂).1 ≠ 0 ∨ (automatonOffset b₂).2 ≠ 0)
        ∧ b₁.cellAt ⟨((b₂.automaton.x : Int) + (automatonOffset b₂).1).toNat,
                     ((b₂.automaton.y : Int) + (automatonOffset b₂).2).toNat⟩ = .vacuum :=
      ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1,
        by rw [hcellNC _ _ hg.1 hg.2.1 hg.2.2.1 hg.2.2.2.1]; exact hg.2.2.2.2.2⟩
    rw [if_pos hg₁, if_pos hg]
    refine ⟨by simp only [stepTo, hs], by simp only [stepTo], ?_⟩
    intro c hcx' hcy'
    have hcx : c.x < b₁.size := hs ▸ hcx'
    have hcy : c.y < b₁.size := hs ▸ hcy'
    have hraw : b₁.cells c = b₂.cells c := by
      have h := hc c hcx hcy
      simp only [Board.cellAt, if_pos (⟨hcx, hcy⟩ : c.x < b₁.size ∧ c.y < b₁.size),
        if_pos (⟨hcx', hcy'⟩ : c.x < b₂.size ∧ c.y < b₂.size)] at h
      exact h
    simp only [stepTo, Board.cellAt, hs, ha, hcx', hcy', and_self, if_true]
    split
    · rfl
    · split
      · rfl
      · exact hraw
  · have hg₁ : ¬ (0 ≤ (b₂.automaton.x : Int) + (automatonOffset b₂).1
        ∧ (b₂.automaton.x : Int) + (automatonOffset b₂).1 < (b₂.size : Int)
        ∧ 0 ≤ (b₂.automaton.y : Int) + (automatonOffset b₂).2
        ∧ (b₂.automaton.y : Int) + (automatonOffset b₂).2 < (b₂.size : Int)
        ∧ ((automatonOffset b₂).1 ≠ 0 ∨ (automatonOffset b₂).2 ≠ 0)
        ∧ b₁.cellAt ⟨((b₂.automaton.x : Int) + (automatonOffset b₂).1).toNat,
                     ((b₂.automaton.y : Int) + (automatonOffset b₂).2).toNat⟩ = .vacuum) := by
      intro h
      exact hg ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
        by rw [← hcellNC _ _ h.1 h.2.1 h.2.2.1 h.2.2.2.1]; exact h.2.2.2.2.2⟩
    rw [if_neg hg₁, if_neg hg]
    exact ⟨hs, ha, fun c hx hy => hc c (hs ▸ hx) (hs ▸ hy)⟩


/-! ## §8c  THE REFERENCE UNFOLDING of `applyMoves bd [ma, mb]`, per cell.

Leg R's per-cell circuit gate is an arithmetic polynomial over indicator products; the reference is
a `filter`/`map`/`find?` pipeline. These four lemmas evaluate that pipeline at a literal 2-element
move list, in the FOUR shapes of `pieceSrcs` (which sources actually carry a piece at turn start),
into the same per-cell if-chain the gate computes — landing particle first, then the other landing,
then vacuum on a cleared source, else the old cell. This is the reference half of the Leg R
capstone's bookkeeping layer. -/

/-- `applyMoves` never resizes the board. -/
theorem applyMoves_size (bd : Board) (ms : List Move) : (applyMoves bd ms).size = bd.size := rfl

/-- BOTH sources carry: two journeys, `find?` scanned in list order (A's landing wins a shared
destination — exactly the gate's `B`-before-`D` priority). -/
theorem applyMoves_cell_TT (bd : Board) (ma mb : Move) (c : Coord)
    (hx : c.x < bd.size) (hy : c.y < bd.size)
    (ha : (bd.cellAt ma.frm).isVacuum = false) (hb : (bd.cellAt mb.frm).isVacuum = false) :
    (applyMoves bd [ma, mb]).cellAt c
      = (if followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) [ma.frm, mb.frm] ma.frm [] 3 = c
         then bd.cellAt ma.frm
         else if followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) [ma.frm, mb.frm] mb.frm [] 3 = c
         then bd.cellAt mb.frm
         else if c = ma.frm ∨ c = mb.frm then Particle.vacuum else bd.cellAt c) := by
  rw [Board.cellAt, applyMoves_size, if_pos (⟨hx, hy⟩ : c.x < bd.size ∧ c.y < bd.size)]
  simp only [applyMoves, List.map, List.filter_cons, ha, hb, List.find?, List.filter_nil,
    not_false_eq_true, decide_true, if_true, decide_eq_true_eq, List.length_cons,
    List.length_nil, List.contains_cons, List.elem_nil, Bool.or_false,
    if_pos (show ¬(false = true) by decide),
    show (0 + 1 + 1 + 1 : Nat) = 3 from rfl, Bool.or_eq_true, beq_iff_eq]
  by_cases h1 : followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) [ma.frm, mb.frm] ma.frm [] 3 = c
  · rw [if_pos h1]; simp only [h1, decide_true]
  · rw [if_neg h1]; simp only [h1, decide_false]
    by_cases h2 : followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) [ma.frm, mb.frm] mb.frm [] 3 = c
    · rw [if_pos h2]; simp only [h2, decide_true]
    · rw [if_neg h2]; simp only [h2, decide_false]

/-- Only A carries: one journey, and only `ma.frm` is cleared. -/
theorem applyMoves_cell_TF (bd : Board) (ma mb : Move) (c : Coord)
    (hx : c.x < bd.size) (hy : c.y < bd.size)
    (ha : (bd.cellAt ma.frm).isVacuum = false) (hb : (bd.cellAt mb.frm).isVacuum = true) :
    (applyMoves bd [ma, mb]).cellAt c
      = (if followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) [ma.frm] ma.frm [] 3 = c
         then bd.cellAt ma.frm
         else if c = ma.frm then Particle.vacuum else bd.cellAt c) := by
  rw [Board.cellAt, applyMoves_size, if_pos (⟨hx, hy⟩ : c.x < bd.size ∧ c.y < bd.size)]
  simp only [applyMoves, List.map, List.filter_cons, ha, hb, List.find?, List.filter_nil,
    not_false_eq_true, decide_true, if_true, decide_eq_true_eq, List.length_cons,
    List.length_nil, List.contains_cons, List.elem_nil, Bool.or_false,
    if_pos (show ¬(false = true) by decide), if_neg (show ¬(¬(true = true)) by decide), not_true_eq_false, if_neg not_false,
    show (0 + 1 + 1 + 1 : Nat) = 3 from rfl, Bool.or_eq_true, beq_iff_eq]
  by_cases h1 : followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) [ma.frm] ma.frm [] 3 = c
  · rw [if_pos h1]; simp only [h1, decide_true]
  · rw [if_neg h1]; simp only [h1, decide_false]

/-- Only B carries: the mirror. -/
theorem applyMoves_cell_FT (bd : Board) (ma mb : Move) (c : Coord)
    (hx : c.x < bd.size) (hy : c.y < bd.size)
    (ha : (bd.cellAt ma.frm).isVacuum = true) (hb : (bd.cellAt mb.frm).isVacuum = false) :
    (applyMoves bd [ma, mb]).cellAt c
      = (if followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) [mb.frm] mb.frm [] 3 = c
         then bd.cellAt mb.frm
         else if c = mb.frm then Particle.vacuum else bd.cellAt c) := by
  rw [Board.cellAt, applyMoves_size, if_pos (⟨hx, hy⟩ : c.x < bd.size ∧ c.y < bd.size)]
  simp only [applyMoves, List.map, List.filter_cons, ha, hb, List.find?, List.filter_nil,
    not_false_eq_true, decide_true, if_true, decide_eq_true_eq, List.length_cons,
    List.length_nil, List.contains_cons, List.elem_nil, Bool.or_false,
    if_pos (show ¬(false = true) by decide), if_neg (show ¬(¬(true = true)) by decide), not_true_eq_false, if_neg not_false,
    show (0 + 1 + 1 + 1 : Nat) = 3 from rfl, Bool.or_eq_true, beq_iff_eq]
  by_cases h1 : followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) [mb.frm] mb.frm [] 3 = c
  · rw [if_pos h1]; simp only [h1, decide_true, List.contains_cons, List.elem_nil,
      Bool.or_false, beq_iff_eq]
  · rw [if_neg h1]; simp only [h1, decide_false, List.contains_cons, List.elem_nil,
      Bool.or_false, beq_iff_eq]

/-- NEITHER source carries: the board is untouched. -/
theorem applyMoves_cell_FF (bd : Board) (ma mb : Move) (c : Coord)
    (hx : c.x < bd.size) (hy : c.y < bd.size)
    (ha : (bd.cellAt ma.frm).isVacuum = true) (hb : (bd.cellAt mb.frm).isVacuum = true) :
    (applyMoves bd [ma, mb]).cellAt c = bd.cellAt c := by
  rw [Board.cellAt, applyMoves_size, if_pos (⟨hx, hy⟩ : c.x < bd.size ∧ c.y < bd.size)]
  simp only [applyMoves, List.map, List.filter_cons, ha, hb, List.find?, List.filter_nil,
    not_false_eq_true, decide_true, if_true, decide_eq_true_eq,
    if_neg (show ¬(¬(true = true)) by decide), not_true_eq_false, if_neg not_false, List.contains_nil]
  rfl

/-! ## §8d  THE `m = 2` MOVE GRAPH AND THE OCCLUSION-AWARE CATERPILLAR.

Pure reference semantics: the two-move graph as a lookup table, and each piece's chain destination in
all five shapes the fixed `followChain` can produce. `Dregg2.Circuit.Emit.AutomataflResolveCapstone`
re-exports these under the same names — they were written there, but they mention no descriptor and
no trace, and the conservation theorem in §8e is their real consumer. -/

/-- **THE `m = 2` MOVE GRAPH, UNCONDITIONALLY.** Each source maps to its own destination exactly when
its own move is not occluded; `find?` scans in list order, so A's entry shadows B's on a shared
source. NO board-size hypothesis: this is the `nextOf`/`find?` computation itself. -/
theorem nextOf_pairN (bd : Board) (ma mb : Move) (srcs : List Coord) (c : Coord) :
    nextOf bd [ma, mb] srcs c
      = if c = ma.frm ∧ occluded bd srcs ma = false then some ma.to
        else if c = mb.frm ∧ occluded bd srcs mb = false then some mb.to else none := by
  by_cases h1 : c = ma.frm ∧ occluded bd srcs ma = false
  · have e1 : (decide (ma.frm = c ∧ ¬ occluded bd srcs ma = true)) = true := by
      simp [h1.1.symm, h1.2]
    rw [if_pos h1]
    simp only [nextOf, List.find?_cons, List.find?_nil, e1, Option.map_some, decide_eq_true_eq,
      Option.map_eq_some_iff, List.mem_cons, List.not_mem_nil, or_false]
  · have e1 : (decide (ma.frm = c ∧ ¬ occluded bd srcs ma = true)) = false := by
      simp only [decide_eq_false_iff_not, not_and, Decidable.not_not]
      intro q
      cases hocc : occluded bd srcs ma
      · exact absurd ⟨q.symm, hocc⟩ h1
      · rfl
    rw [if_neg h1]
    by_cases h2 : c = mb.frm ∧ occluded bd srcs mb = false
    · have e2 : (decide (mb.frm = c ∧ ¬ occluded bd srcs mb = true)) = true := by
        simp [h2.1.symm, h2.2]
      rw [if_pos h2]
      simp only [nextOf, List.find?_cons, List.find?_nil, e1, e2, Option.map_some,
        decide_eq_true_eq, Option.map_eq_some_iff, List.mem_cons, List.not_mem_nil, or_false]
    · have e2 : (decide (mb.frm = c ∧ ¬ occluded bd srcs mb = true)) = false := by
        simp only [decide_eq_false_iff_not, not_and, Decidable.not_not]
        intro q
        cases hocc : occluded bd srcs mb
        · exact absurd ⟨q.symm, hocc⟩ h2
        · rfl
      rw [if_neg h2]
      simp only [nextOf, List.find?_cons, List.find?_nil, e1, e2, Option.map_none,
        decide_eq_true_eq, Option.map_eq_none_iff, List.find?_eq_none, List.mem_cons,
        List.not_mem_nil, or_false, not_and, Decidable.not_not]

/-- **THE A-SIDE LANDING, ALL FIVE CASES, OCCLUSION-AWARE.** Piece A's chain destination is

  * the OTHER piece's `to` exactly on the circuit's `ft_a` pattern — `to_a = frm_b`, `frm_b` NOT
    occluded (so the edge exists), `frm_b` not a carrying source, the 2-cycle broken, and `to_b` not
    a carrying source either (the last conjunct is DEFECT #8's: riding through onto a carrying
    square is only legal if that piece itself vacates, and `to_b` has no edge out);
  * A's OWN SOURCE `frm_a` — the move FAILS TO EXECUTE, defect #8's fix — when `to_a` carries a
    piece with NO edge out of it (occluded, or not a move source at all among the two);
  * A's own `to_a` otherwise.

The caterpillar is at most two hops because the graph has two edges and both self-loops are excluded
by `frm ≠ to`. The MIDDLE case is what the pre-fix reference got wrong: it landed A on `to_a`
regardless, so A's journey and the stayer's journey shared a square, `journeys.find?` awarded it to
one of them, and the OTHER piece vanished from the board. -/
theorem chainDest_aN (bd : Board) (ma mb : Move) (ps : List Coord)
    (hoa : occluded bd [ma.frm, mb.frm] ma = false)
    (hda : ma.frm ≠ ma.to) (hdb : mb.frm ≠ mb.to) (f : Nat) :
    followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) ps ma.frm [] (f + 1 + 1)
      = if ma.to = mb.frm ∧ occluded bd [ma.frm, mb.frm] mb = false
             ∧ ps.contains mb.frm = false ∧ mb.to ≠ ma.frm ∧ ps.contains mb.to = false
        then mb.to
        else if ps.contains ma.to = true
                ∧ ¬ (ma.to = mb.frm ∧ occluded bd [ma.frm, mb.frm] mb = false)
             then ma.frm else ma.to := by
  have hstart : nextOf bd [ma, mb] [ma.frm, mb.frm] ma.frm = some ma.to := by
    rw [nextOf_pairN, if_pos ⟨rfl, hoa⟩]
  have hnil : ¬ ([] : List Coord).contains ma.to = true := by simp
  by_cases hab : ma.to = mb.frm ∧ occluded bd [ma.frm, mb.frm] mb = false
  · have hnext : nextOf bd [ma, mb] [ma.frm, mb.frm] ma.to = some mb.to := by
      rw [nextOf_pairN, if_neg (by rintro ⟨q, -⟩; exact hda q.symm), if_pos ⟨hab.1, hab.2⟩]
    have hmid : ¬ (ps.contains ma.to = true
        ∧ ¬ (ma.to = mb.frm ∧ occluded bd [ma.frm, mb.frm] mb = false)) := by
      rintro ⟨-, h⟩; exact h hab
    rw [if_neg hmid]
    by_cases hps : ps.contains ma.to = true
    · -- `to_a` is B's carrying source, and B HAS an edge: the caterpillar stops on `to_a`.
      have hL : followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) ps ma.frm [] (f + 1 + 1)
          = ma.to := by
        rw [followChain, hstart]
        dsimp only
        rw [if_neg hnil, if_pos hps, hnext]
        simp
      have hno : ¬ (ma.to = mb.frm ∧ occluded bd [ma.frm, mb.frm] mb = false
          ∧ ps.contains mb.frm = false ∧ mb.to ≠ ma.frm ∧ ps.contains mb.to = false) := by
        rintro ⟨h1, -, h3, -⟩
        rw [h1, h3] at hps
        exact Bool.false_ne_true hps
      rw [hL, if_neg hno]
    · by_cases hcy : mb.to = ma.frm
      · have hL : followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) ps ma.frm [] (f + 1 + 1)
            = ma.to := by
          rw [followChain, hstart]
          dsimp only
          rw [if_neg hnil, if_neg hps, hnext]
          dsimp only
          rw [followChain, hnext]
          dsimp only
          rw [if_pos (show ([ma.frm] : List Coord).contains mb.to = true by simp [hcy])]
        have hno : ¬ (ma.to = mb.frm ∧ occluded bd [ma.frm, mb.frm] mb = false
            ∧ ps.contains mb.frm = false ∧ mb.to ≠ ma.frm ∧ ps.contains mb.to = false) := by
          rintro ⟨-, -, -, h4, -⟩; exact h4 hcy
        rw [hL, if_neg hno]
      · have hnextB : nextOf bd [ma, mb] [ma.frm, mb.frm] mb.to = none := by
          rw [nextOf_pairN, if_neg (by rintro ⟨q, -⟩; exact hcy q),
            if_neg (by rintro ⟨q, -⟩; exact hdb q.symm)]
        by_cases hpsb : ps.contains mb.to = true
        · -- DEFECT #8, one hop further out: `to_b` carries and has NO edge, so B stays and A's
          -- ride stops on `to_a` instead of running onto B's particle.
          have hL : followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) ps ma.frm [] (f + 1 + 1)
              = ma.to := by
            rw [followChain, hstart]
            dsimp only
            rw [if_neg hnil, if_neg hps, hnext]
            dsimp only
            rw [followChain, hnext]
            dsimp only
            rw [if_neg (show ¬ ([ma.frm] : List Coord).contains mb.to = true by simp [hcy]),
              if_pos hpsb, hnextB]
            simp
          have hno : ¬ (ma.to = mb.frm ∧ occluded bd [ma.frm, mb.frm] mb = false
              ∧ ps.contains mb.frm = false ∧ mb.to ≠ ma.frm ∧ ps.contains mb.to = false) := by
            rintro ⟨-, -, -, -, h5⟩
            rw [h5] at hpsb
            exact Bool.false_ne_true hpsb
          rw [hL, if_neg hno]
        · have hL : followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) ps ma.frm [] (f + 1 + 1)
              = mb.to := by
            rw [followChain, hstart]
            dsimp only
            rw [if_neg hnil, if_neg hps, hnext]
            dsimp only
            rw [followChain, hnext]
            dsimp only
            rw [if_neg (show ¬ ([ma.frm] : List Coord).contains mb.to = true by simp [hcy]),
              if_neg hpsb, hnextB]
          have hyes : ma.to = mb.frm ∧ occluded bd [ma.frm, mb.frm] mb = false
              ∧ ps.contains mb.frm = false ∧ mb.to ≠ ma.frm ∧ ps.contains mb.to = false :=
            ⟨hab.1, hab.2, by rw [← hab.1]; simpa using hps, hcy, by simpa using hpsb⟩
          rw [hL, if_pos hyes]
  · -- NO edge out of `to_a`.
    have hnext : nextOf bd [ma, mb] [ma.frm, mb.frm] ma.to = none := by
      rw [nextOf_pairN, if_neg (by rintro ⟨q, -⟩; exact hda q.symm),
        if_neg (by rintro ⟨q1, q2⟩; exact hab ⟨q1, q2⟩)]
    have hno : ¬ (ma.to = mb.frm ∧ occluded bd [ma.frm, mb.frm] mb = false
        ∧ ps.contains mb.frm = false ∧ mb.to ≠ ma.frm ∧ ps.contains mb.to = false) := by
      rintro ⟨h1, h2, -, -, -⟩; exact hab ⟨h1, h2⟩
    rw [if_neg hno]
    by_cases hps : ps.contains ma.to = true
    · -- **DEFECT #8'S CASE.** `to_a` carries a piece that cannot move: A's move fails to execute.
      have hL : followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) ps ma.frm [] (f + 1 + 1)
          = ma.frm := by
        rw [followChain, hstart]
        dsimp only
        rw [if_neg hnil, if_pos hps, hnext]
        simp
      rw [hL, if_pos ⟨hps, hab⟩]
    · have hL : followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) ps ma.frm [] (f + 1 + 1)
          = ma.to := by
        rw [followChain, hstart]
        dsimp only
        rw [if_neg hnil, if_neg hps, hnext]
      rw [hL, if_neg (by rintro ⟨h, -⟩; exact hps h)]

/-- **THE B-SIDE LANDING, ALL FIVE CASES, OCCLUSION-AWARE** — the mirror of `chainDest_aN`, under
distinct sources (which is what makes B's own edge reachable past A's in `find?` order). -/
theorem chainDest_bN (bd : Board) (ma mb : Move) (ps : List Coord)
    (hne : ma.frm ≠ mb.frm) (hob : occluded bd [ma.frm, mb.frm] mb = false)
    (hda : ma.frm ≠ ma.to) (hdb : mb.frm ≠ mb.to) (f : Nat) :
    followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) ps mb.frm [] (f + 1 + 1)
      = if mb.to = ma.frm ∧ occluded bd [ma.frm, mb.frm] ma = false
             ∧ ps.contains ma.frm = false ∧ ma.to ≠ mb.frm ∧ ps.contains ma.to = false
        then ma.to
        else if ps.contains mb.to = true
                ∧ ¬ (mb.to = ma.frm ∧ occluded bd [ma.frm, mb.frm] ma = false)
             then mb.frm else mb.to := by
  have hstart : nextOf bd [ma, mb] [ma.frm, mb.frm] mb.frm = some mb.to := by
    rw [nextOf_pairN, if_neg (by rintro ⟨q, -⟩; exact hne q.symm), if_pos ⟨rfl, hob⟩]
  have hnil : ¬ ([] : List Coord).contains mb.to = true := by simp
  by_cases hba : mb.to = ma.frm ∧ occluded bd [ma.frm, mb.frm] ma = false
  · have hnext : nextOf bd [ma, mb] [ma.frm, mb.frm] mb.to = some ma.to := by
      rw [nextOf_pairN, if_pos ⟨hba.1, hba.2⟩]
    have hmid : ¬ (ps.contains mb.to = true
        ∧ ¬ (mb.to = ma.frm ∧ occluded bd [ma.frm, mb.frm] ma = false)) := by
      rintro ⟨-, h⟩; exact h hba
    rw [if_neg hmid]
    by_cases hps : ps.contains mb.to = true
    · have hL : followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) ps mb.frm [] (f + 1 + 1)
          = mb.to := by
        rw [followChain, hstart]
        dsimp only
        rw [if_neg hnil, if_pos hps, hnext]
        simp
      have hno : ¬ (mb.to = ma.frm ∧ occluded bd [ma.frm, mb.frm] ma = false
          ∧ ps.contains ma.frm = false ∧ ma.to ≠ mb.frm ∧ ps.contains ma.to = false) := by
        rintro ⟨h1, -, h3, -⟩
        rw [h1, h3] at hps
        exact Bool.false_ne_true hps
      rw [hL, if_neg hno]
    · by_cases hcy : ma.to = mb.frm
      · have hL : followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) ps mb.frm [] (f + 1 + 1)
            = mb.to := by
          rw [followChain, hstart]
          dsimp only
          rw [if_neg hnil, if_neg hps, hnext]
          dsimp only
          rw [followChain, hnext]
          dsimp only
          rw [if_pos (show ([mb.frm] : List Coord).contains ma.to = true by simp [hcy])]
        have hno : ¬ (mb.to = ma.frm ∧ occluded bd [ma.frm, mb.frm] ma = false
            ∧ ps.contains ma.frm = false ∧ ma.to ≠ mb.frm ∧ ps.contains ma.to = false) := by
          rintro ⟨-, -, -, h4, -⟩; exact h4 hcy
        rw [hL, if_neg hno]
      · have hnextA : nextOf bd [ma, mb] [ma.frm, mb.frm] ma.to = none := by
          rw [nextOf_pairN, if_neg (by rintro ⟨q, -⟩; exact hda q.symm),
            if_neg (by rintro ⟨q, -⟩; exact hcy q)]
        by_cases hpsa : ps.contains ma.to = true
        · have hL : followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) ps mb.frm [] (f + 1 + 1)
              = mb.to := by
            rw [followChain, hstart]
            dsimp only
            rw [if_neg hnil, if_neg hps, hnext]
            dsimp only
            rw [followChain, hnext]
            dsimp only
            rw [if_neg (show ¬ ([mb.frm] : List Coord).contains ma.to = true by simp [hcy]),
              if_pos hpsa, hnextA]
            simp
          have hno : ¬ (mb.to = ma.frm ∧ occluded bd [ma.frm, mb.frm] ma = false
              ∧ ps.contains ma.frm = false ∧ ma.to ≠ mb.frm ∧ ps.contains ma.to = false) := by
            rintro ⟨-, -, -, -, h5⟩
            rw [h5] at hpsa
            exact Bool.false_ne_true hpsa
          rw [hL, if_neg hno]
        · have hL : followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) ps mb.frm [] (f + 1 + 1)
              = ma.to := by
            rw [followChain, hstart]
            dsimp only
            rw [if_neg hnil, if_neg hps, hnext]
            dsimp only
            rw [followChain, hnext]
            dsimp only
            rw [if_neg (show ¬ ([mb.frm] : List Coord).contains ma.to = true by simp [hcy]),
              if_neg hpsa, hnextA]
          have hyes : mb.to = ma.frm ∧ occluded bd [ma.frm, mb.frm] ma = false
              ∧ ps.contains ma.frm = false ∧ ma.to ≠ mb.frm ∧ ps.contains ma.to = false :=
            ⟨hba.1, hba.2, by rw [← hba.1]; simpa using hps, hcy, by simpa using hpsa⟩
          rw [hL, if_pos hyes]
  · have hnext : nextOf bd [ma, mb] [ma.frm, mb.frm] mb.to = none := by
      rw [nextOf_pairN, if_neg (by rintro ⟨q1, q2⟩; exact hba ⟨q1, q2⟩),
        if_neg (by rintro ⟨q, -⟩; exact hdb q.symm)]
    have hno : ¬ (mb.to = ma.frm ∧ occluded bd [ma.frm, mb.frm] ma = false
        ∧ ps.contains ma.frm = false ∧ ma.to ≠ mb.frm ∧ ps.contains ma.to = false) := by
      rintro ⟨h1, h2, -, -, -⟩; exact hba ⟨h1, h2⟩
    rw [if_neg hno]
    by_cases hps : ps.contains mb.to = true
    · have hL : followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) ps mb.frm [] (f + 1 + 1)
          = mb.frm := by
        rw [followChain, hstart]
        dsimp only
        rw [if_neg hnil, if_pos hps, hnext]
        simp
      rw [hL, if_pos ⟨hps, hba⟩]
    · have hL : followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) ps mb.frm [] (f + 1 + 1)
          = mb.to := by
        rw [followChain, hstart]
        dsimp only
        rw [if_neg hnil, if_neg hps, hnext]
      rw [hL, if_neg (by rintro ⟨h, -⟩; exact hps h)]


/-! ## §8e  **THE CONSERVATION THEOREM** — the resolution neither DESTROYS nor DUPLICATES a piece.

Defect #8 was a piece-DESTRUCTION bug: a follower landed on a square whose occupant did not vacate,
two journeys shared a destination, `journeys.find?` awarded the square to one of them, and the other
piece VANISHED off the board.  Patching the traced configuration is worth little on its own; what
makes the whole CLASS impossible to reintroduce silently is a theorem that the resolution PRESERVES
THE PIECES.

`ConservesPieces b b' φ` is the exact-once formulation: `φ` maps each occupied cell of `b` to the
cell its particle occupies in `b'` — INJECTIVELY (no two pieces merge), PARTICLE-PRESERVINGLY (no
piece is silently retyped), and ONTO the occupied cells of `b'` (no piece is conjured).  It is
strictly stronger than a multiset count: it names WHERE each piece went.

`applyMoves_conserves_pieces` proves it for the DEPLOYED ARITY `m = 2` (one move per player — the
shape the whole automatafl descriptor is built for), at ARBITRARY board size, with occlusion LIVE.
The two side hypotheses are honest and named:

  * `hsurv` — the pair is not fork/collide-conflicted.  This is exactly what `conflictResolve`
    guarantees; without it two pieces genuinely target one square and NO resolution can conserve.
  * `hland` — no move targets a square held by a piece that is not one of the two movers.  This is
    the LABELLED RESIDUAL of defect #8 (see `followChain`): a destination held by a NON-SOURCE piece
    is still overwritten, because `followChain` is handed the piece SOURCES, not the board's
    occupancy.  Closing it needs occupancy inside the chain AND a matching descriptor change, so it
    is NAMED here rather than silently assumed away.

`hland` does NOT exclude defect #8's own witness — there the blocker is an OCCLUDER, never a
target — which is what makes this theorem load-bearing: `buggy_refutes_conservation` shows the
PRE-FIX chain violating `ConservesPieces` on a board satisfying every hypothesis. -/

/-- `b'` holds EXACTLY the pieces of `b`, each exactly once, at the cells named by `φ`. -/
structure ConservesPieces (b b' : Board) (φ : Coord → Coord) : Prop where
  /-- No two pieces merge. -/
  inj   : ∀ c₁ c₂ : Coord, (b.cellAt c₁).isVacuum = false → (b.cellAt c₂).isVacuum = false →
            φ c₁ = φ c₂ → c₁ = c₂
  /-- Every piece is still there, with its particle unchanged. -/
  carry : ∀ c : Coord, (b.cellAt c).isVacuum = false → b'.cellAt (φ c) = b.cellAt c
  /-- Nothing was conjured: every occupied cell after is the image of an occupied cell before. -/
  onto  : ∀ c : Coord, (b'.cellAt c).isVacuum = false →
            ∃ c₀ : Coord, (b.cellAt c₀).isVacuum = false ∧ φ c₀ = c

/-- An occupied cell is in bounds (`cellAt` reads vacuum outside the board). -/
theorem inBounds_of_nonvacuum (b : Board) (c : Coord) (h : (b.cellAt c).isVacuum = false) :
    c.x < b.size ∧ c.y < b.size := by
  rw [Board.cellAt] at h
  split at h
  · assumption
  · exact absurd h (by decide)

/-- `occluded` reads a move only through its endpoints. -/
theorem occluded_endpoints (bd : Board) (srcs : List Coord) (m m' : Move)
    (hf : m.frm = m'.frm) (ht : m.to = m'.to) :
    occluded bd srcs m = occluded bd srcs m' := by
  simp only [occluded, hf, ht]

section Conserve

/-- No edge leaves an occluded source (with the shared-source case folded in). -/
theorem nextOf_none_of_occluded (bd : Board) (ma mb : Move)
    (hto : ma.frm = mb.frm → ma.to = mb.to)
    (hoa : occluded bd [ma.frm, mb.frm] ma = true) :
    nextOf bd [ma, mb] [ma.frm, mb.frm] ma.frm = none := by
  rw [nextOf_pairN, if_neg (by rintro ⟨-, q⟩; rw [hoa] at q; exact Bool.noConfusion q)]
  by_cases hf : ma.frm = mb.frm
  · have hob : occluded bd [ma.frm, mb.frm] mb = true := by
      rw [← occluded_endpoints bd [ma.frm, mb.frm] ma mb hf (hto hf)]; exact hoa
    rw [if_neg (by rintro ⟨-, q⟩; rw [hob] at q; exact Bool.noConfusion q)]
  · rw [if_neg (by rintro ⟨q, -⟩; exact hf q)]

/-- A's move FAILS TO EXECUTE — A stays on its own square — when A is occluded, or when A's target
is B's carrying source and B is occluded (so the piece there does not vacate).  The second disjunct
is precisely defect #8's fix. -/
theorem chainStay_a (bd : Board) (ma mb : Move) (hda : ma.frm ≠ ma.to) (hdb : mb.frm ≠ mb.to)
    (hto : ma.frm = mb.frm → ma.to = mb.to)
    (h : occluded bd [ma.frm, mb.frm] ma = true
          ∨ (ma.to = mb.frm ∧ occluded bd [ma.frm, mb.frm] mb = true)) :
    followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) [ma.frm, mb.frm] ma.frm [] 3 = ma.frm := by
  by_cases hoa : occluded bd [ma.frm, mb.frm] ma = true
  · rw [followChain, nextOf_none_of_occluded bd ma mb hto hoa]
  · obtain ⟨hab, hob⟩ := h.resolve_left hoa
    have hoa' : occluded bd [ma.frm, mb.frm] ma = false := by
      cases q : occluded bd [ma.frm, mb.frm] ma
      · rfl
      · exact absurd q hoa
    rw [show (3 : Nat) = 1 + 1 + 1 from rfl, chainDest_aN bd ma mb [ma.frm, mb.frm] hoa' hda hdb 1,
      if_neg (by rintro ⟨-, h2, -⟩; rw [hob] at h2; exact Bool.noConfusion h2),
      if_pos ⟨by simp [hab], by rintro ⟨-, h2⟩; rw [hob] at h2; exact Bool.noConfusion h2⟩]

/-- A's move EXECUTES — A lands on its own target — when A is not occluded and its target is not a
blocked carrying source. -/
theorem chainGo_a (bd : Board) (ma mb : Move) (hda : ma.frm ≠ ma.to) (hdb : mb.frm ≠ mb.to)
    (hoa : occluded bd [ma.frm, mb.frm] ma = false)
    (h : ¬ (ma.to = mb.frm ∧ occluded bd [ma.frm, mb.frm] mb = true)) :
    followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) [ma.frm, mb.frm] ma.frm [] 3 = ma.to := by
  rw [show (3 : Nat) = 1 + 1 + 1 from rfl, chainDest_aN bd ma mb [ma.frm, mb.frm] hoa hda hdb 1,
    if_neg (by rintro ⟨-, -, h3, -⟩; simp at h3),
    if_neg ?_]
  rintro ⟨h1, h2⟩
  simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true,
    beq_iff_eq] at h1
  rcases h1 with h1 | h1
  · exact hda h1.symm
  · refine h2 ⟨h1, ?_⟩
    cases q : occluded bd [ma.frm, mb.frm] mb
    · rfl
    · exact absurd (h ⟨h1, q⟩) not_false

/-- B's move fails to execute — the mirror of `chainStay_a`, under distinct sources. -/
theorem chainStay_b (bd : Board) (ma mb : Move) (hne : ma.frm ≠ mb.frm)
    (hda : ma.frm ≠ ma.to) (hdb : mb.frm ≠ mb.to)
    (h : occluded bd [ma.frm, mb.frm] mb = true
          ∨ (mb.to = ma.frm ∧ occluded bd [ma.frm, mb.frm] ma = true)) :
    followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) [ma.frm, mb.frm] mb.frm [] 3 = mb.frm := by
  by_cases hob : occluded bd [ma.frm, mb.frm] mb = true
  · have hnone : nextOf bd [ma, mb] [ma.frm, mb.frm] mb.frm = none := by
      rw [nextOf_pairN, if_neg (by rintro ⟨q, -⟩; exact hne q.symm),
        if_neg (by rintro ⟨-, q⟩; rw [hob] at q; exact Bool.noConfusion q)]
    rw [followChain, hnone]
  · obtain ⟨hba, hoa⟩ := h.resolve_left hob
    have hob' : occluded bd [ma.frm, mb.frm] mb = false := by
      cases q : occluded bd [ma.frm, mb.frm] mb
      · rfl
      · exact absurd q hob
    rw [show (3 : Nat) = 1 + 1 + 1 from rfl,
      chainDest_bN bd ma mb [ma.frm, mb.frm] hne hob' hda hdb 1,
      if_neg (by rintro ⟨-, h2, -⟩; rw [hoa] at h2; exact Bool.noConfusion h2),
      if_pos ⟨by simp [hba], by rintro ⟨-, h2⟩; rw [hoa] at h2; exact Bool.noConfusion h2⟩]

/-- B's move executes — the mirror of `chainGo_a`. -/
theorem chainGo_b (bd : Board) (ma mb : Move) (hne : ma.frm ≠ mb.frm)
    (hda : ma.frm ≠ ma.to) (hdb : mb.frm ≠ mb.to)
    (hob : occluded bd [ma.frm, mb.frm] mb = false)
    (h : ¬ (mb.to = ma.frm ∧ occluded bd [ma.frm, mb.frm] ma = true)) :
    followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) [ma.frm, mb.frm] mb.frm [] 3 = mb.to := by
  rw [show (3 : Nat) = 1 + 1 + 1 from rfl,
    chainDest_bN bd ma mb [ma.frm, mb.frm] hne hob hda hdb 1,
    if_neg (by rintro ⟨-, -, h3, -⟩; simp at h3),
    if_neg ?_]
  rintro ⟨h1, h2⟩
  simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true,
    beq_iff_eq] at h1
  rcases h1 with h1 | h1
  · refine h2 ⟨h1, ?_⟩
    cases q : occluded bd [ma.frm, mb.frm] ma
    · rfl
    · exact absurd (h ⟨h1, q⟩) not_false
  · exact hdb h1.symm

/-- **CONSERVATION FROM THE ONE-JOURNEY REWRITE.** If `b'` is `b` with the piece on `s` moved to
`d`, and `d` is either `s` itself or an EMPTY square, then `b'` holds exactly `b`'s pieces. -/
theorem conserves_of_single (bd b' : Board) (s d : Coord)
    (hsize : b'.size = bd.size)
    (hdx : d.x < bd.size) (hdy : d.y < bd.size)
    (hd : d = s ∨ (bd.cellAt d).isVacuum = true)
    (hcell : ∀ c : Coord, c.x < bd.size → c.y < bd.size →
        b'.cellAt c
          = (if d = c then bd.cellAt s else if c = s then Particle.vacuum else bd.cellAt c)) :
    ConservesPieces bd b' (fun c => if c = s then d else c) := by
  have hdne : ∀ c : Coord, (bd.cellAt c).isVacuum = false → c ≠ s → d ≠ c := by
    intro c hc hcs hdc
    rcases hd with h | h
    · exact hcs (hdc ▸ h)
    · rw [hdc, hc] at h; exact Bool.noConfusion h
  refine ⟨?_, ?_, ?_⟩
  · intro c₁ c₂ h1 h2 heq
    by_cases e1 : c₁ = s
    · by_cases e2 : c₂ = s
      · rw [e1, e2]
      · rw [if_pos e1, if_neg e2] at heq
        exact absurd heq (hdne c₂ h2 e2)
    · by_cases e2 : c₂ = s
      · rw [if_neg e1, if_pos e2] at heq
        exact absurd heq.symm (hdne c₁ h1 e1)
      · rw [if_neg e1, if_neg e2] at heq; exact heq
  · intro c hc
    obtain ⟨hx, hy⟩ := inBounds_of_nonvacuum bd c hc
    by_cases e : c = s
    · rw [if_pos e, hcell d hdx hdy, if_pos rfl, e]
    · rw [if_neg e, hcell c hx hy, if_neg (hdne c hc e), if_neg e]
  · intro c hc
    obtain ⟨hx, hy⟩ := inBounds_of_nonvacuum b' c hc
    rw [hsize] at hx hy
    rw [hcell c hx hy] at hc
    by_cases h1 : d = c
    · rw [if_pos h1] at hc
      exact ⟨s, hc, by rw [if_pos rfl, h1]⟩
    · rw [if_neg h1] at hc
      by_cases h2 : c = s
      · rw [if_pos h2] at hc; exact absurd hc (by decide)
      · rw [if_neg h2] at hc
        exact ⟨c, hc, by rw [if_neg h2]⟩

/-- **CONSERVATION FROM THE TWO-JOURNEY REWRITE.** Two pieces move to DISTINCT squares, each of
which is one of the two sources or an EMPTY square: no piece is dropped and none is duplicated. -/
theorem conserves_of_pair (bd b' : Board) (s₁ s₂ d₁ d₂ : Coord)
    (hsize : b'.size = bd.size) (hs : s₁ ≠ s₂)
    (hd1x : d₁.x < bd.size) (hd1y : d₁.y < bd.size)
    (hd2x : d₂.x < bd.size) (hd2y : d₂.y < bd.size)
    (hdd : d₁ ≠ d₂)
    (hl1 : d₁ = s₁ ∨ d₁ = s₂ ∨ (bd.cellAt d₁).isVacuum = true)
    (hl2 : d₂ = s₁ ∨ d₂ = s₂ ∨ (bd.cellAt d₂).isVacuum = true)
    (hv1 : (bd.cellAt s₁).isVacuum = false) (hv2 : (bd.cellAt s₂).isVacuum = false)
    (hcell : ∀ c : Coord, c.x < bd.size → c.y < bd.size →
        b'.cellAt c
          = (if d₁ = c then bd.cellAt s₁ else if d₂ = c then bd.cellAt s₂
             else if c = s₁ ∨ c = s₂ then Particle.vacuum else bd.cellAt c)) :
    ConservesPieces bd b' (fun c => if c = s₁ then d₁ else if c = s₂ then d₂ else c) := by
  have hout : ∀ d : Coord, (d = s₁ ∨ d = s₂ ∨ (bd.cellAt d).isVacuum = true) →
      ∀ c : Coord, (bd.cellAt c).isVacuum = false → c ≠ s₁ → c ≠ s₂ → d ≠ c := by
    intro d hdl c hc h1 h2 hdc
    rcases hdl with h | h | h
    · exact h1 (hdc ▸ h)
    · exact h2 (hdc ▸ h)
    · rw [hdc, hc] at h; exact Bool.noConfusion h
  have hne1 := hout d₁ hl1
  have hne2 := hout d₂ hl2
  refine ⟨?_, ?_, ?_⟩
  · intro c₁ c₂ h1 h2 heq
    by_cases e1 : c₁ = s₁
    · rw [if_pos e1] at heq
      by_cases e2 : c₂ = s₁
      · rw [e1, e2]
      · rw [if_neg e2] at heq
        by_cases f2 : c₂ = s₂
        · rw [if_pos f2] at heq; exact absurd heq hdd
        · rw [if_neg f2] at heq; exact absurd heq (hne1 c₂ h2 e2 f2)
    · rw [if_neg e1] at heq
      by_cases f1 : c₁ = s₂
      · rw [if_pos f1] at heq
        by_cases e2 : c₂ = s₁
        · rw [if_pos e2] at heq; exact absurd heq.symm hdd
        · rw [if_neg e2] at heq
          by_cases f2 : c₂ = s₂
          · rw [f1, f2]
          · rw [if_neg f2] at heq; exact absurd heq (hne2 c₂ h2 e2 f2)
      · rw [if_neg f1] at heq
        by_cases e2 : c₂ = s₁
        · rw [if_pos e2] at heq; exact absurd heq.symm (hne1 c₁ h1 e1 f1)
        · rw [if_neg e2] at heq
          by_cases f2 : c₂ = s₂
          · rw [if_pos f2] at heq; exact absurd heq.symm (hne2 c₁ h1 e1 f1)
          · rw [if_neg f2] at heq; exact heq
  · intro c hc
    obtain ⟨hx, hy⟩ := inBounds_of_nonvacuum bd c hc
    by_cases e : c = s₁
    · rw [if_pos e, hcell d₁ hd1x hd1y, if_pos rfl, e]
    · rw [if_neg e]
      by_cases f : c = s₂
      · rw [if_pos f, hcell d₂ hd2x hd2y, if_neg hdd, if_pos rfl, f]
      · rw [if_neg f, hcell c hx hy, if_neg (hne1 c hc e f), if_neg (hne2 c hc e f),
          if_neg (fun q => q.elim e f)]
  · intro c hc
    obtain ⟨hx, hy⟩ := inBounds_of_nonvacuum b' c hc
    rw [hsize] at hx hy
    rw [hcell c hx hy] at hc
    by_cases h1 : d₁ = c
    · exact ⟨s₁, hv1, by rw [if_pos rfl, h1]⟩
    · rw [if_neg h1] at hc
      by_cases h2 : d₂ = c
      · exact ⟨s₂, hv2, by rw [if_neg (Ne.symm hs), if_pos rfl, h2]⟩
      · rw [if_neg h2] at hc
        by_cases h3 : c = s₁ ∨ c = s₂
        · rw [if_pos h3] at hc; exact absurd hc (by decide)
        · rw [if_neg h3] at hc
          exact ⟨c, hc, by rw [if_neg (fun q => h3 (Or.inl q)), if_neg (fun q => h3 (Or.inr q))]⟩

/-- **THE CONSERVATION THEOREM, at the deployed arity `m = 2`.**  The resolution moves pieces
around; it never DESTROYS one and never DUPLICATES one.  Exact-once form: there is an injection from
the occupied cells of the old board onto the occupied cells of the new one that preserves every
particle.  Arbitrary board size; occlusion LIVE; no `decide`, no enumeration of boards.

Hypotheses, all named and all real:
  * `hva`/`hvb` — the two moves are valid (`propose_move`): distinct endpoints, both in bounds.  A
    move whose TARGET is off-board would carry its piece off the board, and nothing could conserve.
  * `hsurv` — the pair is not fork/collide-conflicted, i.e. it SURVIVED `conflictResolve`.
  * `hlandA`/`hlandB` — neither target square holds a piece that is not one of the two movers.  This
    is defect #8's LABELLED RESIDUAL (`followChain`): the chain is handed the piece SOURCES, not the
    board's occupancy, so a piece standing on a target square that never proposed a move is still
    overwritten.  It is NOT implied by the other hypotheses and it does NOT exclude defect #8's own
    witness — where the blocker is an OCCLUDER, not a target — which is exactly why
    `buggy_refutes_conservation` can refute this theorem for the PRE-FIX chain. -/
theorem applyMoves_conserves_pieces (bd : Board) (ma mb : Move)
    (hva : MoveValid bd ma) (hvb : MoveValid bd mb)
    (hsurv : ¬ ((ma.frm = mb.frm ∧ ma.to ≠ mb.to)
        ∨ (ma.to = mb.to ∧ ma.frm ≠ mb.frm
            ∧ (bd.cellAt ma.frm).isVacuum = false ∧ (bd.cellAt mb.frm).isVacuum = false)))
    (hlandA : (bd.cellAt ma.to).isVacuum = true ∨ ma.to = ma.frm ∨ ma.to = mb.frm)
    (hlandB : (bd.cellAt mb.to).isVacuum = true ∨ mb.to = ma.frm ∨ mb.to = mb.frm) :
    ∃ φ : Coord → Coord, ConservesPieces bd (applyMoves bd [ma, mb]) φ := by
  obtain ⟨hda, -, -, ⟨htax, htay⟩, -, -, -, -⟩ := hva
  obtain ⟨hdb, -, -, ⟨htbx, htby⟩, -, -, -, -⟩ := hvb
  have hto : ma.frm = mb.frm → ma.to = mb.to := by
    intro h
    by_cases q : ma.to = mb.to
    · exact q
    · exact absurd (Or.inl ⟨h, q⟩) hsurv
  cases hvA : (bd.cellAt ma.frm).isVacuum with
  | true =>
    cases hvB : (bd.cellAt mb.frm).isVacuum with
    | true =>
      -- NEITHER source carries: the board is untouched.
      refine ⟨id, ⟨fun _ _ _ _ h => h, ?_, ?_⟩⟩
      · intro c hc
        obtain ⟨hx, hy⟩ := inBounds_of_nonvacuum bd c hc
        exact applyMoves_cell_FF bd ma mb c hx hy hvA hvB
      · intro c hc
        obtain ⟨hx, hy⟩ := inBounds_of_nonvacuum _ c hc
        rw [applyMoves_size] at hx hy
        exact ⟨c, by rw [← applyMoves_cell_FF bd ma mb c hx hy hvA hvB]; exact hc, rfl⟩
    | false =>
      -- ONLY B carries.
      have hne : ma.frm ≠ mb.frm := by
        intro h; rw [h, hvB] at hvA; exact Bool.noConfusion hvA
      have hkey : (followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) [mb.frm] mb.frm [] 3 = mb.frm
            ∨ (bd.cellAt (followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) [mb.frm] mb.frm []
                3)).isVacuum = true)
          ∧ (followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) [mb.frm] mb.frm [] 3).x < bd.size
          ∧ (followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) [mb.frm] mb.frm [] 3).y < bd.size := by
        by_cases hob : occluded bd [ma.frm, mb.frm] mb = true
        · have hnone : nextOf bd [ma, mb] [ma.frm, mb.frm] mb.frm = none := by
            rw [nextOf_pairN, if_neg (by rintro ⟨q, -⟩; exact hne q.symm),
              if_neg (by rintro ⟨-, q⟩; rw [hob] at q; exact Bool.noConfusion q)]
          have hst : followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) [mb.frm] mb.frm [] 3
              = mb.frm := by rw [followChain, hnone]
          obtain ⟨hx, hy⟩ := inBounds_of_nonvacuum bd mb.frm hvB
          exact ⟨Or.inl hst, by rw [hst]; exact hx, by rw [hst]; exact hy⟩
        · have hob' : occluded bd [ma.frm, mb.frm] mb = false := by
            cases q : occluded bd [ma.frm, mb.frm] mb
            · rfl
            · exact absurd q hob
          rw [show (3 : Nat) = 1 + 1 + 1 from rfl,
            chainDest_bN bd ma mb [mb.frm] hne hob' hda hdb 1]
          by_cases hC1 : mb.to = ma.frm ∧ occluded bd [ma.frm, mb.frm] ma = false
              ∧ ([mb.frm] : List Coord).contains ma.frm = false ∧ ma.to ≠ mb.frm
              ∧ ([mb.frm] : List Coord).contains ma.to = false
          · rw [if_pos hC1]
            refine ⟨Or.inr ?_, htax, htay⟩
            rcases hlandA with h | h | h
            · exact h
            · rw [h]; exact hvA
            · exact absurd h hC1.2.2.2.1
          · rw [if_neg hC1]
            have hC2 : ¬ (([mb.frm] : List Coord).contains mb.to = true
                ∧ ¬ (mb.to = ma.frm ∧ occluded bd [ma.frm, mb.frm] ma = false)) := by
              rintro ⟨h, -⟩
              simp only [List.contains_cons, List.contains_nil, Bool.or_false, beq_iff_eq] at h
              exact hdb h.symm
            rw [if_neg hC2]
            refine ⟨Or.inr ?_, htbx, htby⟩
            rcases hlandB with h | h | h
            · exact h
            · rw [h]; exact hvA
            · exact absurd h.symm hdb
      exact ⟨_, conserves_of_single bd _ mb.frm _ (applyMoves_size bd [ma, mb])
        hkey.2.1 hkey.2.2 hkey.1
        (fun c hx hy => applyMoves_cell_FT bd ma mb c hx hy hvA hvB)⟩
  | false =>
    cases hvB : (bd.cellAt mb.frm).isVacuum with
    | true =>
      -- ONLY A carries: the mirror.
      have hne : ma.frm ≠ mb.frm := by
        intro h; rw [h, hvB] at hvA; exact Bool.noConfusion hvA
      have hkey : (followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) [ma.frm] ma.frm [] 3 = ma.frm
            ∨ (bd.cellAt (followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) [ma.frm] ma.frm []
                3)).isVacuum = true)
          ∧ (followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) [ma.frm] ma.frm [] 3).x < bd.size
          ∧ (followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) [ma.frm] ma.frm [] 3).y < bd.size := by
        by_cases hoa : occluded bd [ma.frm, mb.frm] ma = true
        · have hst : followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) [ma.frm] ma.frm [] 3
              = ma.frm := by rw [followChain, nextOf_none_of_occluded bd ma mb hto hoa]
          obtain ⟨hx, hy⟩ := inBounds_of_nonvacuum bd ma.frm hvA
          exact ⟨Or.inl hst, by rw [hst]; exact hx, by rw [hst]; exact hy⟩
        · have hoa' : occluded bd [ma.frm, mb.frm] ma = false := by
            cases q : occluded bd [ma.frm, mb.frm] ma
            · rfl
            · exact absurd q hoa
          rw [show (3 : Nat) = 1 + 1 + 1 from rfl,
            chainDest_aN bd ma mb [ma.frm] hoa' hda hdb 1]
          by_cases hC1 : ma.to = mb.frm ∧ occluded bd [ma.frm, mb.frm] mb = false
              ∧ ([ma.frm] : List Coord).contains mb.frm = false ∧ mb.to ≠ ma.frm
              ∧ ([ma.frm] : List Coord).contains mb.to = false
          · rw [if_pos hC1]
            refine ⟨Or.inr ?_, htbx, htby⟩
            rcases hlandB with h | h | h
            · exact h
            · exact absurd h hC1.2.2.2.1
            · rw [h]; exact hvB
          · rw [if_neg hC1]
            have hC2 : ¬ (([ma.frm] : List Coord).contains ma.to = true
                ∧ ¬ (ma.to = mb.frm ∧ occluded bd [ma.frm, mb.frm] mb = false)) := by
              rintro ⟨h, -⟩
              simp only [List.contains_cons, List.contains_nil, Bool.or_false, beq_iff_eq] at h
              exact hda h.symm
            rw [if_neg hC2]
            refine ⟨Or.inr ?_, htax, htay⟩
            rcases hlandA with h | h | h
            · exact h
            · exact absurd h.symm hda
            · rw [h]; exact hvB
      exact ⟨_, conserves_of_single bd _ ma.frm _ (applyMoves_size bd [ma, mb])
        hkey.2.1 hkey.2.2 hkey.1
        (fun c hx hy => applyMoves_cell_TF bd ma mb c hx hy hvA hvB)⟩
    | false =>
      -- BOTH sources carry.
      by_cases hne : ma.frm = mb.frm
      · -- ONE piece, proposed twice with the same target: a single journey.
        have hteq : ma.to = mb.to := hto hne
        have hchB : followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) [ma.frm, mb.frm] mb.frm [] 3
            = followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) [ma.frm, mb.frm] ma.frm [] 3 := by
          rw [hne]
        have hkey : (followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) [ma.frm, mb.frm] ma.frm []
                3 = ma.frm
              ∨ (bd.cellAt (followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) [ma.frm, mb.frm]
                  ma.frm [] 3)).isVacuum = true)
            ∧ (followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) [ma.frm, mb.frm] ma.frm []
                3).x < bd.size
            ∧ (followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) [ma.frm, mb.frm] ma.frm []
                3).y < bd.size := by
          by_cases hoa : occluded bd [ma.frm, mb.frm] ma = true
          · have hst := chainStay_a bd ma mb hda hdb hto (Or.inl hoa)
            obtain ⟨hx, hy⟩ := inBounds_of_nonvacuum bd ma.frm hvA
            exact ⟨Or.inl hst, by rw [hst]; exact hx, by rw [hst]; exact hy⟩
          · have hoa' : occluded bd [ma.frm, mb.frm] ma = false := by
              cases q : occluded bd [ma.frm, mb.frm] ma
              · rfl
              · exact absurd q hoa
            have hgo := chainGo_a bd ma mb hda hdb hoa'
              (by rintro ⟨h1, -⟩; exact hda (h1.trans hne.symm).symm)
            refine ⟨Or.inr ?_, by rw [hgo]; exact htax, by rw [hgo]; exact htay⟩
            rw [hgo]
            rcases hlandA with h | h | h
            · exact h
            · exact absurd h.symm hda
            · exact absurd (h.trans hne.symm).symm hda
        refine ⟨_, conserves_of_single bd _ ma.frm _ (applyMoves_size bd [ma, mb])
          hkey.2.1 hkey.2.2 hkey.1 (fun c hx hy => ?_)⟩
        rw [applyMoves_cell_TT bd ma mb c hx hy hvA hvB, hchB]
        by_cases h1 : followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) [ma.frm, mb.frm] ma.frm []
            3 = c
        · rw [if_pos h1, if_pos h1]
        · rw [if_neg h1, if_neg h1, if_neg h1]
          by_cases h2 : c = ma.frm
          · rw [if_pos (Or.inl h2), if_pos h2]
          · rw [if_neg (fun q => q.elim h2 (fun r => h2 (r.trans hne.symm))), if_neg h2]
      · -- TWO pieces on distinct squares: the substantive case.
        have hAstay := chainStay_a bd ma mb hda hdb hto
        have hAgo := chainGo_a bd ma mb hda hdb
        have hBstay := chainStay_b bd ma mb hne hda hdb
        have hBgo := chainGo_b bd ma mb hne hda hdb
        by_cases hA : occluded bd [ma.frm, mb.frm] ma = true
            ∨ (ma.to = mb.frm ∧ occluded bd [ma.frm, mb.frm] mb = true)
        · -- A stays
          have hdA := hAstay hA
          by_cases hB : occluded bd [ma.frm, mb.frm] mb = true
              ∨ (mb.to = ma.frm ∧ occluded bd [ma.frm, mb.frm] ma = true)
          · have hdB := hBstay hB
            obtain ⟨hxa, hya⟩ := inBounds_of_nonvacuum bd ma.frm hvA
            obtain ⟨hxb, hyb⟩ := inBounds_of_nonvacuum bd mb.frm hvB
            exact ⟨_, conserves_of_pair bd _ ma.frm mb.frm _ _ (applyMoves_size bd [ma, mb]) hne
              (by rw [hdA]; exact hxa) (by rw [hdA]; exact hya)
              (by rw [hdB]; exact hxb) (by rw [hdB]; exact hyb)
              (by rw [hdA, hdB]; exact hne) (Or.inl hdA) (Or.inr (Or.inl hdB)) hvA hvB
              (fun c hx hy => applyMoves_cell_TT bd ma mb c hx hy hvA hvB)⟩
          · have hob' : occluded bd [ma.frm, mb.frm] mb = false := by
              cases q : occluded bd [ma.frm, mb.frm] mb
              · rfl
              · exact absurd (Or.inl q) hB
            have hdB := hBgo hob' (fun h => hB (Or.inr h))
            obtain ⟨hxa, hya⟩ := inBounds_of_nonvacuum bd ma.frm hvA
            have hADB : ma.frm ≠ mb.to := by
              intro h
              have hoa' : occluded bd [ma.frm, mb.frm] ma = false := by
                cases q : occluded bd [ma.frm, mb.frm] ma
                · rfl
                · exact absurd (Or.inr ⟨h.symm, q⟩) hB
              rcases hA with q | ⟨-, q⟩
              · exact absurd q (by rw [hoa']; exact Bool.noConfusion)
              · exact absurd q (by rw [hob']; exact Bool.noConfusion)
            refine ⟨_, conserves_of_pair bd _ ma.frm mb.frm _ _ (applyMoves_size bd [ma, mb]) hne
              (by rw [hdA]; exact hxa) (by rw [hdA]; exact hya)
              (by rw [hdB]; exact htbx) (by rw [hdB]; exact htby)
              (by rw [hdA, hdB]; exact hADB) (Or.inl hdA) ?_ hvA hvB
              (fun c hx hy => applyMoves_cell_TT bd ma mb c hx hy hvA hvB)⟩
            rw [hdB]
            rcases hlandB with h | h | h
            · exact Or.inr (Or.inr h)
            · exact absurd h.symm hADB
            · exact absurd h.symm hdb
        · have hoa' : occluded bd [ma.frm, mb.frm] ma = false := by
            cases q : occluded bd [ma.frm, mb.frm] ma
            · rfl
            · exact absurd (Or.inl q) hA
          have hdA := hAgo hoa' (fun h => hA (Or.inr h))
          by_cases hB : occluded bd [ma.frm, mb.frm] mb = true
              ∨ (mb.to = ma.frm ∧ occluded bd [ma.frm, mb.frm] ma = true)
          · have hdB := hBstay hB
            obtain ⟨hxb, hyb⟩ := inBounds_of_nonvacuum bd mb.frm hvB
            have hADB : ma.to ≠ mb.frm := by
              intro h
              have hob' : occluded bd [ma.frm, mb.frm] mb = false := by
                cases q : occluded bd [ma.frm, mb.frm] mb
                · rfl
                · exact absurd (Or.inr ⟨h, q⟩) hA
              rcases hB with q | ⟨-, q⟩
              · exact absurd q (by rw [hob']; exact Bool.noConfusion)
              · exact absurd q (by rw [hoa']; exact Bool.noConfusion)
            refine ⟨_, conserves_of_pair bd _ ma.frm mb.frm _ _ (applyMoves_size bd [ma, mb]) hne
              (by rw [hdA]; exact htax) (by rw [hdA]; exact htay)
              (by rw [hdB]; exact hxb) (by rw [hdB]; exact hyb)
              (by rw [hdA, hdB]; exact hADB) ?_ (Or.inr (Or.inl hdB)) hvA hvB
              (fun c hx hy => applyMoves_cell_TT bd ma mb c hx hy hvA hvB)⟩
            rw [hdA]
            rcases hlandA with h | h | h
            · exact Or.inr (Or.inr h)
            · exact absurd h.symm hda
            · exact absurd h hADB
          · have hob' : occluded bd [ma.frm, mb.frm] mb = false := by
              cases q : occluded bd [ma.frm, mb.frm] mb
              · rfl
              · exact absurd (Or.inl q) hB
            have hdB := hBgo hob' (fun h => hB (Or.inr h))
            have hADB : ma.to ≠ mb.to := by
              intro h
              exact absurd (Or.inr ⟨h, hne, hvA, hvB⟩) hsurv
            refine ⟨_, conserves_of_pair bd _ ma.frm mb.frm _ _ (applyMoves_size bd [ma, mb]) hne
              (by rw [hdA]; exact htax) (by rw [hdA]; exact htay)
              (by rw [hdB]; exact htbx) (by rw [hdB]; exact htby)
              (by rw [hdA, hdB]; exact hADB) ?_ ?_ hvA hvB
              (fun c hx hy => applyMoves_cell_TT bd ma mb c hx hy hvA hvB)⟩
            · rw [hdA]
              rcases hlandA with h | h | h
              · exact Or.inr (Or.inr h)
              · exact absurd h.symm hda
              · exact Or.inr (Or.inl h)
            · rw [hdB]
              rcases hlandB with h | h | h
              · exact Or.inr (Or.inr h)
              · exact Or.inl h
              · exact absurd h.symm hdb

/-! ### §8e.1  NON-VACUITY: the PRE-FIX chain REFUTES the conservation theorem.

A conservation theorem is only load-bearing if the bug it forbids could actually violate it.
`followChainBuggy` is the reference EXACTLY as it stood before defect #8 was fixed — one branch
differs, the caterpillar's.  On `stayerBoard`, where EVERY hypothesis of
`applyMoves_conserves_pieces` holds, the pre-fix resolution makes a repulsor vanish from the board,
so no `φ` whatever can satisfy `ConservesPieces`.  The fixed reference keeps it. -/

/-- **THE PRE-FIX CHAIN.**  Identical to `followChain` except in defect #8's branch, where it lands
on `nxt` whether or not the piece standing there can move.  Kept only as the falsifier. -/
def followChainBuggy (nextC : Coord → Option Coord) (pieceSrcs : List Coord)
    (start : Coord) (visited : List Coord) (fuel : Nat) : Coord :=
  match fuel with
  | 0        => start
  | fuel + 1 =>
    match nextC start with
    | .none     => start
    | .some nxt =>
      if visited.contains nxt then start
      else if pieceSrcs.contains nxt then nxt
      else match nextC nxt with
        | .none   => nxt
        | .some _ => followChainBuggy nextC pieceSrcs nxt (start :: visited) fuel

/-- `applyMoves` driven by the pre-fix chain. -/
def applyMovesBuggy (b : Board) (moves : List Move) : Board :=
  let srcs      := moves.map (·.frm)
  let nextC     := nextOf b moves srcs
  let pieceSrcs := srcs.filter (fun c => ¬ (b.cellAt c).isVacuum)
  let fuel      := moves.length + 1
  let journeys  : List Journey :=
    pieceSrcs.map (fun s =>
      { src := s, dest := followChainBuggy nextC pieceSrcs s [] fuel, particle := b.cellAt s })
  let clearedSrc (c : Coord) : Bool := pieceSrcs.contains c
  { b with
    conflictAt := fun _ => false,
    cells := fun c =>
      match journeys.find? (fun j => j.dest = c) with
      | .some j => j.particle
      | .none   => if clearedSrc c then .vacuum else b.cellAt c }

/-- 3×3.  A carries an attractor at `(0,0)` and wants `(0,2)`, but `(0,1)` holds a NON-SOURCE
attractor, so A is OCCLUDED and stays.  B carries a repulsor at `(1,0)` and targets `(0,0)` — a
square whose occupant does not vacate, so B's move must FAIL TO EXECUTE. -/
def stayerBoard : Board :=
  mkBoard 3 [(⟨0, 0⟩, .attractor), (⟨1, 0⟩, .repulsor), (⟨0, 1⟩, .attractor)] ⟨2, 2⟩
def stayerA : Move := { who := 0, frm := ⟨0, 0⟩, to := ⟨0, 2⟩ }
def stayerB : Move := { who := 1, frm := ⟨1, 0⟩, to := ⟨0, 0⟩ }

/-- **THE FALSIFIER, MACHINE-CHECKED.**  Every hypothesis of `applyMoves_conserves_pieces` holds on
this board — the blocker is an OCCLUDER, never a move target, so `hlandA`/`hlandB` are satisfied —
A is genuinely occluded, and the two references DISAGREE: the fixed one leaves B's repulsor on
`(1,0)`, the pre-fix one leaves NO repulsor anywhere on the board. -/
theorem landsOnStayer_witness :
    MoveValid stayerBoard stayerA ∧ MoveValid stayerBoard stayerB
      ∧ ¬ ((stayerA.frm = stayerB.frm ∧ stayerA.to ≠ stayerB.to)
            ∨ (stayerA.to = stayerB.to ∧ stayerA.frm ≠ stayerB.frm
               ∧ (stayerBoard.cellAt stayerA.frm).isVacuum = false
               ∧ (stayerBoard.cellAt stayerB.frm).isVacuum = false))
      ∧ ((stayerBoard.cellAt stayerA.to).isVacuum = true
            ∨ stayerA.to = stayerA.frm ∨ stayerA.to = stayerB.frm)
      ∧ ((stayerBoard.cellAt stayerB.to).isVacuum = true
            ∨ stayerB.to = stayerA.frm ∨ stayerB.to = stayerB.frm)
      ∧ occluded stayerBoard [stayerA.frm, stayerB.frm] stayerA = true
      ∧ occluded stayerBoard [stayerA.frm, stayerB.frm] stayerB = false
      ∧ stayerBoard.cellAt ⟨1, 0⟩ = Particle.repulsor
      ∧ (applyMoves stayerBoard [stayerA, stayerB]).cellAt ⟨1, 0⟩ = Particle.repulsor
      ∧ (∀ x, x < 3 → ∀ y, y < 3 →
          (applyMovesBuggy stayerBoard [stayerA, stayerB]).cellAt ⟨x, y⟩ ≠ Particle.repulsor) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

/-- **THE CONSERVATION THEOREM IS LOAD-BEARING.**  No `φ` whatever witnesses `ConservesPieces` for
the PRE-FIX resolution on `stayerBoard`: a piece is simply gone.  Since every hypothesis of
`applyMoves_conserves_pieces` holds there (`landsOnStayer_witness`), the theorem would be FALSE for
the pre-fix `followChain` — it is not a statement that survives the bug. -/
theorem buggy_refutes_conservation (φ : Coord → Coord)
    (h : ConservesPieces stayerBoard (applyMovesBuggy stayerBoard [stayerA, stayerB]) φ) : False := by
  have hval : stayerBoard.cellAt ⟨1, 0⟩ = Particle.repulsor := by decide
  have hc := h.carry ⟨1, 0⟩ (by decide)
  rw [hval] at hc
  have hin : (φ ⟨1, 0⟩).x < 3 ∧ (φ ⟨1, 0⟩).y < 3 :=
    inBounds_of_nonvacuum _ (φ ⟨1, 0⟩) (by rw [hc]; decide)
  have hno : ∀ x, x < 3 → ∀ y, y < 3 →
      (applyMovesBuggy stayerBoard [stayerA, stayerB]).cellAt ⟨x, y⟩ ≠ Particle.repulsor := by
    decide
  exact hno (φ ⟨1, 0⟩).x hin.1 (φ ⟨1, 0⟩).y hin.2 hc

end Conserve

/-! ## §9  Axiom-cleanliness self-check (no `native_decide`; core axioms only). -/

#print axioms moveValidB_iff
#print axioms automatonOffset_bounded
#print axioms automatonStep_preserves_inBounds
#print axioms winner_sound
#print axioms applyTurn_preserves_inBounds
#print axioms automatafl_air_refines_applyTurn
#print axioms automatonStep_congr
#print axioms applyMoves_cell_TT
#print axioms applyMoves_cell_TF
#print axioms applyMoves_cell_FT
#print axioms applyMoves_cell_FF
#print axioms followChain_landing_has_edge
#print axioms chainDest_aN
#print axioms chainDest_bN
#print axioms conserves_of_single
#print axioms conserves_of_pair
#print axioms applyMoves_conserves_pieces
#print axioms landsOnStayer_witness
#print axioms buggy_refutes_conservation

end Dregg2.Games.Automatafl
