/-
# Relay Repair — pay a damaged relay's way back onto the grid

Five physical links join the intake `alpha` to the mast `omega` through the beta and
gamma feeds and the shared delta rail, so exactly two source-to-sink routes exist and
both are three links long.  Installing a link spends that link's *cost* out of a
salvage crate, and both are seeded: `boardFromRunSeed` reads the precommitted run
seed and selects one of eight damage boards, each pricing the five links and the
crate.  A run therefore has to read the damage report before it commits.

Two budgets bind and one of them can be spent into a dead end.  `MAX_TURNS` equals
the length of the shortest route, so every install must be on a route the crate can
still pay for; a run that mixes feeds, or that buys a link it cannot follow through
on, reaches a state from which no route completes.  That state is not a trap the
player has to detect: `completableB` is part of `openB`, so a stranded relay refuses
every further action rather than taking more spares for a run it already knows is
dead.  Failure is representable, legible and reachable — `every_board_can_be_lost`.

The canonical state stores the installed links and the turn count only.  Spares and
route availability are projections of the panel against the board, so a drifting
counter cannot exist.
-/
import Dregg2.Games.PathOfAngels.Core
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.RelayRepair

open Dregg2.Games.PathOfAngels

/-- Equal to the length of every source-to-sink route, so the turn budget binds
exactly: see `win_needs_the_whole_budget`. -/
abbrev MAX_TURNS : Nat := 3

inductive Link where
  | alphaBeta
  | alphaGamma
  | betaDelta
  | gammaDelta
  | deltaOmega
deriving Repr, DecidableEq

def allLinks : List Link :=
  [.alphaBeta, .alphaGamma, .betaDelta, .gammaDelta, .deltaOmega]

theorem allLinks_complete (a : Link) : a ∈ allLinks := by
  cases a <;> simp [allLinks]

/-- Exactly the two simple alpha-to-omega paths in the relay graph.  The emitted
descriptor publishes the same graph as `from`/`to` on every action, and the design
gate re-derives these routes from it and refuses on disagreement. -/
def routes : List (List Link) :=
  [[.alphaBeta, .betaDelta, .deltaOmega], [.alphaGamma, .gammaDelta, .deltaOmega]]

/-- Installed topology is canonical; route availability is derived below. -/
structure Panel where
  alphaBeta : Bool
  alphaGamma : Bool
  betaDelta : Bool
  gammaDelta : Bool
  deltaOmega : Bool
deriving Repr, DecidableEq

def emptyPanel : Panel :=
  { alphaBeta := false, alphaGamma := false, betaDelta := false, gammaDelta := false,
    deltaOmega := false }

def installed (p : Panel) : Link → Bool
  | .alphaBeta => p.alphaBeta
  | .alphaGamma => p.alphaGamma
  | .betaDelta => p.betaDelta
  | .gammaDelta => p.gammaDelta
  | .deltaOmega => p.deltaOmega

def install (p : Panel) : Link → Panel
  | .alphaBeta => { p with alphaBeta := true }
  | .alphaGamma => { p with alphaGamma := true }
  | .betaDelta => { p with betaDelta := true }
  | .gammaDelta => { p with gammaDelta := true }
  | .deltaOmega => { p with deltaOmega := true }

def routedB (p : Panel) : Bool :=
  routes.any fun route => route.all (installed p)

def installedCount (p : Panel) : Nat :=
  (allLinks.filter (installed p)).length

/-! ## The seeded damage board -/

/-- One instance: what the salvaged crate holds, and what each damaged link costs to
install.  Every cost is at least one spare, so a link is never free. -/
structure Board where
  spares : Nat
  alphaBeta : Nat
  alphaGamma : Nat
  betaDelta : Nat
  gammaDelta : Nat
  deltaOmega : Nat
deriving Repr, DecidableEq

def cost (b : Board) : Link → Nat
  | .alphaBeta => b.alphaBeta
  | .alphaGamma => b.alphaGamma
  | .betaDelta => b.betaDelta
  | .gammaDelta => b.gammaDelta
  | .deltaOmega => b.deltaOmega

/-- The eight damage boards a run seed can select.  They are not eight relabellings
of one puzzle: three distinct affordable-route shapes occur (beta feed only, gamma
feed only, either feed), which is what makes reading the report load-bearing. -/
def boardTable : List Board :=
  [ { spares := 5, alphaBeta := 1, alphaGamma := 2, betaDelta := 1, gammaDelta := 1,
      deltaOmega := 2 }
  , { spares := 4, alphaBeta := 3, alphaGamma := 1, betaDelta := 2, gammaDelta := 1,
      deltaOmega := 1 }
  , { spares := 6, alphaBeta := 1, alphaGamma := 3, betaDelta := 2, gammaDelta := 2,
      deltaOmega := 1 }
  , { spares := 5, alphaBeta := 2, alphaGamma := 2, betaDelta := 3, gammaDelta := 1,
      deltaOmega := 2 }
  , { spares := 6, alphaBeta := 2, alphaGamma := 4, betaDelta := 1, gammaDelta := 3,
      deltaOmega := 2 }
  , { spares := 7, alphaBeta := 3, alphaGamma := 2, betaDelta := 3, gammaDelta := 3,
      deltaOmega := 1 }
  , { spares := 4, alphaBeta := 1, alphaGamma := 1, betaDelta := 1, gammaDelta := 1,
      deltaOmega := 2 }
  , { spares := 8, alphaBeta := 4, alphaGamma := 1, betaDelta := 3, gammaDelta := 2,
      deltaOmega := 1 } ]

theorem boardTable_length : boardTable.length = 8 := rfl

/-- Total by construction: no default board, so no board exists outside the table. -/
def boardAt (i : Fin 8) : Board :=
  boardTable.get (Fin.cast boardTable_length.symm i)

theorem boardAt_mem : ∀ i : Fin 8, boardAt i ∈ boardTable := by decide +kernel

/-- A byte modulo eight is uniform over the 256 byte values, so the board draw
carries no modulo bias.  The seed is precommitted in `MissionSpec.runSeed`, and
`Config.board_eq` binds the played board to it. -/
def boardFromRunSeed (runSeed : Digest32) : Fin 8 :=
  ⟨(runSeed.bytes.getD 0 0).val % 8, Nat.mod_lt _ (by omega)⟩

/-! ## Spending, routing, and the state machine -/

def linkSum (b : Board) (links : List Link) : Nat :=
  links.foldl (fun acc link => acc + cost b link) 0

def spent (b : Board) (p : Panel) : Nat :=
  linkSum b (allLinks.filter (installed p))

def sparesLeft (b : Board) (p : Panel) : Nat :=
  b.spares - spent b p

def missing (p : Panel) (route : List Link) : List Link :=
  route.filter (fun link => !installed p link)

structure State where
  panel : Panel
  turns : Nat
deriving Repr, DecidableEq

def initialState : State := { panel := emptyPanel, turns := 0 }

abbrev Action := Link

/-- Can the run still finish?  Some route must be completable both in turns and in
spares.  This is a projection of the panel, the clock and the board — never a stored
flag — and it is a conjunct of `openB`, so a relay that can no longer be routed stops
taking spares instead of letting the run fumble. -/
def completableB (b : Board) (s : State) : Bool :=
  routes.any fun route =>
    let rest := missing s.panel route
    decide (rest.length + s.turns ≤ MAX_TURNS) &&
      decide (linkSum b rest ≤ sparesLeft b s.panel)

def strandedB (b : Board) (s : State) : Bool :=
  !routedB s.panel && !completableB b s

def openB (b : Board) (s : State) (a : Action) : Bool :=
  !routedB s.panel &&
  decide (s.turns < MAX_TURNS) &&
  completableB b s &&
  !installed s.panel a &&
  decide (cost b a ≤ sparesLeft b s.panel)

/-- The transition on the semantically relevant argument alone.  `step` below is this
function; the finite tables and the emitter call it directly, so no second relay
transition function exists anywhere in the repository. -/
def stepB (b : Board) (s : State) (a : Action) : Option State :=
  if openB b s a then
    some { panel := install s.panel a, turns := s.turns + 1 }
  else
    none

/-! Each conjunct of `openB`, read back out of an accepted action.  The five
refusal reasons the finite table emits are exactly the negations of these. -/

theorem openB_unrouted (b : Board) (s : State) (a : Action) (h : openB b s a = true) :
    routedB s.panel = false := by
  cases hr : routedB s.panel
  · simp [hr]
  · simp [openB, hr] at h

theorem openB_in_time (b : Board) (s : State) (a : Action) (h : openB b s a = true) :
    s.turns < MAX_TURNS := by
  by_contra hcon
  simp [openB, hcon] at h

theorem openB_completable (b : Board) (s : State) (a : Action) (h : openB b s a = true) :
    completableB b s = true := by
  cases hc : completableB b s
  · simp [openB, hc] at h
  · simp [hc]

theorem openB_fresh (b : Board) (s : State) (a : Action) (h : openB b s a = true) :
    installed s.panel a = false := by
  cases hi : installed s.panel a
  · simp [hi]
  · simp [openB, hi] at h

theorem openB_affordable (b : Board) (s : State) (a : Action) (h : openB b s a = true) :
    cost b a ≤ sparesLeft b s.panel := by
  by_contra hcon
  simp [openB, hcon] at h

def replayB (b : Board) : State → List Action → Option State
  | s, [] => some s
  | s, a :: as =>
      match stepB b s a with
      | none => none
      | some s' => replayB b s' as

structure Config where
  board : Board
  mission : MissionSpec
  reward : Contribution
  reward_accepted : mission.acceptsContribution reward = true
  board_eq : board = boardAt (boardFromRunSeed mission.runSeed)

def step (cfg : Config) (s : State) (a : Action) : Option State := stepB cfg.board s a

def replay (cfg : Config) : State → List Action → Option State := replayB cfg.board

/-- The finite tables and the emitter dispatch `stepB` on the seeded board, which is
this transition and not a copy of it. -/
theorem step_eq_stepB (cfg : Config) (s : State) (a : Action) :
    step cfg s a = stepB cfg.board s a := rfl

theorem replay_eq_replayB (cfg : Config) (s : State) (acts : List Action) :
    replay cfg s acts = replayB cfg.board s acts := rfl

private def terminalOutput (cfg : Config) (s : State) : Option (Contribution × ArtifactRef) :=
  if routedB s.panel then some (cfg.reward, cfg.mission.artifact) else none

def remaining (s : State) : Nat := MAX_TURNS - s.turns

def byte (n : Nat) : Fin 256 := ⟨n % 256, Nat.mod_lt _ (by omega)⟩

def linkCode : Link → Nat
  | .alphaBeta => 0
  | .alphaGamma => 1
  | .betaDelta => 2
  | .gammaDelta => 3
  | .deltaOmega => 4

def actionAt (actions : List Action) (i : Nat) : Nat :=
  match actions[i]? with
  | some a => linkCode a
  | none => 255

def transcriptDigest (actions : List Action) : Digest32 where
  bytes := List.ofFn (fun i : Fin 32 =>
    if i.val = 0 then byte actions.length else byte (actionAt actions (i.val - 1)))
  length_eq := by simp

structure JudgedRun where
  finalState : State
  afterWorld : WorldState
  receipt : RunReceipt

structure JudgeContext where
  actorRoot : Digest32
  playerKey : Digest32
  previousPlayerCounter : Nat

def judge (cfg : Config) (before : WorldState) (ctx : JudgeContext)
    (actions : List Action) : Option JudgedRun :=
  match replay cfg initialState actions with
  | none => none
  | some finalState =>
      match terminalOutput cfg finalState with
      | none => none
      | some (contribution, _artifact) =>
          match happlied : applyContribution cfg.mission contribution before with
          | none => none
          | some afterWorld =>
              some {
                finalState
                afterWorld
                receipt := {
                  mission := cfg.mission
                  federationId := cfg.mission.federationId
                  contentRoot := cfg.mission.contentRoot
                  activationDigest := cfg.mission.activationDigest
                  contentSession := cfg.mission.contentSession
                  contentEpoch := cfg.mission.epoch
                  actorRoot := ctx.actorRoot
                  playerKey := ctx.playerKey
                  previousPlayerCounter := ctx.previousPlayerCounter
                  playerCounter := ctx.previousPlayerCounter + 1
                  runSeed := cfg.mission.runSeed
                  preWorld := before
                  postWorld := afterWorld
                  contribution
                  transcriptDigest := transcriptDigest actions
                  federation_matches := rfl
                  content_root_matches := rfl
                  activation_matches := rfl
                  content_session_matches := rfl
                  content_epoch_matches := rfl
                  run_seed_matches := rfl
                  player_counter_advances := rfl
                  applied := happlied
                }
              }

/-! ## Routing -/

theorem routedB_iff_route (p : Panel) :
    routedB p = true ↔
      (p.alphaBeta = true ∧ p.betaDelta = true ∧ p.deltaOmega = true) ∨
      (p.alphaGamma = true ∧ p.gammaDelta = true ∧ p.deltaOmega = true) := by
  obtain ⟨aB, aG, bD, gD, dO⟩ := p
  cases aB <;> cases aG <;> cases bD <;> cases gD <;> cases dO <;>
    simp [routedB, routes, installed]

/-- No route is shorter than the budget, so no win is. -/
theorem routed_needs_the_budget (p : Panel) (h : routedB p = true) :
    MAX_TURNS ≤ installedCount p := by
  -- Every field is a `Bool`, so after `cases` the goal is closed and `decide`
  -- settles all 32 panels uniformly.
  --
  -- ⚠ This was `first | simp_all […] | (revert h; decide)` and it left unsolved
  -- goals, which Lean discharges with `sorryAx` — silently poisoning
  -- `win_needs_the_whole_budget` and `judged_run_spent_the_budget` downstream.
  -- `first` commits to its first branch that does not FAIL, and `simp_all`
  -- succeeds-without-closing on the panels that route, so `decide` was never
  -- reached on exactly the cases that needed it. The axiom-hygiene gate caught
  -- it; the design numbers did not, because a solver reads the emitted table and
  -- an unproved lemma emits the same table as a proved one.
  obtain ⟨aB, aG, bD, gD, dO⟩ := p
  cases aB <;> cases aG <;> cases bD <;> cases gD <;> cases dO <;>
    revert h <;> decide

/-! ## Spending is exact -/

theorem installedCount_install (p : Panel) (a : Action) (h : installed p a = false) :
    installedCount (install p a) = installedCount p + 1 := by
  obtain ⟨aB, aG, bD, gD, dO⟩ := p
  cases a <;> cases aB <;> cases aG <;> cases bD <;> cases gD <;> cases dO <;>
    revert h <;> decide

theorem spent_install (b : Board) (p : Panel) (a : Action) (h : installed p a = false) :
    spent b (install p a) = spent b p + cost b a := by
  revert h
  obtain ⟨aB, aG, bD, gD, dO⟩ := p
  cases a <;> cases aB <;> cases aG <;> cases bD <;> cases gD <;> cases dO <;>
    simp [spent, linkSum, allLinks, install, installed, cost, List.filter_cons, List.filter_nil] <;> omega

/-- The crate is never overdrawn.  Nat subtraction in `sparesLeft` therefore never
silently clamps a negative balance to zero on a reachable state. -/
def withinCrateB (b : Board) (p : Panel) : Bool := decide (spent b p ≤ b.spares)

theorem withinCrate_initial (b : Board) : withinCrateB b initialState.panel = true := by
  simp [withinCrateB, spent, initialState, emptyPanel, installed, allLinks, linkSum]

theorem step_stays_within_crate (b : Board) (s s' : State) (a : Action)
    (hin : withinCrateB b s.panel = true) (h : stepB b s a = some s') :
    withinCrateB b s'.panel = true := by
  simp only [stepB] at h
  split at h
  · rename_i hopen
    have hni := openB_fresh b s a hopen
    have haff := openB_affordable b s a hopen
    simp only [Option.some.injEq] at h
    subst s'
    simp only [withinCrateB, decide_eq_true_eq] at hin ⊢
    rw [spent_install b s.panel a hni]
    simp only [sparesLeft] at haff
    omega
  · contradiction

theorem step_spends_exactly (b : Board) (s s' : State) (a : Action)
    (hin : withinCrateB b s.panel = true) (h : stepB b s a = some s') :
    sparesLeft b s'.panel + cost b a = sparesLeft b s.panel := by
  simp only [stepB] at h
  split at h
  · rename_i hopen
    have hni := openB_fresh b s a hopen
    have haff := openB_affordable b s a hopen
    simp only [Option.some.injEq] at h
    subst s'
    simp only [withinCrateB, decide_eq_true_eq] at hin
    simp only [sparesLeft] at haff ⊢
    rw [spent_install b s.panel a hni]
    omega
  · contradiction

/-! ## The clock -/

theorem step_deterministic (b : Board) (s : State) (a : Action) {s₁ s₂ : State}
    (h₁ : stepB b s a = some s₁) (h₂ : stepB b s a = some s₂) : s₁ = s₂ := by
  rw [h₁] at h₂
  exact Option.some.inj h₂

theorem step_some_turns (b : Board) (s : State) (a : Action) {s' : State}
    (h : stepB b s a = some s') : s'.turns = s.turns + 1 := by
  simp only [stepB] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst s'
    rfl
  · contradiction

theorem step_some_bound (b : Board) (s : State) (a : Action) {s' : State}
    (h : stepB b s a = some s') : s'.turns ≤ MAX_TURNS := by
  simp only [stepB] at h
  split at h
  · rename_i hopen
    have hlt := openB_in_time b s a hopen
    simp only [Option.some.injEq] at h
    subst s'
    simp only
    omega
  · contradiction

theorem remaining_strictly_decreases (b : Board) (s : State) (a : Action) {s' : State}
    (h : stepB b s a = some s') : remaining s' < remaining s := by
  have ht := step_some_turns b s a h
  have hb := step_some_bound b s a h
  simp only [remaining]
  omega

theorem step_installs_one (b : Board) (s : State) (a : Action) {s' : State}
    (h : stepB b s a = some s') :
    installedCount s'.panel = installedCount s.panel + 1 := by
  simp only [stepB] at h
  split at h
  · rename_i hopen
    have hni := openB_fresh b s a hopen
    simp only [Option.some.injEq] at h
    subst s'
    exact installedCount_install s.panel a hni
  · contradiction

/-! ## Refusals — each of the five emitted reasons is a theorem -/

theorem solved_refuses (b : Board) (s : State) (a : Action) (h : routedB s.panel = true) :
    stepB b s a = none := by
  simp [stepB, openB, h]

theorem exhausted_refuses (b : Board) (s : State) (a : Action) (h : MAX_TURNS ≤ s.turns) :
    stepB b s a = none := by
  simp [stepB, openB, Nat.not_lt.mpr h]

theorem duplicate_link_refused (b : Board) (s : State) (a : Action)
    (h : installed s.panel a = true) : stepB b s a = none := by
  simp [stepB, openB, h]

theorem unaffordable_link_refused (b : Board) (s : State) (a : Action)
    (h : sparesLeft b s.panel < cost b a) : stepB b s a = none := by
  simp [stepB, openB, Nat.not_le.mpr h]

/-- A stranded relay refuses *every* action, so a lost run cannot keep spending. -/
theorem stranded_refuses_everything (b : Board) (s : State) (a : Action)
    (h : completableB b s = false) : stepB b s a = none := by
  simp [stepB, openB, h]

/-! ## Replay -/

theorem replayB_append (b : Board) (s : State) (xs ys : List Action) :
    replayB b s (xs ++ ys) = (replayB b s xs).bind (fun s' => replayB b s' ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons a as ih =>
      simp only [List.cons_append, replayB]
      split <;> simp_all

theorem refused_prefix_refuses_replay (b : Board) (s : State) (a : Action)
    (as : List Action) (h : stepB b s a = none) : replayB b s (a :: as) = none := by
  simp [replayB, h]

theorem replayB_counts (b : Board) (acts : List Action) : ∀ (s s' : State),
    replayB b s acts = some s' → installedCount s.panel = s.turns →
      installedCount s'.panel = s'.turns ∧ s'.turns = s.turns + acts.length := by
  induction acts with
  | nil =>
      intro s s' h hinv
      simp only [replayB, Option.some.injEq] at h
      subst h
      exact ⟨hinv, by simp⟩
  | cons a as ih =>
      intro s s' h hinv
      simp only [replayB] at h
      split at h
      · contradiction
      · rename_i s₁ hstep
        have hc := step_installs_one b s a hstep
        have ht := step_some_turns b s a hstep
        have hih := ih s₁ s' h (by omega)
        refine ⟨hih.1, ?_⟩
        have h2 := hih.2
        simp only [List.length_cons]
        omega

/-- **The turn budget binds.**  No accepted play shorter than `MAX_TURNS` is ever
rewarded, and `step_some_bound` forbids a longer one, so every win is exactly
`MAX_TURNS` actions.  This is the statement the design gate measures as
`execution floor == action_limit`, proved here for every board and every play. -/
theorem win_needs_the_whole_budget (b : Board) (acts : List Action) (s' : State)
    (h : replayB b initialState acts = some s') (hw : routedB s'.panel = true) :
    MAX_TURNS ≤ acts.length := by
  have hinv : installedCount initialState.panel = initialState.turns := rfl
  have hzero : initialState.turns = 0 := rfl
  have hc := replayB_counts b acts initialState s' h hinv
  have hroute := routed_needs_the_budget s'.panel hw
  obtain ⟨hcount, hturns⟩ := hc
  omega

/-! ## Every seeded instance is winnable, losable, and forks -/

def routeAffordableB (b : Board) (route : List Link) : Bool :=
  decide (route.length ≤ MAX_TURNS) && decide (linkSum b route ≤ b.spares)

/-- The first route the crate can pay for, in the emitted route order. -/
def winningLine (b : Board) : List Action :=
  (routes.find? (routeAffordableB b)).getD []

def playsOutB (b : Board) (acts : List Action) : Bool :=
  match replayB b initialState acts with
  | none => false
  | some s => routedB s.panel

/-- Some accepted two-action play ends on a panel from which no route completes. -/
def losableB (b : Board) : Bool :=
  allLinks.any fun x => allLinks.any fun y =>
    match replayB b initialState [x, y] with
    | none => false
    | some s => strandedB b s

/-- Some reachable state offers one install that keeps the run alive and another,
equally legal, that kills it. -/
def forksB (b : Board) : Bool :=
  allLinks.any fun x =>
    match replayB b initialState [x] with
    | none => false
    | some s =>
        (allLinks.any fun y =>
          match stepB b s y with
          | none => false
          | some t => routedB t.panel || completableB b t) &&
        (allLinks.any fun y =>
          match stepB b s y with
          | none => false
          | some t => !routedB t.panel && !completableB b t)

/-- Not one instance: every board the seed can select is solvable by an accepted
play, so no draw is a dead mission. -/
theorem every_board_has_an_accepted_win :
    ∀ i : Fin 8, playsOutB (boardAt i) (winningLine (boardAt i)) = true := by
  decide +kernel

theorem every_win_is_within_budget :
    ∀ i : Fin 8, (winningLine (boardAt i)).length = MAX_TURNS := by
  decide +kernel

/-- Failure is reachable on every board, not merely representable. -/
theorem every_board_can_be_lost : ∀ i : Fin 8, losableB (boardAt i) = true := by
  decide +kernel

/-- On every board some choice changes the outcome, which is what the design gate
counts as an outcome-changing fork. -/
theorem every_board_forks : ∀ i : Fin 8, forksB (boardAt i) = true := by
  decide +kernel

/-- Every link is priced, so no install is free and the crate always binds. -/
theorem every_link_costs_a_spare (a : Link) : ∀ i : Fin 8, 1 ≤ cost (boardAt i) a := by
  cases a <;> decide +kernel

/-! ## Output and receipt -/

theorem terminalOutput_none_without_route (cfg : Config) (s : State)
    (h : routedB s.panel = false) : terminalOutput cfg s = none := by
  simp [terminalOutput, h]

theorem terminalOutput_is_mission_accepted (cfg : Config) (s : State)
    {out : Contribution × ArtifactRef} (h : terminalOutput cfg s = some out) :
    cfg.mission.acceptsContribution out.1 = true := by
  simp only [terminalOutput] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst out
    exact cfg.reward_accepted
  · contradiction

theorem terminalOutput_names_exact_beta_artifact (cfg : Config) (s : State)
    {out : Contribution × ArtifactRef} (h : terminalOutput cfg s = some out) :
    out.2 = cfg.mission.artifact := by
  simp only [terminalOutput] at h
  split at h
  · simp only [Option.some.injEq] at h
    rw [← h]
  · contradiction

theorem terminalOutput_canonical (cfg : Config) (s : State)
    {contribution : Contribution} {artifact : ArtifactRef}
    (h : terminalOutput cfg s = some (contribution, artifact)) :
    terminalOutput cfg s = some (contribution, cfg.mission.artifact) := by
  have hart := terminalOutput_names_exact_beta_artifact cfg s h
  change artifact = cfg.mission.artifact at hart
  rw [hart] at h
  exact h

/-- The board a run is judged on is the one its precommitted seed selects; a host
cannot reprice the relay after seeing the transcript. -/
theorem judged_board_is_the_seeded_board (cfg : Config) :
    cfg.board = boardAt (boardFromRunSeed cfg.mission.runSeed) := cfg.board_eq

theorem judge_some_sound (cfg : Config) (before : WorldState) (ctx : JudgeContext)
    (actions : List Action) {run : JudgedRun} (h : judge cfg before ctx actions = some run) :
    replay cfg initialState actions = some run.finalState ∧
    terminalOutput cfg run.finalState =
      some (run.receipt.contribution, cfg.mission.artifact) ∧
    applyContribution cfg.mission run.receipt.contribution before = some run.afterWorld ∧
    run.receipt.mission = cfg.mission ∧
    run.receipt.transcriptDigest = transcriptDigest actions := by
  unfold judge at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · contradiction
      · simp only [Option.some.injEq] at h
        subst run
        refine ⟨by assumption, ?_, by assumption, rfl, rfl⟩
        apply terminalOutput_canonical
        assumption

theorem judge_receipt_binds_transcript (cfg : Config) (before : WorldState)
    (ctx : JudgeContext) (actions : List Action) {run : JudgedRun}
    (h : judge cfg before ctx actions = some run) :
    run.receipt.transcriptDigest = transcriptDigest actions :=
  (judge_some_sound cfg before ctx actions h).2.2.2.2

/-- A judged win spent the whole budget: the receipt cannot report a two-action
completion of a three-link route. -/
theorem judged_run_spent_the_budget (cfg : Config) (before : WorldState)
    (ctx : JudgeContext) (actions : List Action) {run : JudgedRun}
    (h : judge cfg before ctx actions = some run) : MAX_TURNS ≤ actions.length := by
  have hsound := judge_some_sound cfg before ctx actions h
  have hroute : routedB run.finalState.panel = true := by
    have := hsound.2.1
    simp only [terminalOutput] at this
    split at this
    · assumption
    · contradiction
  exact win_needs_the_whole_budget cfg.board actions run.finalState hsound.1 hroute

#assert_axioms allLinks_complete
#assert_axioms boardAt_mem
#assert_axioms step_eq_stepB
#assert_axioms replay_eq_replayB
#assert_axioms openB_unrouted
#assert_axioms openB_in_time
#assert_axioms openB_completable
#assert_axioms openB_fresh
#assert_axioms openB_affordable
#assert_axioms routedB_iff_route
#assert_axioms routed_needs_the_budget
#assert_axioms installedCount_install
#assert_axioms spent_install
#assert_axioms withinCrate_initial
#assert_axioms step_stays_within_crate
#assert_axioms step_spends_exactly
#assert_axioms step_deterministic
#assert_axioms step_some_turns
#assert_axioms step_some_bound
#assert_axioms step_installs_one
#assert_axioms remaining_strictly_decreases
#assert_axioms solved_refuses
#assert_axioms exhausted_refuses
#assert_axioms duplicate_link_refused
#assert_axioms unaffordable_link_refused
#assert_axioms stranded_refuses_everything
#assert_axioms replayB_append
#assert_axioms refused_prefix_refuses_replay
#assert_axioms replayB_counts
#assert_axioms win_needs_the_whole_budget
#assert_axioms every_board_has_an_accepted_win
#assert_axioms every_win_is_within_budget
#assert_axioms every_board_can_be_lost
#assert_axioms every_board_forks
#assert_axioms every_link_costs_a_spare
#assert_axioms terminalOutput_none_without_route
#assert_axioms terminalOutput_is_mission_accepted
#assert_axioms terminalOutput_names_exact_beta_artifact
#assert_axioms terminalOutput_canonical
#assert_axioms judged_board_is_the_seeded_board
#assert_axioms judge_some_sound
#assert_axioms judge_receipt_binds_transcript
#assert_axioms judged_run_spent_the_budget

end Dregg2.Games.PathOfAngels.RelayRepair
