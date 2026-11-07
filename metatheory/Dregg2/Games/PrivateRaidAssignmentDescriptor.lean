/-
# Dregg2.Games.PrivateRaidAssignmentDescriptor

Lean author for a fixed-four private raid/matchmaking role assignment.

Four public seat indices are assigned the four canonical roles exactly once.
Each participant privately supplies a suitability score in `[0,3]` and an
independent admissibility bit for every role.  The public statement is only
`(session, rule, inputRoot8, assignedRole[0..4))`; scores, admissibility, and
the winning total remain private.

The accepted assignment is feasible, globally maximizes total suitability
over all 24 role permutations, and is the lexicographically lowest assignment
on ties.  Tier-1 trace construction is honest-but-visible: the producer sees
the private matrix.  Hiding from the verifier is supplied by the Rust
`HidingFriPcs` façade, not by this relation alone.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Tactics

namespace Dregg2.Games.PrivateRaidAssignmentDescriptor

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 TableId TraceFamily VmTrace Satisfied2
    ChipTableSoundN chipLookupTupleN chip_lookup_sound_N envAt emitVmJson2)

set_option autoImplicit false

/-! ## 1. Exact semantic relation. -/

def SEAT_COUNT : Nat := 4
def ROLE_COUNT : Nat := 4
def SCORE_BITS : Nat := 2
def DIFF_BITS : Nat := 4
def DIGEST_WIDTH : Nat := 8
def CANDIDATE_COUNT : Nat := 24
def BABYBEAR_MODULUS : Int := 2013265921

/-- ASCII `RAI4`: commitment domain for this exact private-input framing. -/
def ROOT_DOMAIN_TAG : Int := 1380006196

/-- ASCII `RAM4`: fixed N=4, score<4, admissible, max, lex-lowest rule. -/
def RULE_ID : Int := 1380007220

@[ext] structure ParticipantInput where
  scores : Fin 4 → Fin 4
  admissible : Fin 4 → Fin 2

structure PrivateWitness where
  inputs : Fin 4 → ParticipantInput
  blinding : Fin 8 → Int

structure PublicStatement where
  session : Int
  rule : Int
  inputRoot : Fin 8 → Int
  roles : Fin 4 → Fin 4
  deriving DecidableEq, Repr

def CanonicalBlinding (w : PrivateWitness) : Prop :=
  ∀ lane, 0 ≤ w.blinding lane ∧ w.blinding lane < BABYBEAR_MODULUS

def canonicalBlindingCheck (w : PrivateWitness) : Bool :=
  (List.ofFn w.blinding).all fun z =>
    decide (0 ≤ z ∧ z < BABYBEAR_MODULUS)

theorem canonicalBlindingCheck_iff (w : PrivateWitness) :
    canonicalBlindingCheck w = true ↔ CanonicalBlinding w := by
  simp [canonicalBlindingCheck, CanonicalBlinding]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ lane
    fin_cases lane <;> assumption
  · intro h
    exact ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6, h 7⟩

/-- Twelve faithful private bits per participant: four base-4 score digits,
then four independent admissibility bits. -/
def participantPack (input : ParticipantInput) : Int :=
  (input.scores 0).val + 4 * (input.scores 1).val +
  16 * (input.scores 2).val + 64 * (input.scores 3).val +
  256 * (input.admissible 0).val + 512 * (input.admissible 1).val +
  1024 * (input.admissible 2).val + 2048 * (input.admissible 3).val

theorem participantPack_bounds (input : ParticipantInput) :
    0 ≤ participantPack input ∧ participantPack input < 4096 := by
  have s0 := (input.scores 0).isLt; have s1 := (input.scores 1).isLt
  have s2 := (input.scores 2).isLt; have s3 := (input.scores 3).isLt
  have a0 := (input.admissible 0).isLt; have a1 := (input.admissible 1).isLt
  have a2 := (input.admissible 2).isLt; have a3 := (input.admissible 3).isLt
  simp only [participantPack]
  omega

theorem participantPack_injective : Function.Injective participantPack := by
  intro left right h
  have ls0 := (left.scores 0).isLt; have ls1 := (left.scores 1).isLt
  have ls2 := (left.scores 2).isLt; have ls3 := (left.scores 3).isLt
  have la0 := (left.admissible 0).isLt; have la1 := (left.admissible 1).isLt
  have la2 := (left.admissible 2).isLt; have la3 := (left.admissible 3).isLt
  have rs0 := (right.scores 0).isLt; have rs1 := (right.scores 1).isLt
  have rs2 := (right.scores 2).isLt; have rs3 := (right.scores 3).isLt
  have ra0 := (right.admissible 0).isLt; have ra1 := (right.admissible 1).isLt
  have ra2 := (right.admissible 2).isLt; have ra3 := (right.admissible 3).isLt
  have hs0 : (left.scores 0).val = (right.scores 0).val := by
    simp only [participantPack] at h; omega
  have hs1 : (left.scores 1).val = (right.scores 1).val := by
    simp only [participantPack] at h; omega
  have hs2 : (left.scores 2).val = (right.scores 2).val := by
    simp only [participantPack] at h; omega
  have hs3 : (left.scores 3).val = (right.scores 3).val := by
    simp only [participantPack] at h; omega
  have ha0 : (left.admissible 0).val = (right.admissible 0).val := by
    simp only [participantPack] at h; omega
  have ha1 : (left.admissible 1).val = (right.admissible 1).val := by
    simp only [participantPack] at h; omega
  have ha2 : (left.admissible 2).val = (right.admissible 2).val := by
    simp only [participantPack] at h; omega
  have ha3 : (left.admissible 3).val = (right.admissible 3).val := by
    simp only [participantPack] at h; omega
  apply ParticipantInput.ext
  · funext role
    fin_cases role
    · exact Fin.ext hs0
    · exact Fin.ext hs1
    · exact Fin.ext hs2
    · exact Fin.ext hs3
  · funext role
    fin_cases role
    · exact Fin.ext ha0
    · exact Fin.ext ha1
    · exact Fin.ext ha2
    · exact Fin.ext ha3

/-- Two 12-bit participant inputs per canonical BabyBear felt. -/
def packedLow (w : PrivateWitness) : Int :=
  participantPack (w.inputs 0) + 4096 * participantPack (w.inputs 1)

def packedHigh (w : PrivateWitness) : Int :=
  participantPack (w.inputs 2) + 4096 * participantPack (w.inputs 3)

theorem packedInputs_injective {left right : PrivateWitness}
    (hlow : packedLow left = packedLow right)
    (hhigh : packedHigh left = packedHigh right) : left.inputs = right.inputs := by
  have ll0 := participantPack_bounds (left.inputs 0)
  have ll1 := participantPack_bounds (left.inputs 1)
  have rl0 := participantPack_bounds (right.inputs 0)
  have rl1 := participantPack_bounds (right.inputs 1)
  have ll2 := participantPack_bounds (left.inputs 2)
  have ll3 := participantPack_bounds (left.inputs 3)
  have rl2 := participantPack_bounds (right.inputs 2)
  have rl3 := participantPack_bounds (right.inputs 3)
  have h0 : participantPack (left.inputs 0) = participantPack (right.inputs 0) := by
    simp only [packedLow] at hlow; omega
  have h1 : participantPack (left.inputs 1) = participantPack (right.inputs 1) := by
    simp only [packedLow] at hlow; omega
  have h2 : participantPack (left.inputs 2) = participantPack (right.inputs 2) := by
    simp only [packedHigh] at hhigh; omega
  have h3 : participantPack (left.inputs 3) = participantPack (right.inputs 3) := by
    simp only [packedHigh] at hhigh; omega
  funext seat
  fin_cases seat
  · exact participantPack_injective h0
  · exact participantPack_injective h1
  · exact participantPack_injective h2
  · exact participantPack_injective h3

def rootPreimage (session : Int) (w : PrivateWitness) : List Int :=
  [ROOT_DOMAIN_TAG, session, RULE_ID, packedLow w, packedHigh w] ++
    List.ofFn w.blinding ++ [0, 0, 0]

def inputRoot (hash8 : List Int → Fin 8 → Int) (session : Int)
    (w : PrivateWitness) : Fin 8 → Int := hash8 (rootPreimage session w)

def ExactAssignment (roles : Fin 4 → Fin 4) : Prop := Function.Bijective roles

def AdmissibleAssignment (w : PrivateWitness) (roles : Fin 4 → Fin 4) : Prop :=
  ∀ seat, (w.inputs seat).admissible (roles seat) = 1

def totalSuitability (w : PrivateWitness) (roles : Fin 4 → Fin 4) : Int :=
  (List.ofFn fun seat : Fin 4 => ((w.inputs seat).scores (roles seat)).val).sum

/-- Base-4 encoding with seat zero most significant is exactly lexicographic
order on the four public role digits. -/
def lexCode (roles : Fin 4 → Fin 4) : Int :=
  64 * (roles 0).val + 16 * (roles 1).val +
    4 * (roles 2).val + (roles 3).val

theorem lexCode_injective : Function.Injective lexCode := by
  intro left right h
  have l0 := (left 0).isLt; have l1 := (left 1).isLt
  have l2 := (left 2).isLt; have l3 := (left 3).isLt
  have r0 := (right 0).isLt; have r1 := (right 1).isLt
  have r2 := (right 2).isLt; have r3 := (right 3).isLt
  have h0 : (left 0).val = (right 0).val := by
    simp only [lexCode] at h; omega
  have h1 : (left 1).val = (right 1).val := by
    simp only [lexCode] at h; omega
  have h2 : (left 2).val = (right 2).val := by
    simp only [lexCode] at h; omega
  have h3 : (left 3).val = (right 3).val := by
    simp only [lexCode] at h; omega
  funext seat
  fin_cases seat
  · exact Fin.ext h0
  · exact Fin.ext h1
  · exact Fin.ext h2
  · exact Fin.ext h3

def Feasible (w : PrivateWitness) (roles : Fin 4 → Fin 4) : Prop :=
  ExactAssignment roles ∧ AdmissibleAssignment w roles

/-- Global optimum plus deterministic lexicographically-lowest tie break. -/
def OptimalLex (w : PrivateWitness) (roles : Fin 4 → Fin 4) : Prop :=
  Feasible w roles ∧
  ∀ candidate, Feasible w candidate →
    totalSuitability w candidate ≤ totalSuitability w roles ∧
    (totalSuitability w candidate = totalSuitability w roles →
      lexCode roles ≤ lexCode candidate)

theorem optimalLex_unique {w : PrivateWitness} {left right : Fin 4 → Fin 4}
    (hl : OptimalLex w left) (hr : OptimalLex w right) : left = right := by
  have hlr := hl.2 right hr.1
  have hrl := hr.2 left hl.1
  have hscore : totalSuitability w left = totalSuitability w right := by omega
  have hcodeLR : lexCode left ≤ lexCode right := hlr.2 hscore.symm
  have hcodeRL : lexCode right ≤ lexCode left := hrl.2 hscore
  exact lexCode_injective (by omega)

def Accepts (hash8 : List Int → Fin 8 → Int)
    (pub : PublicStatement) (w : PrivateWitness) : Prop :=
  CanonicalBlinding w ∧
  pub.rule = RULE_ID ∧
  pub.inputRoot = inputRoot hash8 pub.session w ∧
  OptimalLex w pub.roles

noncomputable def optimalLexCheck (w : PrivateWitness)
    (roles : Fin 4 → Fin 4) : Bool := by
  classical
  exact decide (OptimalLex w roles)

noncomputable def check (hash8 : List Int → Fin 8 → Int)
    (pub : PublicStatement) (w : PrivateWitness) : Bool :=
  canonicalBlindingCheck w &&
  (pub.rule == RULE_ID) &&
  (pub.inputRoot == inputRoot hash8 pub.session w) &&
  optimalLexCheck w pub.roles

theorem check_iff (hash8 : List Int → Fin 8 → Int)
    (pub : PublicStatement) (w : PrivateWitness) :
    check hash8 pub w = true ↔ Accepts hash8 pub w := by
  classical
  simp [check, optimalLexCheck, Accepts, canonicalBlindingCheck_iff, and_assoc]

theorem check_sound {hash8 : List Int → Fin 8 → Int}
    {pub : PublicStatement} {w : PrivateWitness}
    (h : check hash8 pub w = true) :
    CanonicalBlinding w ∧ pub.rule = RULE_ID ∧
    pub.inputRoot = inputRoot hash8 pub.session w ∧
    Feasible w pub.roles ∧
    ∀ candidate, Feasible w candidate →
      totalSuitability w candidate ≤ totalSuitability w pub.roles ∧
      (totalSuitability w candidate = totalSuitability w pub.roles →
        lexCode pub.roles ≤ lexCode candidate) := by
  exact (check_iff hash8 pub w).mp h

def RootCollision (hash8 : List Int → Fin 8 → Int) (session : Int)
    (left right : PrivateWitness) : Prop :=
  (left.inputs ≠ right.inputs ∨ left.blinding ≠ right.blinding) ∧
    inputRoot hash8 session left = inputRoot hash8 session right

theorem two_distinct_openings_yield_root_collision
    {hash8 : List Int → Fin 8 → Int} {pub : PublicStatement}
    {left right : PrivateWitness}
    (hl : check hash8 pub left = true) (hr : check hash8 pub right = true)
    (hdiff : left.inputs ≠ right.inputs ∨ left.blinding ≠ right.blinding) :
    RootCollision hash8 pub.session left right := by
  have al := (check_iff hash8 pub left).mp hl
  have ar := (check_iff hash8 pub right).mp hr
  exact ⟨hdiff, al.2.2.1.symm.trans ar.2.2.1⟩

/-! ## 2. Exhaustive fixed candidate set. -/

/-- The 24 permutations in increasing lexicographic order. -/
def candidateRows : List (List Nat) :=
  [ [0, 1, 2, 3], [0, 1, 3, 2], [0, 2, 1, 3], [0, 2, 3, 1]
  , [0, 3, 1, 2], [0, 3, 2, 1], [1, 0, 2, 3], [1, 0, 3, 2]
  , [1, 2, 0, 3], [1, 2, 3, 0], [1, 3, 0, 2], [1, 3, 2, 0]
  , [2, 0, 1, 3], [2, 0, 3, 1], [2, 1, 0, 3], [2, 1, 3, 0]
  , [2, 3, 0, 1], [2, 3, 1, 0], [3, 0, 1, 2], [3, 0, 2, 1]
  , [3, 1, 0, 2], [3, 1, 2, 0], [3, 2, 0, 1], [3, 2, 1, 0] ]

def roleRow (roles : Fin 4 → Fin 4) : List Nat :=
  List.ofFn fun seat => (roles seat).val

theorem candidateRows_cover_values :
    ∀ a b c d : Fin 4,
      [a.val, b.val, c.val, d.val].Nodup →
      [a.val, b.val, c.val, d.val] ∈ candidateRows := by
  decide

theorem candidateRows_complete
    (roles : Fin 4 → Fin 4) (h : ExactAssignment roles) :
    roleRow roles ∈ candidateRows := by
  have h01 : roles 0 ≠ roles 1 := by
    intro heq
    have := h.1 heq
    omega
  have h02 : roles 0 ≠ roles 2 := by
    intro heq
    have := h.1 heq
    omega
  have h03 : roles 0 ≠ roles 3 := by
    intro heq
    have := h.1 heq
    omega
  have h12 : roles 1 ≠ roles 2 := by
    intro heq
    have := h.1 heq
    omega
  have h13 : roles 1 ≠ roles 3 := by
    intro heq
    have := h.1 heq
    omega
  have h23 : roles 2 ≠ roles 3 := by
    intro heq
    have := h.1 heq
    omega
  have hv01 : (roles 0).val ≠ (roles 1).val := fun heq => h01 (Fin.ext heq)
  have hv02 : (roles 0).val ≠ (roles 2).val := fun heq => h02 (Fin.ext heq)
  have hv03 : (roles 0).val ≠ (roles 3).val := fun heq => h03 (Fin.ext heq)
  have hv12 : (roles 1).val ≠ (roles 2).val := fun heq => h12 (Fin.ext heq)
  have hv13 : (roles 1).val ≠ (roles 3).val := fun heq => h13 (Fin.ext heq)
  have hv23 : (roles 2).val ≠ (roles 3).val := fun heq => h23 (Fin.ext heq)
  have hnVal :
      [(roles 0).val, (roles 1).val, (roles 2).val, (roles 3).val].Nodup := by
    simp_all
  have hrow : roleRow roles = [(roles 0).val, (roles 1).val, (roles 2).val, (roles 3).val] := rfl
  rw [hrow]
  exact candidateRows_cover_values (roles 0) (roles 1) (roles 2) (roles 3) hnVal

theorem candidateRows_shape :
    candidateRows.length = 24 ∧
    ∀ row ∈ candidateRows,
      row.length = 4 ∧ row.Nodup ∧ ∀ role ∈ row, role < 4 := by
  decide

#guard candidateRows.length == CANDIDATE_COUNT

/-! ## 3. Lean-authored fixed AIR descriptor. -/

def SESSION : Nat := 0
def RULE : Nat := 1
def ROOT_BASE : Nat := 2
def SCORE_BASE : Nat := 10
def SCORE_BIT_BASE : Nat := 26
def ADMISSIBLE_BASE : Nat := 58
def ASSIGNED_BASE : Nat := 74
def SELECT_BASE : Nat := 78
def TOTAL : Nat := 94
def TOTAL_BIT_BASE : Nat := 95
def BLIND_BASE : Nat := 99
def CANDIDATE_CHOSEN_BASE : Nat := 107
def CANDIDATE_ALLOWED_BASE : Nat := 131
def DIFF_BASE : Nat := 155
def DIFF_BIT_BASE : Nat := 179
def DIFF_NONZERO_BASE : Nat := 275
def TRACE_WIDTH : Nat := 299

def ROOT (lane : Nat) : Nat := ROOT_BASE + lane
def SCORE (seat role : Nat) : Nat := SCORE_BASE + ROLE_COUNT * seat + role
def SCORE_BIT (seat role bit : Nat) : Nat :=
  SCORE_BIT_BASE + SCORE_BITS * (ROLE_COUNT * seat + role) + bit
def ADMISSIBLE (seat role : Nat) : Nat :=
  ADMISSIBLE_BASE + ROLE_COUNT * seat + role
def ASSIGNED (seat : Nat) : Nat := ASSIGNED_BASE + seat
def SELECT (seat role : Nat) : Nat := SELECT_BASE + ROLE_COUNT * seat + role
def TOTAL_BIT (bit : Nat) : Nat := TOTAL_BIT_BASE + bit
def BLIND (lane : Nat) : Nat := BLIND_BASE + lane
def CANDIDATE_CHOSEN (candidate : Nat) : Nat := CANDIDATE_CHOSEN_BASE + candidate
def CANDIDATE_ALLOWED (candidate : Nat) : Nat := CANDIDATE_ALLOWED_BASE + candidate
def DIFF (candidate : Nat) : Nat := DIFF_BASE + candidate
def DIFF_BIT (candidate bit : Nat) : Nat := DIFF_BIT_BASE + DIFF_BITS * candidate + bit
def DIFF_NONZERO (candidate : Nat) : Nat := DIFF_NONZERO_BASE + candidate

def v (col : Nat) : EmittedExpr := .var col
def c (z : Int) : EmittedExpr := .const z
def add (x y : EmittedExpr) : EmittedExpr := .add x y
def mul (x y : EmittedExpr) : EmittedExpr := .mul x y
def neg (x : EmittedExpr) : EmittedExpr := mul (c (-1)) x
def sub (x y : EmittedExpr) : EmittedExpr := add x (neg y)
def sumE (xs : List EmittedExpr) : EmittedExpr := xs.foldr add (c 0)
def prodE (xs : List EmittedExpr) : EmittedExpr := xs.foldr mul (c 1)
def weighted (k : Int) (x : EmittedExpr) : EmittedExpr := mul (c k) x
def binaryBody (col : Nat) : EmittedExpr := mul (v col) (sub (v col) (c 1))

def recompose (col : Nat) (bit : Nat → Nat) (bits : Nat) : EmittedExpr :=
  sub (sumE ((List.range bits).map fun b => weighted (2 ^ b) (v (bit b)))) (v col)

def participantPackExpr (seat : Nat) : EmittedExpr :=
  sumE
    [ v (SCORE seat 0), weighted 4 (v (SCORE seat 1))
    , weighted 16 (v (SCORE seat 2)), weighted 64 (v (SCORE seat 3))
    , weighted 256 (v (ADMISSIBLE seat 0)), weighted 512 (v (ADMISSIBLE seat 1))
    , weighted 1024 (v (ADMISSIBLE seat 2)), weighted 2048 (v (ADMISSIBLE seat 3)) ]

def packedLowExpr : EmittedExpr :=
  add (participantPackExpr 0) (weighted 4096 (participantPackExpr 1))

def packedHighExpr : EmittedExpr :=
  add (participantPackExpr 2) (weighted 4096 (participantPackExpr 3))

def rootInputExprs : List EmittedExpr :=
  [c ROOT_DOMAIN_TAG, v SESSION, v RULE, packedLowExpr, packedHighExpr] ++
    (List.range DIGEST_WIDTH).map (fun lane => v (BLIND lane)) ++ [c 0, c 0, c 0]

def rootDigestCols : List Nat := (List.range DIGEST_WIDTH).map ROOT

def rootLookup : VmConstraint2 :=
  .lookup { table := .poseidon2, tuple := chipLookupTupleN rootInputExprs rootDigestCols }

def scoreBitBodies : List EmittedExpr :=
  (List.range SEAT_COUNT).flatMap fun seat =>
    (List.range ROLE_COUNT).flatMap fun role =>
      (List.range SCORE_BITS).map fun bit => binaryBody (SCORE_BIT seat role bit)

def scoreRecomposeBodies : List EmittedExpr :=
  (List.range SEAT_COUNT).flatMap fun seat =>
    (List.range ROLE_COUNT).map fun role =>
      recompose (SCORE seat role) (SCORE_BIT seat role) SCORE_BITS

def admissibleBitBodies : List EmittedExpr :=
  (List.range SEAT_COUNT).flatMap fun seat =>
    (List.range ROLE_COUNT).map fun role => binaryBody (ADMISSIBLE seat role)

def selectBitBodies : List EmittedExpr :=
  (List.range SEAT_COUNT).flatMap fun seat =>
    (List.range ROLE_COUNT).map fun role => binaryBody (SELECT seat role)

def selectRowBodies : List EmittedExpr :=
  (List.range SEAT_COUNT).map fun seat =>
    sub (sumE ((List.range ROLE_COUNT).map fun role => v (SELECT seat role))) (c 1)

def selectColumnBodies : List EmittedExpr :=
  (List.range ROLE_COUNT).map fun role =>
    sub (sumE ((List.range SEAT_COUNT).map fun seat => v (SELECT seat role))) (c 1)

def assignedRecomposeBodies : List EmittedExpr :=
  (List.range SEAT_COUNT).map fun seat =>
    sub (v (ASSIGNED seat))
      (sumE ((List.range ROLE_COUNT).map fun (role : Nat) =>
        weighted role (v (SELECT seat role))))

def chosenAdmissibleBodies : List EmittedExpr :=
  (List.range SEAT_COUNT).map fun seat =>
    sumE ((List.range ROLE_COUNT).map fun role =>
      mul (v (SELECT seat role)) (sub (c 1) (v (ADMISSIBLE seat role))))

def selectedTotalExpr : EmittedExpr :=
  sumE ((List.range SEAT_COUNT).flatMap fun seat =>
    (List.range ROLE_COUNT).map fun role =>
      mul (v (SELECT seat role)) (v (SCORE seat role)))

def candidateRole (candidate seat : Nat) : Nat :=
  (candidateRows.getD candidate []).getD seat 0

def candidateScoreExpr (candidate : Nat) : EmittedExpr :=
  sumE ((List.range SEAT_COUNT).map fun seat =>
    v (SCORE seat (candidateRole candidate seat)))

def candidateChosenExpr (candidate : Nat) : EmittedExpr :=
  prodE ((List.range SEAT_COUNT).map fun seat =>
    v (SELECT seat (candidateRole candidate seat)))

def candidateAllowedExpr (candidate : Nat) : EmittedExpr :=
  prodE ((List.range SEAT_COUNT).map fun seat =>
    v (ADMISSIBLE seat (candidateRole candidate seat)))

def earlierChosenExpr (candidate : Nat) : EmittedExpr :=
  sumE (((List.range CANDIDATE_COUNT).drop (candidate + 1)).map fun later =>
    v (CANDIDATE_CHOSEN later))

def diffZeroExpr (candidate : Nat) : EmittedExpr :=
  prodE ((List.range DIFF_BITS).map fun bit =>
    sub (c 1) (v (DIFF_BIT candidate bit)))

def candidateChosenBodies : List EmittedExpr :=
  (List.range CANDIDATE_COUNT).map fun candidate =>
    sub (v (CANDIDATE_CHOSEN candidate)) (candidateChosenExpr candidate)

def candidateAllowedBodies : List EmittedExpr :=
  (List.range CANDIDATE_COUNT).map fun candidate =>
    sub (v (CANDIDATE_ALLOWED candidate)) (candidateAllowedExpr candidate)

def diffBitBodies : List EmittedExpr :=
  (List.range CANDIDATE_COUNT).flatMap fun candidate =>
    (List.range DIFF_BITS).map fun bit => binaryBody (DIFF_BIT candidate bit)

def diffRecomposeBodies : List EmittedExpr :=
  (List.range CANDIDATE_COUNT).map fun candidate =>
    recompose (DIFF candidate) (DIFF_BIT candidate) DIFF_BITS

def diffNonzeroBodies : List EmittedExpr :=
  (List.range CANDIDATE_COUNT).map fun candidate =>
    sub (v (DIFF_NONZERO candidate)) (sub (c 1) (diffZeroExpr candidate))

/-- If a candidate is feasible, its score difference from the chosen total is
the canonical nonnegative four-bit `DIFF`. -/
def candidateDominanceBodies : List EmittedExpr :=
  (List.range CANDIDATE_COUNT).map fun candidate =>
    mul (v (CANDIDATE_ALLOWED candidate))
      (sub (sub (v TOTAL) (candidateScoreExpr candidate)) (v (DIFF candidate)))

/-- A feasible lexicographically earlier candidate may not tie the chosen
assignment: its certified difference must be nonzero. -/
def lexTieBodies : List EmittedExpr :=
  (List.range CANDIDATE_COUNT).map fun candidate =>
    mul (mul (v (CANDIDATE_ALLOWED candidate)) (earlierChosenExpr candidate))
      (sub (c 1) (v (DIFF_NONZERO candidate)))

def semanticBodies : List EmittedExpr :=
  [sub (v RULE) (c RULE_ID)] ++
  scoreBitBodies ++ scoreRecomposeBodies ++ admissibleBitBodies ++
  selectBitBodies ++ selectRowBodies ++ selectColumnBodies ++
  assignedRecomposeBodies ++ chosenAdmissibleBodies ++
  (List.range DIFF_BITS).map (fun bit => binaryBody (TOTAL_BIT bit)) ++
  [recompose TOTAL TOTAL_BIT DIFF_BITS, sub (v TOTAL) selectedTotalExpr] ++
  candidateChosenBodies ++ candidateAllowedBodies ++
  diffBitBodies ++ diffRecomposeBodies ++ diffNonzeroBodies ++
  candidateDominanceBodies ++ lexTieBodies

def publicPins : List VmConstraint2 :=
  [ .base (.piBinding .first SESSION 0)
  , .base (.piBinding .first RULE 1) ] ++
  (List.range DIGEST_WIDTH).map
    (fun lane => .base (.piBinding .first (ROOT lane) (2 + lane))) ++
  (List.range SEAT_COUNT).map
    (fun seat => .base (.piBinding .first (ASSIGNED seat) (10 + seat)))

def privateRaidAssignmentN4Descriptor : EffectVmDescriptor2 :=
  { name := "private-raid-assignment-n4::admissible-max-lex-v1"
  , traceWidth := TRACE_WIDTH
  , piCount := 14
  , tables := []
  , constraints := [rootLookup] ++
      semanticBodies.map (fun body => .base (.gate body)) ++ publicPins ++
      semanticBodies.map (fun body => .base (.boundary .last body))
  , hashSites := []
  , ranges := [] }

#guard rootInputExprs.length == 16
#guard rootDigestCols.length == 8
#guard scoreBitBodies.length == 32
#guard admissibleBitBodies.length == 16
#guard candidateDominanceBodies.length == 24
#guard lexTieBodies.length == 24
#guard privateRaidAssignmentN4Descriptor.traceWidth == 299
#guard privateRaidAssignmentN4Descriptor.piCount == 14
#guard privateRaidAssignmentN4Descriptor.constraints.length ==
  1 + 2 * semanticBodies.length + 14

/-! ## 4. Emitted-AIR extraction boundary. -/

def raidM0 : Int → Int := fun _ => 0
def raidF0 : Int → Int × Nat := fun _ => (0, 0)

def constTrace (a pis : Assignment) (tf : TraceFamily) : VmTrace where
  rows := List.replicate 4 a
  pub := pis
  tf := tf

@[simp] theorem constTrace_rows_length (a pis : Assignment) (tf : TraceFamily) :
    (constTrace a pis tf).rows.length = 4 := by simp [constTrace]

@[simp] theorem constTrace_loc0 (a pis : Assignment) (tf : TraceFamily) :
    (envAt (constTrace a pis tf) 0).loc = a := by
  funext col
  simp [envAt, constTrace]

@[simp] theorem constTrace_pub0 (a pis : Assignment) (tf : TraceFamily) :
    (envAt (constTrace a pis tf) 0).pub = pis := rfl

@[simp] theorem constTrace_tf (a pis : Assignment) (tf : TraceFamily) :
    (constTrace a pis tf).tf = tf := rfl

def CanonicalAssignment (a : Assignment) : Prop :=
  ∀ col, 0 ≤ a col ∧ a col < BABYBEAR_MODULUS

theorem semantic_gate_mem {body : EmittedExpr} (hbody : body ∈ semanticBodies) :
    VmConstraint2.base (.gate body) ∈ privateRaidAssignmentN4Descriptor.constraints := by
  simp [privateRaidAssignmentN4Descriptor, hbody]

theorem public_pin_mem {pin : VmConstraint2} (hpin : pin ∈ publicPins) :
    pin ∈ privateRaidAssignmentN4Descriptor.constraints := by
  simp [privateRaidAssignmentN4Descriptor, hpin]

theorem root_lookup_mem : rootLookup ∈ privateRaidAssignmentN4Descriptor.constraints := by
  simp [privateRaidAssignmentN4Descriptor]

theorem semantic_gate_vanishes {hash : List Int → Int}
    {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf))
    {body : EmittedExpr} (hbody : body ∈ semanticBodies) :
    body.eval a ≡ 0 [ZMOD BABYBEAR_MODULUS] := by
  have h := hsat.rowConstraints 0 (by simp) _ (semantic_gate_mem hbody)
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, BABYBEAR_MODULUS] using h

theorem public_pin_sound {hash : List Int → Int}
    {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf))
    {col pi : Nat}
    (hpin : VmConstraint2.base (.piBinding .first col pi) ∈ publicPins) :
    a col ≡ pis pi [ZMOD BABYBEAR_MODULUS] := by
  have h := hsat.rowConstraints 0 (by simp) _ (public_pin_mem hpin)
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, BABYBEAR_MODULUS] using h

theorem wide_root_lookup_sound {hash : List Int → Int}
    {a pis : Assignment} {tf : TraceFamily}
    (permOut : List Int → List Int)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf)) :
    rootDigestCols.map a = permOut (rootInputExprs.map (·.eval a)) := by
  have hrow := hsat.rowConstraints 0 (by simp) rootLookup root_lookup_mem
  have hlookup :
      (chipLookupTupleN rootInputExprs rootDigestCols).map (·.eval a) ∈
        tf TableId.poseidon2 := by
    simpa [rootLookup, VmConstraint2.holdsAt,
      Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt] using hrow
  exact chip_lookup_sound_N permOut (tf TableId.poseidon2) hChip a
    rootInputExprs rootDigestCols (by decide) hlookup

structure EmittedAirFacts (permOut : List Int → List Int)
    (a pis : Assignment) (tf : TraceFamily) : Prop where
  semanticGates : ∀ body ∈ semanticBodies,
    body.eval a ≡ 0 [ZMOD BABYBEAR_MODULUS]
  wideRoot : rootDigestCols.map a = permOut (rootInputExprs.map (·.eval a))
  publicPins : ∀ col pi,
    VmConstraint2.base (.piBinding .first col pi) ∈ publicPins →
    a col ≡ pis pi [ZMOD BABYBEAR_MODULUS]

theorem privateRaidAssignmentN4_emitted_air_sound
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (permOut : List Int → List Int)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf)) :
    EmittedAirFacts permOut a pis tf :=
  ⟨fun _ hbody => semantic_gate_vanishes hsat hbody,
   wide_root_lookup_sound permOut hChip hsat,
   fun _ _ hpin => public_pin_sound hsat hpin⟩

/-! ## 5. Complete finite modular-to-integer decode. -/

open Dregg2.Circuit.Emit.EffectVmEmitTransfer (pPrimeInt)

theorem eq_of_modEq_of_canonical {x y : Int}
    (hmod : x ≡ y [ZMOD BABYBEAR_MODULUS])
    (hx : 0 ≤ x ∧ x < BABYBEAR_MODULUS)
    (hy : 0 ≤ y ∧ y < BABYBEAR_MODULUS) : x = y := by
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hmod
  simp only [BABYBEAR_MODULUS] at hk hx hy
  omega

theorem binary_of_modular_gate {a : Assignment} {col : Nat}
    (hcanon : CanonicalAssignment a)
    (hmod : (binaryBody col).eval a ≡ 0 [ZMOD BABYBEAR_MODULUS]) :
    a col = 0 ∨ a col = 1 := by
  have hev : (binaryBody col).eval a = a col * (a col - 1) := by
    simp only [binaryBody, sub, neg, mul, add, v, c, EmittedExpr.eval]
    ring
  rw [hev] at hmod
  have hd : (2013265921 : Int) ∣ a col * (a col - 1) := by
    simpa [BABYBEAR_MODULUS] using Int.modEq_zero_iff_dvd.mp hmod
  rcases pPrimeInt.dvd_mul.mp hd with hx | hx
  · obtain ⟨k, hk⟩ := hx
    have hc := hcanon col
    simp only [BABYBEAR_MODULUS] at hc
    left
    omega
  · obtain ⟨k, hk⟩ := hx
    have hc := hcanon col
    simp only [BABYBEAR_MODULUS] at hc
    right
    omega

theorem score_bit_body_mem (seat role : Fin 4) (bit : Fin 2) :
    binaryBody (SCORE_BIT seat.val role.val bit.val) ∈ semanticBodies := by
  fin_cases seat <;> fin_cases role <;> fin_cases bit <;> decide

theorem admissible_bit_body_mem (seat role : Fin 4) :
    binaryBody (ADMISSIBLE seat.val role.val) ∈ semanticBodies := by
  fin_cases seat <;> fin_cases role <;> decide

theorem select_bit_body_mem (seat role : Fin 4) :
    binaryBody (SELECT seat.val role.val) ∈ semanticBodies := by
  fin_cases seat <;> fin_cases role <;> decide

theorem total_bit_body_mem (bit : Fin 4) :
    binaryBody (TOTAL_BIT bit.val) ∈ semanticBodies := by
  fin_cases bit <;> decide

theorem diff_bit_body_mem (candidate : Fin 24) (bit : Fin 4) :
    binaryBody (DIFF_BIT candidate.val bit.val) ∈ semanticBodies := by
  fin_cases candidate <;> fin_cases bit <;> decide

structure DecodedPrivateBits (a : Assignment) : Prop where
  score : ∀ seat role : Fin 4, ∀ bit : Fin 2,
    a (SCORE_BIT seat.val role.val bit.val) = 0 ∨
      a (SCORE_BIT seat.val role.val bit.val) = 1
  admissible : ∀ seat role : Fin 4,
    a (ADMISSIBLE seat.val role.val) = 0 ∨
      a (ADMISSIBLE seat.val role.val) = 1
  select : ∀ seat role : Fin 4,
    a (SELECT seat.val role.val) = 0 ∨ a (SELECT seat.val role.val) = 1
  total : ∀ bit : Fin 4,
    a (TOTAL_BIT bit.val) = 0 ∨ a (TOTAL_BIT bit.val) = 1
  diff : ∀ candidate : Fin 24, ∀ bit : Fin 4,
    a (DIFF_BIT candidate.val bit.val) = 0 ∨
      a (DIFF_BIT candidate.val bit.val) = 1

theorem privateRaidAssignmentN4_private_bits_decoded
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf)) :
    DecodedPrivateBits a := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro seat role bit
    exact binary_of_modular_gate hcanon
      (semantic_gate_vanishes hsat (score_bit_body_mem seat role bit))
  · intro seat role
    exact binary_of_modular_gate hcanon
      (semantic_gate_vanishes hsat (admissible_bit_body_mem seat role))
  · intro seat role
    exact binary_of_modular_gate hcanon
      (semantic_gate_vanishes hsat (select_bit_body_mem seat role))
  · intro bit
    exact binary_of_modular_gate hcanon
      (semantic_gate_vanishes hsat (total_bit_body_mem bit))
  · intro candidate bit
    exact binary_of_modular_gate hcanon
      (semantic_gate_vanishes hsat (diff_bit_body_mem candidate bit))

theorem score_recompose_body_mem (seat role : Fin 4) :
    recompose (SCORE seat.val role.val) (SCORE_BIT seat.val role.val) SCORE_BITS ∈
      semanticBodies := by
  fin_cases seat <;> fin_cases role <;> decide

theorem diff_recompose_body_mem (candidate : Fin 24) :
    recompose (DIFF candidate.val) (DIFF_BIT candidate.val) DIFF_BITS ∈
      semanticBodies := by
  fin_cases candidate <;> decide

theorem total_recompose_body_mem : recompose TOTAL TOTAL_BIT DIFF_BITS ∈ semanticBodies := by
  decide

theorem score_recompose_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf))
    (seat role : Fin 4) :
    a (SCORE seat.val role.val) =
      a (SCORE_BIT seat.val role.val 0) +
        2 * a (SCORE_BIT seat.val role.val 1) := by
  have hbits := privateRaidAssignmentN4_private_bits_decoded hcanon hsat
  have hb0 := hbits.score seat role 0
  have hb1 := hbits.score seat role 1
  have hgate := semantic_gate_vanishes hsat (score_recompose_body_mem seat role)
  have hres :
      (a (SCORE_BIT seat.val role.val 0) +
          2 * a (SCORE_BIT seat.val role.val 1)) -
        a (SCORE seat.val role.val) ≡ 0 [ZMOD BABYBEAR_MODULUS] := by
    norm_num [recompose, sumE, weighted, sub, neg, mul, add, v, c, SCORE_BITS,
      EmittedExpr.eval, List.range_succ, Function.comp_apply] at hgate
    simpa [sub_eq_add_neg] using hgate
  have hcong :
      a (SCORE_BIT seat.val role.val 0) +
          2 * a (SCORE_BIT seat.val role.val 1) ≡
        a (SCORE seat.val role.val) [ZMOD BABYBEAR_MODULUS] := by
    simpa using hres.add_right (a (SCORE seat.val role.val))
  have hsmall :
      0 ≤ a (SCORE_BIT seat.val role.val 0) +
          2 * a (SCORE_BIT seat.val role.val 1) ∧
      a (SCORE_BIT seat.val role.val 0) +
          2 * a (SCORE_BIT seat.val role.val 1) < BABYBEAR_MODULUS := by
    rcases hb0 with hb0 | hb0 <;> rcases hb1 with hb1 | hb1 <;>
      simp_all [BABYBEAR_MODULUS]
  exact (eq_of_modEq_of_canonical hcong hsmall
    (hcanon (SCORE seat.val role.val))).symm

theorem score_column_bounds
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf))
    (seat role : Fin 4) :
    0 ≤ a (SCORE seat.val role.val) ∧ a (SCORE seat.val role.val) < 4 := by
  rw [score_recompose_exact hcanon hsat seat role]
  have hbits := privateRaidAssignmentN4_private_bits_decoded hcanon hsat
  have hb0 := hbits.score seat role 0
  have hb1 := hbits.score seat role 1
  rcases hb0 with hb0 | hb0 <;> rcases hb1 with hb1 | hb1 <;> simp_all

theorem four_bit_recompose_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf))
    (col : Nat) (bit : Nat → Nat)
    (hbody : recompose col bit DIFF_BITS ∈ semanticBodies)
    (hbits : ∀ b : Fin 4, a (bit b.val) = 0 ∨ a (bit b.val) = 1) :
    a col = a (bit 0) + 2 * a (bit 1) + 4 * a (bit 2) + 8 * a (bit 3) := by
  have hb0 := hbits 0; have hb1 := hbits 1
  have hb2 := hbits 2; have hb3 := hbits 3
  have hgate := semantic_gate_vanishes hsat hbody
  have hres :
      (a (bit 0) + 2 * a (bit 1) + 4 * a (bit 2) + 8 * a (bit 3)) - a col ≡
        0 [ZMOD BABYBEAR_MODULUS] := by
    norm_num [recompose, sumE, weighted, sub, neg, mul, add, v, c, DIFF_BITS,
      EmittedExpr.eval, List.range_succ, Function.comp_apply] at hgate
    simpa [sub_eq_add_neg, add_assoc] using hgate
  have hcong :
      a (bit 0) + 2 * a (bit 1) + 4 * a (bit 2) + 8 * a (bit 3) ≡
        a col [ZMOD BABYBEAR_MODULUS] := by
    simpa using hres.add_right (a col)
  have hsmall :
      0 ≤ a (bit 0) + 2 * a (bit 1) + 4 * a (bit 2) + 8 * a (bit 3) ∧
      a (bit 0) + 2 * a (bit 1) + 4 * a (bit 2) + 8 * a (bit 3) <
        BABYBEAR_MODULUS := by
    rcases hb0 with hb0 | hb0 <;> rcases hb1 with hb1 | hb1 <;>
      rcases hb2 with hb2 | hb2 <;> rcases hb3 with hb3 | hb3 <;>
      simp_all [BABYBEAR_MODULUS]
  exact (eq_of_modEq_of_canonical hcong hsmall (hcanon col)).symm

theorem total_recompose_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf)) :
    a TOTAL = a (TOTAL_BIT 0) + 2 * a (TOTAL_BIT 1) +
      4 * a (TOTAL_BIT 2) + 8 * a (TOTAL_BIT 3) := by
  apply four_bit_recompose_exact hcanon hsat TOTAL TOTAL_BIT total_recompose_body_mem
  exact (privateRaidAssignmentN4_private_bits_decoded hcanon hsat).total

theorem diff_recompose_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf))
    (candidate : Fin 24) :
    a (DIFF candidate.val) =
      a (DIFF_BIT candidate.val 0) + 2 * a (DIFF_BIT candidate.val 1) +
      4 * a (DIFF_BIT candidate.val 2) + 8 * a (DIFF_BIT candidate.val 3) := by
  apply four_bit_recompose_exact hcanon hsat
    (DIFF candidate.val) (DIFF_BIT candidate.val) (diff_recompose_body_mem candidate)
  exact (privateRaidAssignmentN4_private_bits_decoded hcanon hsat).diff candidate

theorem total_column_bounds
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf)) : 0 ≤ a TOTAL ∧ a TOTAL ≤ 15 := by
  rw [total_recompose_exact hcanon hsat]
  have hbits := privateRaidAssignmentN4_private_bits_decoded hcanon hsat
  have h0 := hbits.total 0; have h1 := hbits.total 1
  have h2 := hbits.total 2; have h3 := hbits.total 3
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;> simp_all

theorem diff_column_bounds
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf))
    (candidate : Fin 24) : 0 ≤ a (DIFF candidate.val) ∧ a (DIFF candidate.val) ≤ 15 := by
  rw [diff_recompose_exact hcanon hsat candidate]
  have hbits := privateRaidAssignmentN4_private_bits_decoded hcanon hsat
  have h0 := hbits.diff candidate 0; have h1 := hbits.diff candidate 1
  have h2 := hbits.diff candidate 2; have h3 := hbits.diff candidate 3
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;> simp_all

theorem select_row_body_mem (seat : Fin 4) :
    sub (sumE ((List.range ROLE_COUNT).map fun role => v (SELECT seat.val role))) (c 1) ∈
      semanticBodies := by
  fin_cases seat <;> decide

theorem select_column_body_mem (role : Fin 4) :
    sub (sumE ((List.range SEAT_COUNT).map fun seat => v (SELECT seat role.val))) (c 1) ∈
      semanticBodies := by
  fin_cases role <;> decide

theorem assigned_recompose_body_mem (seat : Fin 4) :
    sub (v (ASSIGNED seat.val))
      (sumE ((List.range ROLE_COUNT).map fun (role : Nat) =>
        weighted role (v (SELECT seat.val role)))) ∈ semanticBodies := by
  fin_cases seat <;> decide

theorem select_row_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf))
    (seat : Fin 4) :
    a (SELECT seat.val 0) + a (SELECT seat.val 1) +
      a (SELECT seat.val 2) + a (SELECT seat.val 3) = 1 := by
  have bits := privateRaidAssignmentN4_private_bits_decoded hcanon hsat
  have h0 := bits.select seat 0; have h1 := bits.select seat 1
  have h2 := bits.select seat 2; have h3 := bits.select seat 3
  have hgate := semantic_gate_vanishes hsat (select_row_body_mem seat)
  have hres :
      (a (SELECT seat.val 0) + a (SELECT seat.val 1) +
        a (SELECT seat.val 2) + a (SELECT seat.val 3)) - 1 ≡
        0 [ZMOD BABYBEAR_MODULUS] := by
    norm_num [ROLE_COUNT, sumE, sub, neg, mul, add, v, c, EmittedExpr.eval,
      List.range_succ, Function.comp_apply, add_assoc] at hgate
    simpa [sub_eq_add_neg, add_assoc] using hgate
  have hcong :
      a (SELECT seat.val 0) + a (SELECT seat.val 1) +
        a (SELECT seat.val 2) + a (SELECT seat.val 3) ≡ 1
        [ZMOD BABYBEAR_MODULUS] := by
    simpa using hres.add_right 1
  apply eq_of_modEq_of_canonical hcong
  · rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
      rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
      simp_all [BABYBEAR_MODULUS]
  · norm_num [BABYBEAR_MODULUS]

theorem select_column_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf))
    (role : Fin 4) :
    a (SELECT 0 role.val) + a (SELECT 1 role.val) +
      a (SELECT 2 role.val) + a (SELECT 3 role.val) = 1 := by
  have bits := privateRaidAssignmentN4_private_bits_decoded hcanon hsat
  have h0 := bits.select 0 role; have h1 := bits.select 1 role
  have h2 := bits.select 2 role; have h3 := bits.select 3 role
  have hgate := semantic_gate_vanishes hsat (select_column_body_mem role)
  have hres :
      (a (SELECT 0 role.val) + a (SELECT 1 role.val) +
        a (SELECT 2 role.val) + a (SELECT 3 role.val)) - 1 ≡
        0 [ZMOD BABYBEAR_MODULUS] := by
    norm_num [SEAT_COUNT, sumE, sub, neg, mul, add, v, c, EmittedExpr.eval,
      List.range_succ, Function.comp_apply, add_assoc] at hgate
    simpa [sub_eq_add_neg, add_assoc] using hgate
  have hcong :
      a (SELECT 0 role.val) + a (SELECT 1 role.val) +
        a (SELECT 2 role.val) + a (SELECT 3 role.val) ≡ 1
        [ZMOD BABYBEAR_MODULUS] := by
    simpa using hres.add_right 1
  apply eq_of_modEq_of_canonical hcong
  · rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
      rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
      simp_all [BABYBEAR_MODULUS]
  · norm_num [BABYBEAR_MODULUS]

theorem assigned_column_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf))
    (seat : Fin 4) :
    a (ASSIGNED seat.val) =
      a (SELECT seat.val 1) + 2 * a (SELECT seat.val 2) +
        3 * a (SELECT seat.val 3) := by
  have bits := privateRaidAssignmentN4_private_bits_decoded hcanon hsat
  have h0 := bits.select seat 0; have h1 := bits.select seat 1
  have h2 := bits.select seat 2; have h3 := bits.select seat 3
  have hsum := select_row_exact hcanon hsat seat
  have hgate := semantic_gate_vanishes hsat (assigned_recompose_body_mem seat)
  have hres :
      a (ASSIGNED seat.val) -
        (a (SELECT seat.val 1) + 2 * a (SELECT seat.val 2) +
          3 * a (SELECT seat.val 3)) ≡ 0 [ZMOD BABYBEAR_MODULUS] := by
    norm_num [ROLE_COUNT, sumE, weighted, sub, neg, mul, add, v, c,
      EmittedExpr.eval, List.range_succ, Function.comp_apply, add_assoc] at hgate
    simpa [sub_eq_add_neg, add_assoc] using hgate
  have hcong :
      a (ASSIGNED seat.val) ≡
        a (SELECT seat.val 1) + 2 * a (SELECT seat.val 2) +
          3 * a (SELECT seat.val 3) [ZMOD BABYBEAR_MODULUS] := by
    simpa using hres.add_right
      (a (SELECT seat.val 1) + 2 * a (SELECT seat.val 2) +
        3 * a (SELECT seat.val 3))
  apply eq_of_modEq_of_canonical hcong (hcanon (ASSIGNED seat.val))
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
    simp_all [BABYBEAR_MODULUS]

theorem assigned_column_bounds
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf))
    (seat : Fin 4) : 0 ≤ a (ASSIGNED seat.val) ∧ a (ASSIGNED seat.val) < 4 := by
  rw [assigned_column_exact hcanon hsat seat]
  have bits := privateRaidAssignmentN4_private_bits_decoded hcanon hsat
  have h0 := bits.select seat 0; have h1 := bits.select seat 1
  have h2 := bits.select seat 2; have h3 := bits.select seat 3
  have hsum := select_row_exact hcanon hsat seat
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;> simp_all

def decodedRoles (a : Assignment) (seat : Fin 4) : Fin 4 :=
  ⟨(a (ASSIGNED seat.val)).toNat % 4, Nat.mod_lt _ (by decide)⟩

theorem decoded_role_coe
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf))
    (seat : Fin 4) : ((decodedRoles a seat).val : Int) = a (ASSIGNED seat.val) := by
  simp only [decodedRoles]
  rw [Nat.mod_eq_of_lt]
  · exact Int.toNat_of_nonneg (assigned_column_bounds hcanon hsat seat).1
  · exact (Int.toNat_lt (assigned_column_bounds hcanon hsat seat).1).2
      (assigned_column_bounds hcanon hsat seat).2

theorem selected_selector_one
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf))
    (seat role : Fin 4)
    (hrole : a (ASSIGNED seat.val) = role.val) :
    a (SELECT seat.val role.val) = 1 := by
  have bits := privateRaidAssignmentN4_private_bits_decoded hcanon hsat
  have h0 := bits.select seat 0; have h1 := bits.select seat 1
  have h2 := bits.select seat 2; have h3 := bits.select seat 3
  have hsum := select_row_exact hcanon hsat seat
  have hassigned := assigned_column_exact hcanon hsat seat
  fin_cases role <;>
    norm_num at h0 h1 h2 h3 hsum hassigned hrole ⊢ <;>
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
      rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;> omega

theorem decoded_roles_exact_assignment
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf)) :
    ExactAssignment (decodedRoles a) := by
  apply Finite.injective_iff_bijective.mp
  intro left right heq
  have hl := selected_selector_one hcanon hsat left (decodedRoles a left)
    (decoded_role_coe hcanon hsat left).symm
  have hr0 := selected_selector_one hcanon hsat right (decodedRoles a right)
    (decoded_role_coe hcanon hsat right).symm
  have hr : a (SELECT right.val (decodedRoles a left).val) = 1 := by
    simpa [heq] using hr0
  have hsum := select_column_exact hcanon hsat (decodedRoles a left)
  have hn0 := (hcanon (SELECT 0 (decodedRoles a left).val)).1
  have hn1 := (hcanon (SELECT 1 (decodedRoles a left).val)).1
  have hn2 := (hcanon (SELECT 2 (decodedRoles a left).val)).1
  have hn3 := (hcanon (SELECT 3 (decodedRoles a left).val)).1
  fin_cases left <;> fin_cases right <;> simp_all <;> omega

def decodedScore (a : Assignment) (seat role : Fin 4) : Fin 4 :=
  ⟨(a (SCORE seat.val role.val)).toNat % 4, Nat.mod_lt _ (by decide)⟩

def decodedAdmissible (a : Assignment) (seat role : Fin 4) : Fin 2 :=
  ⟨(a (ADMISSIBLE seat.val role.val)).toNat % 2, Nat.mod_lt _ (by decide)⟩

def decodedWitness (a : Assignment) : PrivateWitness where
  inputs := fun seat =>
    { scores := decodedScore a seat
    , admissible := decodedAdmissible a seat }
  blinding := fun lane => a (BLIND lane.val)

theorem decoded_score_coe
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf))
    (seat role : Fin 4) :
    (((decodedWitness a).inputs seat).scores role).val =
      (a (SCORE seat.val role.val)).toNat := by
  simp only [decodedWitness, decodedScore]
  apply Nat.mod_eq_of_lt
  exact (Int.toNat_lt (score_column_bounds hcanon hsat seat role).1).2
    (score_column_bounds hcanon hsat seat role).2

theorem decoded_score_int
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf))
    (seat role : Fin 4) :
    ((((decodedWitness a).inputs seat).scores role).val : Int) =
      a (SCORE seat.val role.val) := by
  rw [decoded_score_coe hcanon hsat]
  exact Int.toNat_of_nonneg (score_column_bounds hcanon hsat seat role).1

theorem decoded_admissible_int
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf))
    (seat role : Fin 4) :
    ((((decodedWitness a).inputs seat).admissible role).val : Int) =
      a (ADMISSIBLE seat.val role.val) := by
  have hbit :=
    (privateRaidAssignmentN4_private_bits_decoded hcanon hsat).admissible seat role
  simp only [decodedWitness, decodedAdmissible]
  rcases hbit with hbit | hbit <;> simp [hbit]

theorem chosen_admissible_body_mem (seat : Fin 4) :
    sumE ((List.range ROLE_COUNT).map fun role =>
      mul (v (SELECT seat.val role))
        (sub (c 1) (v (ADMISSIBLE seat.val role)))) ∈ semanticBodies := by
  fin_cases seat <;> decide

theorem bit_complement_product_bounds {x y : Int}
    (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) :
    0 ≤ x * (1 - y) ∧ x * (1 - y) ≤ 1 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num

theorem eq_zero_of_modEq_of_small_nonneg {x : Int}
    (hmod : x ≡ 0 [ZMOD BABYBEAR_MODULUS])
    (hx : 0 ≤ x ∧ x < BABYBEAR_MODULUS) : x = 0 := by
  obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp hmod
  simp only [BABYBEAR_MODULUS] at hk hx
  omega

theorem chosen_admissible_sum_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf))
    (seat : Fin 4) :
    a (SELECT seat.val 0) * (1 - a (ADMISSIBLE seat.val 0)) +
      a (SELECT seat.val 1) * (1 - a (ADMISSIBLE seat.val 1)) +
      a (SELECT seat.val 2) * (1 - a (ADMISSIBLE seat.val 2)) +
      a (SELECT seat.val 3) * (1 - a (ADMISSIBLE seat.val 3)) = 0 := by
  have bits := privateRaidAssignmentN4_private_bits_decoded hcanon hsat
  have t0 := bit_complement_product_bounds (bits.select seat 0) (bits.admissible seat 0)
  have t1 := bit_complement_product_bounds (bits.select seat 1) (bits.admissible seat 1)
  have t2 := bit_complement_product_bounds (bits.select seat 2) (bits.admissible seat 2)
  have t3 := bit_complement_product_bounds (bits.select seat 3) (bits.admissible seat 3)
  norm_num at t0 t1 t2 t3
  have hgate := semantic_gate_vanishes hsat (chosen_admissible_body_mem seat)
  have hmod :
      a (SELECT seat.val 0) * (1 - a (ADMISSIBLE seat.val 0)) +
        a (SELECT seat.val 1) * (1 - a (ADMISSIBLE seat.val 1)) +
        a (SELECT seat.val 2) * (1 - a (ADMISSIBLE seat.val 2)) +
        a (SELECT seat.val 3) * (1 - a (ADMISSIBLE seat.val 3)) ≡
        0 [ZMOD BABYBEAR_MODULUS] := by
    norm_num [ROLE_COUNT, sumE, sub, neg, mul, add, v, c, EmittedExpr.eval,
      List.range_succ, Function.comp_apply, add_assoc] at hgate
    simpa [sub_eq_add_neg, add_assoc] using hgate
  apply eq_zero_of_modEq_of_small_nonneg hmod
  simp only [BABYBEAR_MODULUS]
  omega

theorem decoded_roles_admissible
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf)) :
    AdmissibleAssignment (decodedWitness a) (decodedRoles a) := by
  intro seat
  have bits := privateRaidAssignmentN4_private_bits_decoded hcanon hsat
  have hsum := chosen_admissible_sum_exact hcanon hsat seat
  have t0 := bit_complement_product_bounds (bits.select seat 0) (bits.admissible seat 0)
  have t1 := bit_complement_product_bounds (bits.select seat 1) (bits.admissible seat 1)
  have t2 := bit_complement_product_bounds (bits.select seat 2) (bits.admissible seat 2)
  have t3 := bit_complement_product_bounds (bits.select seat 3) (bits.admissible seat 3)
  norm_num at t0 t1 t2 t3
  have hsel := selected_selector_one hcanon hsat seat (decodedRoles a seat)
    (decoded_role_coe hcanon hsat seat).symm
  have hadm := bits.admissible seat (decodedRoles a seat)
  have hdecode := decoded_admissible_int hcanon hsat seat (decodedRoles a seat)
  generalize hr : decodedRoles a seat = role at hsel hadm hdecode ⊢
  fin_cases role <;>
    norm_num at hsel hadm hdecode ⊢ <;>
    rcases hadm with hadm | hadm <;> simp_all <;> omega

theorem selected_seat_value_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf))
    (seat : Fin 4) :
    a (SELECT seat.val 0) * a (SCORE seat.val 0) +
      a (SELECT seat.val 1) * a (SCORE seat.val 1) +
      a (SELECT seat.val 2) * a (SCORE seat.val 2) +
      a (SELECT seat.val 3) * a (SCORE seat.val 3) =
        a (SCORE seat.val (decodedRoles a seat).val) := by
  have bits := privateRaidAssignmentN4_private_bits_decoded hcanon hsat
  have h0 := bits.select seat 0; have h1 := bits.select seat 1
  have h2 := bits.select seat 2; have h3 := bits.select seat 3
  have hsum := select_row_exact hcanon hsat seat
  have hsel := selected_selector_one hcanon hsat seat (decodedRoles a seat)
    (decoded_role_coe hcanon hsat seat).symm
  generalize hr : decodedRoles a seat = role at hsel ⊢
  fin_cases role <;>
    norm_num at h0 h1 h2 h3 hsum hsel ⊢ <;>
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
      rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;> simp_all

theorem selected_total_expr_eval
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf)) :
    selectedTotalExpr.eval a =
      a (SCORE 0 (decodedRoles a 0).val) +
      a (SCORE 1 (decodedRoles a 1).val) +
      a (SCORE 2 (decodedRoles a 2).val) +
      a (SCORE 3 (decodedRoles a 3).val) := by
  have h0 := selected_seat_value_exact hcanon hsat (0 : Fin 4)
  have h1 := selected_seat_value_exact hcanon hsat (1 : Fin 4)
  have h2 := selected_seat_value_exact hcanon hsat (2 : Fin 4)
  have h3 := selected_seat_value_exact hcanon hsat (3 : Fin 4)
  norm_num [selectedTotalExpr, SEAT_COUNT, ROLE_COUNT, sumE, mul, add, v, c,
    EmittedExpr.eval, List.range_succ, Function.comp_apply, add_assoc] at h0 h1 h2 h3 ⊢
  omega

theorem selected_total_body_mem : sub (v TOTAL) selectedTotalExpr ∈ semanticBodies := by
  decide

theorem selected_total_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf)) :
    a TOTAL =
      a (SCORE 0 (decodedRoles a 0).val) +
      a (SCORE 1 (decodedRoles a 1).val) +
      a (SCORE 2 (decodedRoles a 2).val) +
      a (SCORE 3 (decodedRoles a 3).val) := by
  have hgate := semantic_gate_vanishes hsat selected_total_body_mem
  have heval := selected_total_expr_eval hcanon hsat
  have hres :
      a TOTAL - selectedTotalExpr.eval a ≡ 0 [ZMOD BABYBEAR_MODULUS] := by
    simpa [sub, neg, mul, add, v, c, EmittedExpr.eval, sub_eq_add_neg] using hgate
  have hcong : a TOTAL ≡ selectedTotalExpr.eval a [ZMOD BABYBEAR_MODULUS] := by
    simpa using hres.add_right (selectedTotalExpr.eval a)
  rw [heval] at hcong
  apply eq_of_modEq_of_canonical hcong (hcanon TOTAL)
  have s0 := score_column_bounds hcanon hsat (0 : Fin 4) (decodedRoles a 0)
  have s1 := score_column_bounds hcanon hsat (1 : Fin 4) (decodedRoles a 1)
  have s2 := score_column_bounds hcanon hsat (2 : Fin 4) (decodedRoles a 2)
  have s3 := score_column_bounds hcanon hsat (3 : Fin 4) (decodedRoles a 3)
  norm_num at s0 s1 s2 s3
  simp only [BABYBEAR_MODULUS]
  omega

theorem decoded_total_suitability
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf)) :
    totalSuitability (decodedWitness a) (decodedRoles a) = a TOTAL := by
  rw [selected_total_exact hcanon hsat]
  simp [totalSuitability, decoded_score_int hcanon hsat]
  ring

def candidateRoleFin (candidate : Fin 24) (seat : Fin 4) : Fin 4 :=
  ⟨candidateRole candidate.val seat.val, by
    fin_cases candidate <;> fin_cases seat <;> decide⟩

def rolesOfCandidate (candidate : Fin 24) : Fin 4 → Fin 4 :=
  candidateRoleFin candidate

theorem candidate_chosen_body_mem (candidate : Fin 24) :
    sub (v (CANDIDATE_CHOSEN candidate.val)) (candidateChosenExpr candidate.val) ∈
      semanticBodies := by
  fin_cases candidate <;> decide

theorem candidate_allowed_body_mem (candidate : Fin 24) :
    sub (v (CANDIDATE_ALLOWED candidate.val)) (candidateAllowedExpr candidate.val) ∈
      semanticBodies := by
  fin_cases candidate <;> decide

theorem diff_nonzero_body_mem (candidate : Fin 24) :
    sub (v (DIFF_NONZERO candidate.val))
      (sub (c 1) (diffZeroExpr candidate.val)) ∈ semanticBodies := by
  fin_cases candidate <;> decide

theorem candidate_chosen_expr_bit
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf))
    (candidate : Fin 24) :
    (candidateChosenExpr candidate.val).eval a = 0 ∨
      (candidateChosenExpr candidate.val).eval a = 1 := by
  have bits := privateRaidAssignmentN4_private_bits_decoded hcanon hsat
  have h0 := bits.select 0 (candidateRoleFin candidate 0)
  have h1 := bits.select 1 (candidateRoleFin candidate 1)
  have h2 := bits.select 2 (candidateRoleFin candidate 2)
  have h3 := bits.select 3 (candidateRoleFin candidate 3)
  fin_cases candidate <;>
    norm_num [candidateChosenExpr, candidateRoleFin, candidateRole, candidateRows,
      SEAT_COUNT, prodE, mul, v, c, EmittedExpr.eval, List.range_succ,
      Function.comp_apply] at h0 h1 h2 h3 ⊢ <;>
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
      rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;> simp_all

theorem candidate_allowed_expr_bit
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf))
    (candidate : Fin 24) :
    (candidateAllowedExpr candidate.val).eval a = 0 ∨
      (candidateAllowedExpr candidate.val).eval a = 1 := by
  have bits := privateRaidAssignmentN4_private_bits_decoded hcanon hsat
  have h0 := bits.admissible 0 (candidateRoleFin candidate 0)
  have h1 := bits.admissible 1 (candidateRoleFin candidate 1)
  have h2 := bits.admissible 2 (candidateRoleFin candidate 2)
  have h3 := bits.admissible 3 (candidateRoleFin candidate 3)
  fin_cases candidate <;>
    norm_num [candidateAllowedExpr, candidateRoleFin, candidateRole, candidateRows,
      SEAT_COUNT, prodE, mul, v, c, EmittedExpr.eval, List.range_succ,
      Function.comp_apply] at h0 h1 h2 h3 ⊢ <;>
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
      rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;> simp_all

theorem candidate_chosen_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf))
    (candidate : Fin 24) :
    a (CANDIDATE_CHOSEN candidate.val) = (candidateChosenExpr candidate.val).eval a := by
  have hgate := semantic_gate_vanishes hsat (candidate_chosen_body_mem candidate)
  have hres :
      a (CANDIDATE_CHOSEN candidate.val) - (candidateChosenExpr candidate.val).eval a ≡
        0 [ZMOD BABYBEAR_MODULUS] := by
    simpa [sub, neg, mul, add, v, c, EmittedExpr.eval, sub_eq_add_neg] using hgate
  have hcong :
      a (CANDIDATE_CHOSEN candidate.val) ≡ (candidateChosenExpr candidate.val).eval a
        [ZMOD BABYBEAR_MODULUS] := by
    simpa using hres.add_right ((candidateChosenExpr candidate.val).eval a)
  apply eq_of_modEq_of_canonical hcong (hcanon (CANDIDATE_CHOSEN candidate.val))
  rcases candidate_chosen_expr_bit hcanon hsat candidate with h | h <;>
    simp [h, BABYBEAR_MODULUS]

theorem candidate_allowed_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf))
    (candidate : Fin 24) :
    a (CANDIDATE_ALLOWED candidate.val) = (candidateAllowedExpr candidate.val).eval a := by
  have hgate := semantic_gate_vanishes hsat (candidate_allowed_body_mem candidate)
  have hres :
      a (CANDIDATE_ALLOWED candidate.val) - (candidateAllowedExpr candidate.val).eval a ≡
        0 [ZMOD BABYBEAR_MODULUS] := by
    simpa [sub, neg, mul, add, v, c, EmittedExpr.eval, sub_eq_add_neg] using hgate
  have hcong :
      a (CANDIDATE_ALLOWED candidate.val) ≡ (candidateAllowedExpr candidate.val).eval a
        [ZMOD BABYBEAR_MODULUS] := by
    simpa using hres.add_right ((candidateAllowedExpr candidate.val).eval a)
  apply eq_of_modEq_of_canonical hcong (hcanon (CANDIDATE_ALLOWED candidate.val))
  rcases candidate_allowed_expr_bit hcanon hsat candidate with h | h <;>
    simp [h, BABYBEAR_MODULUS]

theorem candidate_chosen_bit
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf)) (candidate : Fin 24) :
    a (CANDIDATE_CHOSEN candidate.val) = 0 ∨
      a (CANDIDATE_CHOSEN candidate.val) = 1 := by
  rw [candidate_chosen_exact hcanon hsat candidate]
  exact candidate_chosen_expr_bit hcanon hsat candidate

theorem candidate_allowed_bit
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf)) (candidate : Fin 24) :
    a (CANDIDATE_ALLOWED candidate.val) = 0 ∨
      a (CANDIDATE_ALLOWED candidate.val) = 1 := by
  rw [candidate_allowed_exact hcanon hsat candidate]
  exact candidate_allowed_expr_bit hcanon hsat candidate

theorem diff_zero_expr_bit
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf)) (candidate : Fin 24) :
    (diffZeroExpr candidate.val).eval a = 0 ∨
      (diffZeroExpr candidate.val).eval a = 1 := by
  have bits := privateRaidAssignmentN4_private_bits_decoded hcanon hsat
  have h0 := bits.diff candidate 0; have h1 := bits.diff candidate 1
  have h2 := bits.diff candidate 2; have h3 := bits.diff candidate 3
  norm_num [diffZeroExpr, DIFF_BITS, prodE, sub, neg, mul, add, v, c,
    EmittedExpr.eval, List.range_succ, Function.comp_apply] at h0 h1 h2 h3 ⊢
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;> simp_all

theorem diff_nonzero_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf)) (candidate : Fin 24) :
    a (DIFF_NONZERO candidate.val) = 1 - (diffZeroExpr candidate.val).eval a := by
  have hgate := semantic_gate_vanishes hsat (diff_nonzero_body_mem candidate)
  have hres :
      a (DIFF_NONZERO candidate.val) - (1 - (diffZeroExpr candidate.val).eval a) ≡
        0 [ZMOD BABYBEAR_MODULUS] := by
    simpa [sub, neg, mul, add, v, c, EmittedExpr.eval, sub_eq_add_neg] using hgate
  have hcong :
      a (DIFF_NONZERO candidate.val) ≡ 1 - (diffZeroExpr candidate.val).eval a
        [ZMOD BABYBEAR_MODULUS] := by
    simpa using hres.add_right (1 - (diffZeroExpr candidate.val).eval a)
  apply eq_of_modEq_of_canonical hcong (hcanon (DIFF_NONZERO candidate.val))
  rcases diff_zero_expr_bit hcanon hsat candidate with h | h <;>
    simp [h, BABYBEAR_MODULUS]

theorem diff_nonzero_zero_of_diff_zero
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash privateRaidAssignmentN4Descriptor raidM0 raidF0 []
      (constTrace a pis tf)) (candidate : Fin 24)
    (hdiff : a (DIFF candidate.val) = 0) :
    a (DIFF_NONZERO candidate.val) = 0 := by
  have hrecomp := diff_recompose_exact hcanon hsat candidate
  have bits := privateRaidAssignmentN4_private_bits_decoded hcanon hsat
  have h0 := bits.diff candidate 0; have h1 := bits.diff candidate 1
  have h2 := bits.diff candidate 2; have h3 := bits.diff candidate 3
  rw [diff_nonzero_exact hcanon hsat candidate]
  norm_num [diffZeroExpr, DIFF_BITS, prodE, sub, neg, mul, add, v, c,
    EmittedExpr.eval, List.range_succ, Function.comp_apply] at hrecomp ⊢
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;> simp_all

/-! ## 6. Mender enactment semantics.

This is a small Lean-authored semantic companion to the hosted Keep mechanic.
It does not claim refinement of the Rust implementation: no extraction or FFI
bridge connects this transition to that code.  `authenticatedActor` denotes the
identity already authenticated by the surrounding turn/application boundary.

An accepted assignment is carried as a bijection, hence publishes exactly one
Mender seat.  The grant binds that assignment to the authenticated proof
submitter and to the world-timeline cursor at which it was accepted.  Enactment
then permits exactly that seat and actor, never before the acceptance cursor,
at most once, and only when adding twenty hit points stays at or below fifty.
-/

/-- Public role number used by the Rust raid ABI for `Mender`. -/
def MENDER_ROLE_ID : Fin 4 := ⟨2, by omega⟩

theorem exactAssignment_unique_mender {roles : Fin 4 → Fin 4}
    (hexact : ExactAssignment roles) :
    ∃! seat, roles seat = MENDER_ROLE_ID := by
  obtain ⟨seat, hseat⟩ := hexact.2 MENDER_ROLE_ID
  refine ⟨seat, hseat, ?_⟩
  intro other hother
  exact hexact.1 (hother.trans hseat.symm)

/-- Application capability minted after accepting one private raid proof. -/
structure MenderGrant where
  roles : Fin 4 → Fin 4
  exactAssignment : ExactAssignment roles
  authenticatedCarrier : Nat
  acceptedAfter : Nat

theorem MenderGrant.unique_mender (grant : MenderGrant) :
    ∃! seat, grant.roles seat = MENDER_ROLE_ID :=
  exactAssignment_unique_mender grant.exactAssignment

/-- The public, authenticated inputs of one attempted Mender world action. -/
structure MenderCommand where
  seat : Fin 4
  authenticatedActor : Nat
  deriving DecidableEq, Repr

/-- Only the state touched by the Mender semantic transition. -/
structure MenderState where
  hp : Nat
  mendingUsed : Bool
  timelineCursor : Nat
  deriving DecidableEq, Repr

inductive MenderRefusal where
  | wrongSeat
  | wrongActor
  | staleGrant
  | alreadyUsed
  | wouldOverheal
  deriving DecidableEq, Repr

inductive MenderOutcome where
  | committed (state : MenderState)
  | refused (reason : MenderRefusal) (state : MenderState)
  deriving DecidableEq, Repr

def menderSuccessor (state : MenderState) : MenderState :=
  { hp := state.hp + 20
  , mendingUsed := true
  , timelineCursor := state.timelineCursor + 1 }

/-- Deterministic fail-closed Mender transition, in the same refusal order as
the logical boundary: assignment seat, actor, timeline, resource, HP ceiling. -/
def enactMender (grant : MenderGrant) (command : MenderCommand)
    (state : MenderState) : MenderOutcome :=
  if grant.roles command.seat ≠ MENDER_ROLE_ID then
    .refused .wrongSeat state
  else if command.authenticatedActor ≠ grant.authenticatedCarrier then
    .refused .wrongActor state
  else if grant.acceptedAfter > state.timelineCursor then
    .refused .staleGrant state
  else if state.mendingUsed then
    .refused .alreadyUsed state
  else if state.hp > 30 then
    .refused .wouldOverheal state
  else
    .committed (menderSuccessor state)

theorem enactMender_commits
    {grant : MenderGrant} {command : MenderCommand} {state : MenderState}
    (hseat : grant.roles command.seat = MENDER_ROLE_ID)
    (hactor : command.authenticatedActor = grant.authenticatedCarrier)
    (hcursor : grant.acceptedAfter ≤ state.timelineCursor)
    (hunused : state.mendingUsed = false)
    (hhp : state.hp ≤ 30) :
    enactMender grant command state = .committed (menderSuccessor state) := by
  have hnotStale : ¬grant.acceptedAfter > state.timelineCursor := by omega
  have hnotOverheal : ¬state.hp > 30 := by omega
  simp [enactMender, hseat, hactor, hnotStale, hunused, hnotOverheal]

/-- Functional correctness of every successful transition: exact recovery,
resource consumption, cursor advance, and the post-state HP ceiling. -/
theorem enactMender_functional_correctness
    {grant : MenderGrant} {command : MenderCommand}
    {before after : MenderState}
    (h : enactMender grant command before = .committed after) :
    grant.roles command.seat = MENDER_ROLE_ID ∧
    command.authenticatedActor = grant.authenticatedCarrier ∧
    grant.acceptedAfter ≤ before.timelineCursor ∧
    before.mendingUsed = false ∧
    before.hp ≤ 30 ∧
    after.hp = before.hp + 20 ∧
    after.hp ≤ 50 ∧
    after.mendingUsed = true ∧
    after.timelineCursor = before.timelineCursor + 1 := by
  simp only [enactMender] at h
  split at h <;> try contradiction
  next hseat =>
    split at h <;> try contradiction
    next hactor =>
      split at h <;> try contradiction
      next hcursor =>
        split at h <;> try contradiction
        next hused =>
          split at h <;> try contradiction
          next hhp =>
            simp only [MenderOutcome.committed.injEq] at h
            subst after
            simp only [menderSuccessor]
            simp_all

theorem enactMender_wrong_seat
    {grant : MenderGrant} {command : MenderCommand} {state : MenderState}
    (hseat : grant.roles command.seat ≠ MENDER_ROLE_ID) :
    enactMender grant command state = .refused .wrongSeat state := by
  simp [enactMender, hseat]

theorem enactMender_wrong_actor
    {grant : MenderGrant} {command : MenderCommand} {state : MenderState}
    (hseat : grant.roles command.seat = MENDER_ROLE_ID)
    (hactor : command.authenticatedActor ≠ grant.authenticatedCarrier) :
    enactMender grant command state = .refused .wrongActor state := by
  simp [enactMender, hseat, hactor]

theorem enactMender_stale
    {grant : MenderGrant} {command : MenderCommand} {state : MenderState}
    (hseat : grant.roles command.seat = MENDER_ROLE_ID)
    (hactor : command.authenticatedActor = grant.authenticatedCarrier)
    (hstale : state.timelineCursor < grant.acceptedAfter) :
    enactMender grant command state = .refused .staleGrant state := by
  simp [enactMender, hseat, hactor, hstale]

theorem enactMender_reuse
    {grant : MenderGrant} {command : MenderCommand} {state : MenderState}
    (hseat : grant.roles command.seat = MENDER_ROLE_ID)
    (hactor : command.authenticatedActor = grant.authenticatedCarrier)
    (hcursor : grant.acceptedAfter ≤ state.timelineCursor)
    (hused : state.mendingUsed = true) :
    enactMender grant command state = .refused .alreadyUsed state := by
  simp [enactMender, hseat, hactor, hcursor, hused]

theorem enactMender_overheal
    {grant : MenderGrant} {command : MenderCommand} {state : MenderState}
    (hseat : grant.roles command.seat = MENDER_ROLE_ID)
    (hactor : command.authenticatedActor = grant.authenticatedCarrier)
    (hcursor : grant.acceptedAfter ≤ state.timelineCursor)
    (hunused : state.mendingUsed = false)
    (hhp : 30 < state.hp) :
    enactMender grant command state = .refused .wouldOverheal state := by
  simp [enactMender, hseat, hactor, hcursor, hunused, hhp]

/-- Refusal is observationally state-holding, independently of its reason. -/
theorem enactMender_refusal_holds_state
    {grant : MenderGrant} {command : MenderCommand} {before after : MenderState}
    {reason : MenderRefusal}
    (h : enactMender grant command before = .refused reason after) :
    after = before := by
  unfold enactMender at h
  split at h
  · simp_all
  · split at h
    · simp_all
    · split at h
      · simp_all
      · split at h
        · simp_all
        · split at h <;> simp_all

/-- The first successful recovery consumes the resource, so the next otherwise
identical attempt is refused without changing its post-success state. -/
theorem enactMender_success_then_reuse
    {grant : MenderGrant} {command : MenderCommand} {state : MenderState}
    (hseat : grant.roles command.seat = MENDER_ROLE_ID)
    (hactor : command.authenticatedActor = grant.authenticatedCarrier)
    (hcursor : grant.acceptedAfter ≤ state.timelineCursor) :
    enactMender grant command (menderSuccessor state) =
      .refused .alreadyUsed (menderSuccessor state) := by
  apply enactMender_reuse hseat hactor
  · simp [menderSuccessor]
    omega
  · simp [menderSuccessor]

def exampleMenderGrant : MenderGrant where
  roles := id
  exactAssignment := Function.bijective_id
  authenticatedCarrier := 7
  acceptedAfter := 3

def exampleMenderCommand : MenderCommand where
  seat := 2
  authenticatedActor := 7

def exampleMenderState : MenderState where
  hp := 30
  mendingUsed := false
  timelineCursor := 3

#guard enactMender exampleMenderGrant exampleMenderCommand exampleMenderState ==
  .committed { hp := 50, mendingUsed := true, timelineCursor := 4 }

#guard enactMender exampleMenderGrant
    { seat := 1, authenticatedActor := 7 } exampleMenderState ==
  .refused .wrongSeat exampleMenderState

#guard enactMender exampleMenderGrant
    { seat := 2, authenticatedActor := 8 } exampleMenderState ==
  .refused .wrongActor exampleMenderState

#guard enactMender exampleMenderGrant exampleMenderCommand
    { hp := 30, mendingUsed := false, timelineCursor := 2 } ==
  .refused .staleGrant { hp := 30, mendingUsed := false, timelineCursor := 2 }

#guard enactMender exampleMenderGrant exampleMenderCommand
    { hp := 30, mendingUsed := true, timelineCursor := 3 } ==
  .refused .alreadyUsed { hp := 30, mendingUsed := true, timelineCursor := 3 }

#guard enactMender exampleMenderGrant exampleMenderCommand
    { hp := 31, mendingUsed := false, timelineCursor := 3 } ==
  .refused .wouldOverheal { hp := 31, mendingUsed := false, timelineCursor := 3 }

#assert_all_clean [
  Dregg2.Games.PrivateRaidAssignmentDescriptor.participantPack_injective,
  Dregg2.Games.PrivateRaidAssignmentDescriptor.packedInputs_injective,
  Dregg2.Games.PrivateRaidAssignmentDescriptor.lexCode_injective,
  Dregg2.Games.PrivateRaidAssignmentDescriptor.optimalLex_unique,
  Dregg2.Games.PrivateRaidAssignmentDescriptor.check_sound,
  Dregg2.Games.PrivateRaidAssignmentDescriptor.candidateRows_complete,
  Dregg2.Games.PrivateRaidAssignmentDescriptor.candidateRows_shape,
  Dregg2.Games.PrivateRaidAssignmentDescriptor.privateRaidAssignmentN4_emitted_air_sound,
  Dregg2.Games.PrivateRaidAssignmentDescriptor.privateRaidAssignmentN4_private_bits_decoded,
  Dregg2.Games.PrivateRaidAssignmentDescriptor.score_recompose_exact,
  Dregg2.Games.PrivateRaidAssignmentDescriptor.decoded_roles_exact_assignment,
  Dregg2.Games.PrivateRaidAssignmentDescriptor.decoded_roles_admissible,
  Dregg2.Games.PrivateRaidAssignmentDescriptor.selected_total_exact,
  Dregg2.Games.PrivateRaidAssignmentDescriptor.candidate_chosen_exact,
  Dregg2.Games.PrivateRaidAssignmentDescriptor.candidate_allowed_exact,
  Dregg2.Games.PrivateRaidAssignmentDescriptor.diff_nonzero_zero_of_diff_zero,
  Dregg2.Games.PrivateRaidAssignmentDescriptor.exactAssignment_unique_mender,
  Dregg2.Games.PrivateRaidAssignmentDescriptor.enactMender_functional_correctness,
  Dregg2.Games.PrivateRaidAssignmentDescriptor.enactMender_wrong_seat,
  Dregg2.Games.PrivateRaidAssignmentDescriptor.enactMender_wrong_actor,
  Dregg2.Games.PrivateRaidAssignmentDescriptor.enactMender_stale,
  Dregg2.Games.PrivateRaidAssignmentDescriptor.enactMender_reuse,
  Dregg2.Games.PrivateRaidAssignmentDescriptor.enactMender_overheal,
  Dregg2.Games.PrivateRaidAssignmentDescriptor.enactMender_refusal_holds_state,
  Dregg2.Games.PrivateRaidAssignmentDescriptor.enactMender_success_then_reuse]

end Dregg2.Games.PrivateRaidAssignmentDescriptor
