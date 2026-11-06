/-
# Dregg2.Circuit.Emit.MinaWrapVerifierAir — the in-AIR Kimchi/Wrap verifier's ROW, and the stage
census that prices it.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored AIR.** The row layout, every gate expression and the emitted descriptor are
authored here and go through the compiler (`EffectLower.lowerAir` of an `EffectAirIR.EffectAir`);
`mainRailOk = true` holds by `rfl`. There is no hand-written `VmConstraint2` anywhere in this file.
Rust PROVES the artifact and authors no constraint. House Law #1.

## WHAT THIS IS

`PastaFieldSound` and `PastaAddSubSound` each emit ONE Pasta operation as a standalone descriptor —
a multiply (253 constraints / 190 columns) and an add/sub (160 / 128). Six such descriptors are
checked in and, until this file, **every one of them was used only by its own soundness test**. A
verifier is not one operation; it is ~1.6 M of them in a fixed order. This file is the unit that
makes that sayable:

  * **§1–§3 the ALU ROW.** One row that can be a multiply OR an add OR a sub, selector-gated, in a
    layout that costs `794` committed columns against the standalone multiply's `694` — **1.14× for
    full operation generality**, because the add/sub operands reuse the multiply's own limb blocks
    and its range lookups. All three polarities reduce to the two existing forcing theorems with no
    re-derived bound: `felt_gates_force_congruence` and `addsub_gates_force_congruence` are both
    parametric in their base columns, which is exactly what makes the reuse legitimate rather than a
    second copy.
  * **§4 the CHAIN, and what it does NOT do.** `nxt.x = loc.z` under a selector — the only
    inter-row wiring `EffectAirIR`'s main rail can express. `chain_forces_limb_congruence` and
    `chain_forces_limb_equality` say what a chained transition buys;
    `unchained_transition_relates_nothing` says, as a theorem and not a caveat, what an unchained
    one does not; and `inter_row_wiring_is_transition_only` exhibits, on the IR's own decidable
    verdict, why there is no third option.
  * **§5 the STAGE CENSUS**, derived from the atom and verified against o1-labs source.
  * **§6 the OPENING'S VACUITY, as a theorem** (`opening_is_vacuous_when_sg_is_free`).

## ⚑ WHAT THIS IS NOT

It is **not** a Wrap verification and it is **not** machine-checked Pickles. What the emitted
descriptor establishes, exactly, is: *every row satisfying the gates performs the Pasta field
operation its selector names, and every CHAINED transition feeds one row's output to the next row's
first operand.* Whether the resulting straight-line program IS Kimchi's `verify` is a statement
about the TRACE GENERATOR, and this file proves nothing about that. §5's census is a PRICE, not a
proof of coverage.

## ⚑ THE THREE COUNTS VERIFIED AT SOURCE (this brief was carrying one that is wrong by 3.65×)

  * **The ξ-aggregate is 47 terms.** `~/dev/proof-systems/kimchi/src/verifier.rs:969-1075`, counted
    for a Wrap VK (no lookup index, no optional gate commitments): `2` recursion (`polys`, at
    `Max_proofs_verified = 2`) `+ 1` `public_comm` `+ 1` `ft_comm` `+ 1` `Column::Z` `+ 6` index
    commitments (Generic · Poseidon · CompleteAdd · VarBaseMul · EndoMul · EndoMulScalar) `+ 15`
    witness (`COLUMNS`) `+ 15` coefficient `+ 6` sigma (`PERMUTS − 1`) = **47**. Confirmed.
  * **The SRS is 2^15 = 32 768 bases and the IPA runs 15 rounds**, while the wrap DOMAIN is
    2^14 = 16 384 — two different powers, and reading either for the other is the error the brief
    warns about. The domain figure is independently pinned by `KimchiWrapMain`'s own measurement
    against the devnet wrap VK.
  * ⚑ **AND THE COLUMN COUNT IN THE PRICE WAS THE DECLARED ONE.** Measured 2026-08-04 on the
    deployed prover: `pasta-fpmul-sound` declares 190 columns and the prover commits to **694** —
    `MainLayout::build` appends a nibble-decomposition aux block per declared range lookup, so the
    committed width is `trace_width + Σ decomp_cols(bits)` and the inflation is **3.65×**. Every
    trace-size and LDE figure denominated in 190 is low by that factor. §5 prices in committed
    columns.

## Axiom hygiene

General theorems are `#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}). Facts
about concrete data are `native_decide`, pinned `#assert_compiled` (since 2026-11-06). No `sorry`/`admit`. Facts are NAMED THEOREMS — this file adds zero `#guard`s.
-/
import Dregg2.Circuit.Emit.PastaAddSubSound
import Dregg2.Circuit.Emit.EffectLowerCertified
import Dregg2.Circuit.GateExpr
-- ⚑ §7: the certified Schwartz–Zippel multiply body, relocated onto the ALU row's own layout.
import Dregg2.Circuit.Emit.PastaSzMul

namespace Dregg2.Circuit.Emit.MinaWrapVerifierAir

open Dregg2.Circuit (Assignment Expr Constraint ConstraintSystem)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 TableDef TableId mainTableDef VmConstraint2 WindowExpr)
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg LimbsLeg WindowLeg)
open Dregg2.Circuit.TableAirIR (RowSel)
open Dregg2.Circuit.Emit.EffectLower (lowerAir P)
open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaFieldSound
open Dregg2.Circuit.Emit.PastaAddSubSound

set_option autoImplicit false
-- The emitted spine is 127 gate legs + 32 window legs + 7 limb legs over 226 columns; the default
-- 512 does not reach the kernel reduction of the descriptor's constraint list.
set_option maxRecDepth 100000

/-! ## §1 — THE ROW LAYOUT.

⚑ The whole reason the ALU is cheap is that **the add/sub operands ARE the multiply's operands**.
`PastaAddSubSound` lays an add out at `AX_BASE = 0, AY_BASE = 32, AZ_BASE = 64`; `PastaFieldSound`
lays a multiply out at `X_BASE = 0, Y_BASE = 32, Z_BASE = 64`. Those coincide, and both files use
the same `SB = 8` limb encoding — so one set of three 32-column blocks and one set of 96 8-bit range
lookups serves all three operations. Only the reduction witnesses differ, and those get their own
columns. -/

/-- The multiply's quotient block: 32 columns of 8-bit limbs at `96`. Unused on an add/sub row
(the witness fills it with zeros, which its own range lookups accept). -/
def ALU_Q_BASE : Nat := 3 * SK
/-- The multiply's 62 carry columns at `128`, range-checked at `CB = 16`. -/
def ALU_C_BASE : Nat := 4 * SK
/-- ⚑ The add/sub carry BIT, at `190` — its OWN column at width 1, not a cell of the quotient
block. `PastaAddSubSound.adDigit_abs_le` needs `0 ≤ c < 2` to bound the digit by four bytes; an
8-bit column would need that bound re-derived, so this file spends one column and one width-1 table
instead of re-proving a bound that already exists. -/
def ALU_AC_COL : Nat := 4 * SK + (NG - 1)
/-- The add/sub carry chain: 31 columns at `191`, range-checked at `ACB = 8`. -/
def ALU_ACAR_BASE : Nat := ALU_AC_COL + 1

/-- The multiply selector. -/
def SEL_MUL : Nat := ALU_ACAR_BASE + (NA - 1)
/-- The add selector. -/
def SEL_ADD : Nat := SEL_MUL + 1
/-- The sub selector. -/
def SEL_SUB : Nat := SEL_MUL + 2
/-- ⚑ The CHAIN selector — the only inter-row wiring the main rail can carry (§4). -/
def SEL_CHAIN : Nat := SEL_MUL + 3

/-- `4·32 + 62 + 1 + 31 + 4 = 226` declared main columns. -/
def ALU_WIDTH : Nat := SEL_CHAIN + 1

theorem ALU_Q_BASE_eq : ALU_Q_BASE = 96 := rfl
theorem ALU_C_BASE_eq : ALU_C_BASE = 128 := rfl
theorem ALU_AC_COL_eq : ALU_AC_COL = 190 := rfl
theorem ALU_ACAR_BASE_eq : ALU_ACAR_BASE = 191 := rfl
theorem SEL_MUL_eq : SEL_MUL = 222 := rfl
theorem SEL_CHAIN_eq : SEL_CHAIN = 225 := rfl
theorem ALU_WIDTH_eq : ALU_WIDTH = 226 := rfl

/-- ⚑ **THE MULTIPLY'S LAYOUT IS UNMOVED.** The ALU reuses `PastaFieldSound`'s own base constants
verbatim, so `fpMulSound_forces` — which is stated at `X_BASE / Y_BASE / Z_BASE / Q_BASE / C_BASE` —
is a statement about THESE columns and needs no re-basing. A future edit that moved either layout
would break this `rfl` rather than silently make §3's reuse a statement about a different row. -/
theorem alu_reuses_the_multiply_layout :
    (ALU_Q_BASE, ALU_C_BASE) = (Q_BASE, C_BASE) := rfl

/-- …and the add/sub operand blocks coincide with the multiply's, which is the whole saving. -/
theorem alu_reuses_the_addsub_operand_layout :
    (X_BASE, Y_BASE, Z_BASE) = (AX_BASE, AY_BASE, AZ_BASE) := rfl

/-! ## §2 — THE GATES.

Each operation's body is the expression its own sound module already emits, multiplied by that
operation's selector. That multiplication is the ONLY new algebra in this file, and it is what makes
one row able to be three things. -/

/-- The selector-gated multiply gate at index `m`: `sMul · coefExpr m`. ⚑ Degree **3** — the body is
already degree 2 (`x_i · y_j`) and the selector adds one. The deployed main-AIR degree budget is 3
(`descriptor_ir2.rs`'s `ir2_degree_budget`), so this sits exactly at it. -/
def aluMulExpr (pl : Nat → ℤ) (m : Nat) : Expr :=
  .mul (.var SEL_MUL) (coefExpr X_BASE Y_BASE Z_BASE ALU_Q_BASE ALU_C_BASE pl m)

/-- The selector-gated add/sub gate at index `m`: `s · adExpr m`. Degree **2** — the add/sub body is
linear in the trace apart from the single `c · constant` term, so the selector lands it at 2. -/
def aluAddSubExpr (sel : Nat) (pl : Nat → ℤ) (sy sc : ℤ) (m : Nat) : Expr :=
  .mul (.var sel) (adExpr X_BASE Y_BASE Z_BASE ALU_AC_COL ALU_ACAR_BASE pl sy sc m)

/-- `s · (s − 1)` — the booleanity body. Over BabyBear (a FIELD) this forces `s ≡ 0` or `s ≡ 1`,
which is §3's `alu_selector_is_boolean`. -/
def boolExpr (sel : Nat) : Expr :=
  Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toSource
    (Dregg2.Circuit.GateExpr.gBool (.leaf sel))

theorem boolExpr_eq (sel : Nat) :
    boolExpr sel = .mul (.var sel) (.add (.var sel) (.const (-1))) := rfl

/-- `sMul + sAdd + sSub − 1` — exactly one operation per row. -/
def selSumExpr : Expr :=
  .add (.add (.add (.var SEL_MUL) (.var SEL_ADD)) (.var SEL_SUB)) (.const (-1))

/-- ⚑ **THE CHAIN LEG at limb `i`**: `sChain · (nxt(X_BASE + i) − loc(Z_BASE + i))`. A `.transition`
window gate, so `nxt` is the genuine successor row (`WindowLeg.mainRailOk` refuses a `nxt` read
under any other selector, and that refusal is the reason this is the one wiring available). -/
def chainWindowExpr (i : Nat) : WindowExpr :=
  .mul (.loc SEL_CHAIN)
       (Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toWindow
         (Dregg2.Circuit.GateExpr.gThread (X_BASE + i) (Z_BASE + i)))

/-- The `NG − 1 = 62` multiply-carry columns. -/
def aluCarryCols : List Nat := (List.range (NG - 1)).map (ALU_C_BASE + ·)
/-- The `NA − 1 = 31` add/sub-carry columns. -/
def aluAcarCols : List Nat := (List.range (NA - 1)).map (ALU_ACAR_BASE + ·)

/-- ⚑ **THE SOURCE AIR OF ONE PASTA ALU ROW**, modulus-parametric in the limb vector `pl`.

Leg order is emission order, and it is: 63 multiply gates · 32 add gates · 32 sub gates · 4
booleanity gates · 1 selector-sum gate · 32 chain window legs · 7 limb legs. -/
def pastaAluAir (pl : Nat → ℤ) : EffectAir :=
  { tables := [ mainTableDef ALU_WIDTH
              , ⟨rangeTidW SB, "range_w8", 1, .rangeLimb SB⟩
              , ⟨rangeTidW CB, "range_w16", 1, .rangeLimb CB⟩
              , ⟨rangeTidW CBITS, "range_w1", 1, .rangeLimb CBITS⟩ ]
  , legs :=
      (List.range NG).map (fun m => AirLeg.gate ⟨aluMulExpr pl m, .const 0⟩)
      ++ (List.range NA).map
           (fun m => AirLeg.gate ⟨aluAddSubExpr SEL_ADD pl 1 (-1) m, .const 0⟩)
      ++ (List.range NA).map
           (fun m => AirLeg.gate ⟨aluAddSubExpr SEL_SUB pl (-1) 1 m, .const 0⟩)
      ++ [ AirLeg.gate ⟨boolExpr SEL_MUL, .const 0⟩
         , AirLeg.gate ⟨boolExpr SEL_ADD, .const 0⟩
         , AirLeg.gate ⟨boolExpr SEL_SUB, .const 0⟩
         , AirLeg.gate ⟨boolExpr SEL_CHAIN, .const 0⟩
         , AirLeg.gate ⟨selSumExpr, .const 0⟩ ]
      ++ (List.range SK).map (fun i => AirLeg.window ⟨RowSel.transition, chainWindowExpr i⟩)
      ++ [ AirLeg.limbs ⟨limbCols X_BASE, SB, rangeTidW SB⟩
         , AirLeg.limbs ⟨limbCols Y_BASE, SB, rangeTidW SB⟩
         , AirLeg.limbs ⟨limbCols Z_BASE, SB, rangeTidW SB⟩
         , AirLeg.limbs ⟨limbCols ALU_Q_BASE, SB, rangeTidW SB⟩
         , AirLeg.limbs ⟨aluCarryCols, CB, rangeTidW CB⟩
         , AirLeg.limbs ⟨[ALU_AC_COL], CBITS, rangeTidW CBITS⟩
         , AirLeg.limbs ⟨aluAcarCols, ACB, rangeTidW SB⟩ ] }

/-- ⚑ **The compiler ACCEPTS this block.** Every leg has a deployed main-rail image: the 32 window
legs because they are `.transition` (the ONLY scope in which `nxt` is the successor row and not the
wrap row), and the seven `limbs` legs because every declared width is `0 < bits ≤ 29`. A window leg
re-scoped to `.all`, or a limb width of 30, would emit `refuseConstraints` and make this false. -/
theorem pastaAluAir_mainRailOk (pl : Nat → ℤ) : (pastaAluAir pl).mainRailOk = true := by
  unfold pastaAluAir EffectAir.mainRailOk
  simp only [List.all_append, List.all_map, Bool.and_eq_true, List.all_eq_true]
  -- ⚠ `simp only` leaves the conjunction LEFT-nested here, so a fixed `⟨?_, …⟩` arity is a
  -- brittle way to split it. `repeat' apply And.intro` is nesting-agnostic.
  repeat' apply And.intro
  all_goals first
    | decide
    | (intro m _; rfl)

/-- ⚑ **THE TIE VERDICT, PROVED ONCE AND MODULUS-PARAMETRICALLY.** The ALU row publishes NOTHING —
its descriptors carry `piCount = 0` and no `.pin` leg appears in the block — so every leg lands in
the non-`pin` arm of `EffectAir.pinsTied` and the verdict follows from the leg SHAPES, at seven
blocks rather than the 171 legs a `decide` would whnf one at a time.

⚠ Not a weakening: the same `pinsTied`, at the same value. Growing a `.pin` leg here would leave
the `intro m _; rfl` arm with a goal it cannot close, and this would go red. -/
theorem pastaAluAir_pinsTied (pl : Nat → ℤ) : (pastaAluAir pl).pinsTied = true := by
  unfold pastaAluAir EffectAir.pinsTied
  simp only [List.all_append, List.all_map, Bool.and_eq_true]
  repeat' apply And.intro
  all_goals rfl

/-- ⚑ **THE TIED SOURCE** — `(pastaAluAir pLimb)` carrying its two decidable verdicts in its TYPE:
`mainRailOk` (main-rail expressible) and `pinsTied` (every published column is DERIVED by another
leg). A `TiedAir` cannot be built for a block that publishes a column nothing else constrains, so a
decorative pin is unrepresentable here rather than detectable by a census afterwards.

⚑ **BOTH VERDICTS ARE SUPPLIED, NOT RE-DERIVED.** The fields are `autoParam`s defaulting to
`by decide`; left blank they re-derive, inside the elaborator's `whnf` and at the CONCRETE limb
vector, the two facts the parametric theorems above already carry — once per instance, and this
file has four. -/
def fpAluTiedAir : Dregg2.Circuit.Emit.EffectLower.TiedAir where
  air  := (pastaAluAir pLimb)
  ok   := pastaAluAir_mainRailOk pLimb
  tied := pastaAluAir_pinsTied pLimb

/-- The `fp` ALU: every row is an operation modulo the Pallas base / Vesta scalar prime. -/
def fpAluDesc : EffectVmDescriptor2 :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-pasta-alu-sound::v1" ALU_WIDTH 0 [] fpAluTiedAir).val

/-- ⚑ **THE CERTIFICATE, produced by the emit.** Every leg of the source is FORCED by the emitted
descriptor's constraints on any row window that satisfies them — `AirLeg.forces`, stated in the
SOURCE's vocabulary and never mentioning the lowering, so it is not `P → P`. Not re-derived here.

**Zero bytes move**: `lowerTiedAir … |>.val` is `lowerAir …` by `rfl`. -/
theorem fpAluDesc_certified :
    Dregg2.Circuit.Emit.EffectLower.CertifiedRefines fpAluDesc [] (pastaAluAir pLimb) :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-pasta-alu-sound::v1" ALU_WIDTH 0 [] fpAluTiedAir).property

/-- ⚑ **THE ZERO.** The certified lowering emits the term the bare lowering emitted, by `rfl` — so
the migration changed what this definition PROVES, not what it PRODUCES. No re-emit, no VK rotation.
Also the unfolding lemma for the cost/shape proofs below, which reason through `lowerAir`. -/
theorem fpAluDesc_eq_lowerAir :
    fpAluDesc = Dregg2.Circuit.Emit.EffectLower.lowerAir "dregg-pasta-alu-sound::v1" ALU_WIDTH 0 [] (pastaAluAir pLimb) := rfl

/-- ⚑ **THE TIED SOURCE** — `(pastaAluAir qLimb)` carrying its two decidable verdicts in its TYPE:
`mainRailOk` (main-rail expressible) and `pinsTied` (every published column is DERIVED by another
leg). A `TiedAir` cannot be built for a block that publishes a column nothing else constrains, so a
decorative pin is unrepresentable here rather than detectable by a census afterwards. -/
def fqAluTiedAir : Dregg2.Circuit.Emit.EffectLower.TiedAir where
  air  := (pastaAluAir qLimb)
  ok   := pastaAluAir_mainRailOk qLimb
  tied := pastaAluAir_pinsTied qLimb

/-- The `fq` ALU: the same shape at the Vesta base / Pallas scalar prime. The encoding is
field-independent; only the constant limb vector moves. -/
def fqAluDesc : EffectVmDescriptor2 :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-pasta-alu-fq-sound::v1" ALU_WIDTH 0 [] fqAluTiedAir).val

/-- ⚑ **THE CERTIFICATE, produced by the emit.** Every leg of the source is FORCED by the emitted
descriptor's constraints on any row window that satisfies them — `AirLeg.forces`, stated in the
SOURCE's vocabulary and never mentioning the lowering, so it is not `P → P`. Not re-derived here.

**Zero bytes move**: `lowerTiedAir … |>.val` is `lowerAir …` by `rfl`. -/
theorem fqAluDesc_certified :
    Dregg2.Circuit.Emit.EffectLower.CertifiedRefines fqAluDesc [] (pastaAluAir qLimb) :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-pasta-alu-fq-sound::v1" ALU_WIDTH 0 [] fqAluTiedAir).property

/-- ⚑ **THE ZERO.** The certified lowering emits the term the bare lowering emitted, by `rfl` — so
the migration changed what this definition PROVES, not what it PRODUCES. No re-emit, no VK rotation.
Also the unfolding lemma for the cost/shape proofs below, which reason through `lowerAir`. -/
theorem fqAluDesc_eq_lowerAir :
    fqAluDesc = Dregg2.Circuit.Emit.EffectLower.lowerAir "dregg-pasta-alu-fq-sound::v1" ALU_WIDTH 0 [] (pastaAluAir qLimb) := rfl

/-- ⚑ **THE EMITTED COST, as a theorem rather than a caption.** `63 + 32 + 32` operation gates
`+ 4` booleanity `+ 1` selector-sum `+ 32` chain windows `+ 222` range lookups
(`4·32` limbs + `62` multiply carries + `1` carry bit + `31` add/sub carries) = **386**
constraints. Against the standalone multiply's `253` that is **1.53× the constraints** — and
against its `694` committed columns the ALU's `794` is **1.14× the WIDTH**, which is the number
that decides the trace size. A row that can be any of three operations costs 14% more memory than a
row that can only multiply.

**THE LEG SHAPE — 171 legs and 222 range lookups**, and the two numbers are separate because
a limb leg is ONE leg and MANY lookups. `63` multiply gates `+ 32` add `+ 32` sub `+ 4` booleanity
`+ 1` selector-sum `+ 32` chain windows `+ 7` limb legs = `171`; the seven limb legs carry
`4·32 + 62 + 1 + 31 = 222` lookups between them.

⚠ The emitted CONSTRAINT count is `171 − 7 + 222 = 386` — every non-limb leg lowers to exactly one
constraint (`EffectLower.lowerLeg_ne_nil` is the floor; the gate/window arms are singletons) and a
limb leg lowers to one per limb. That figure is asserted in Rust against the emitted JSON
(`circuit/tests/pasta_alu_verifier_row_proves.rs`) rather than here, because kernel-reducing the
assembled 386-constraint list did not terminate inside `maxHeartbeats 4000000` — which is itself
worth recording: the compiler's output is checkable by the deployed parser far more cheaply than by
the kernel, so the shape pin lives at the SOURCE (here) and the byte pin at the ARTIFACT (Rust). -/
theorem pastaAluAir_leg_shape (pl : Nat → ℤ) : (pastaAluAir pl).legs.length = 171 := by
  simp [pastaAluAir, NG, NA, SK]

/-- The declared width the descriptor carries. The COMMITTED width is `794`; that is a fact about
the deployed `MainLayout::build`, measured in Rust, not derivable here. -/
theorem fpAluDesc_trace_width : fpAluDesc.traceWidth = 226 := rfl

/-! ## §3 — WHAT A ROW FORCES.

Each polarity reduces to the forcing theorem its own sound module already proved. Nothing is
re-derived: both source theorems are parametric in their base columns AND in the limb vector, so
instantiating them at the ALU's layout is a rewrite, not a second proof of the same bound. -/

/-- The gate body of an ALU multiply row evaluates to `sMul · coefBody`. -/
theorem aluMulExpr_eval (a : Assignment) (pl : Nat → ℤ) (m : Nat) :
    (aluMulExpr pl m).eval a
      = a SEL_MUL * coefBody a X_BASE Y_BASE Z_BASE ALU_Q_BASE ALU_C_BASE pl m := by
  unfold aluMulExpr
  simp only [Expr.eval, coefExpr_eval]

/-- …and of an ALU add/sub row to `s · adBody`. -/
theorem aluAddSubExpr_eval (a : Assignment) (sel : Nat) (pl : Nat → ℤ) (sy sc : ℤ) (m : Nat) :
    (aluAddSubExpr sel pl sy sc m).eval a
      = a sel * adBody a X_BASE Y_BASE Z_BASE ALU_AC_COL ALU_ACAR_BASE pl sy sc m := by
  unfold aluAddSubExpr
  simp only [Expr.eval, adExpr_eval]

/-- ⚑ **A SELECTOR IS A BIT.** The booleanity gate's DEPLOYED reading is `P ∣ s·(s−1)`; `P` is
prime, so `P` divides one of the factors and `s` is `0` or `1` mod `P`. This is the fact the three
forcing theorems below take as a hypothesis in its `= 1` form, and it is what makes "the selector
names the operation" a constraint rather than a convention. -/
theorem alu_selector_is_boolean (a : Assignment) (sel : Nat)
    (h : P ∣ (boolExpr sel).eval a) :
    (a sel ≡ 0 [ZMOD P]) ∨ (a sel ≡ 1 [ZMOD P]) := by
  have hp : Prime (P : ℤ) := by
    rw [Int.prime_iff_natAbs_prime]
    norm_num [Dregg2.Circuit.Emit.EffectLower.P]
  have hbody : (boolExpr sel).eval a = a sel * (a sel - 1) := by
    simp only [boolExpr_eq, Expr.eval]; ring
  rw [hbody] at h
  rcases hp.dvd_mul.mp h with h1 | h2
  · exact Or.inl (Int.modEq_zero_iff_dvd.mpr h1)
  · exact Or.inr (Int.ModEq.symm (Int.modEq_iff_dvd.mpr (by simpa using h2)))

/-- ⚑ **THE MULTIPLY POLARITY.** Hypotheses: the row's multiply selector is on, the range facts the
seven emitted `limbs` legs supply, and the DEPLOYED reading of every emitted multiply gate
(`P ∣ body` — what `prove_vm_descriptor2` checks). Conclusion: the Pasta congruence.

The step from the SELECTOR-GATED body to the bare one is the only new content, and it is one line:
`P ∣ 1 · body`. -/
theorem alu_mul_forces (a : Assignment) (hsel : a SEL_MUL = 1)
    (hx : ∀ i, i < SK → 0 ≤ a (X_BASE + i) ∧ a (X_BASE + i) < 2 ^ SB)
    (hy : ∀ i, i < SK → 0 ≤ a (Y_BASE + i) ∧ a (Y_BASE + i) < 2 ^ SB)
    (hz : ∀ i, i < SK → 0 ≤ a (Z_BASE + i) ∧ a (Z_BASE + i) < 2 ^ SB)
    (hq : ∀ i, i < SK → 0 ≤ a (ALU_Q_BASE + i) ∧ a (ALU_Q_BASE + i) < 2 ^ SB)
    (hc : ∀ i, i < NG - 1 → 0 ≤ a (ALU_C_BASE + i) ∧ a (ALU_C_BASE + i) < 2 ^ CB)
    (hgates : ∀ m, m < NG → P ∣ (aluMulExpr pLimb m).eval a) :
    (pN : ℤ) ∣ (sVal a X_BASE * sVal a Y_BASE - sVal a Z_BASE) :=
  felt_gates_force_congruence a X_BASE Y_BASE Z_BASE ALU_Q_BASE ALU_C_BASE pLimb (pN : ℤ)
    hx hy hz hq pLimb_bounds pLimb_recomposes hc
    (fun m hm => by
      have h := hgates m hm
      rw [aluMulExpr_eval, hsel, one_mul] at h
      exact h)

/-- The same at the Vesta-base / Pallas-scalar modulus. -/
theorem alu_mul_forces_fq (a : Assignment) (hsel : a SEL_MUL = 1)
    (hx : ∀ i, i < SK → 0 ≤ a (X_BASE + i) ∧ a (X_BASE + i) < 2 ^ SB)
    (hy : ∀ i, i < SK → 0 ≤ a (Y_BASE + i) ∧ a (Y_BASE + i) < 2 ^ SB)
    (hz : ∀ i, i < SK → 0 ≤ a (Z_BASE + i) ∧ a (Z_BASE + i) < 2 ^ SB)
    (hq : ∀ i, i < SK → 0 ≤ a (ALU_Q_BASE + i) ∧ a (ALU_Q_BASE + i) < 2 ^ SB)
    (hc : ∀ i, i < NG - 1 → 0 ≤ a (ALU_C_BASE + i) ∧ a (ALU_C_BASE + i) < 2 ^ CB)
    (hgates : ∀ m, m < NG → P ∣ (aluMulExpr qLimb m).eval a) :
    (qN : ℤ) ∣ (sVal a X_BASE * sVal a Y_BASE - sVal a Z_BASE) :=
  felt_gates_force_congruence a X_BASE Y_BASE Z_BASE ALU_Q_BASE ALU_C_BASE qLimb (qN : ℤ)
    hx hy hz hq qLimb_bounds qLimb_recomposes hc
    (fun m hm => by
      have h := hgates m hm
      rw [aluMulExpr_eval, hsel, one_mul] at h
      exact h)

/-- ⚑ **THE ADD POLARITY**, through `addsub_gates_force_congruence` at `(sy, sc) = (1, −1)`. -/
theorem alu_add_forces (a : Assignment) (hsel : a SEL_ADD = 1)
    (hx : ∀ i, i < SK → 0 ≤ a (X_BASE + i) ∧ a (X_BASE + i) < 2 ^ SB)
    (hy : ∀ i, i < SK → 0 ≤ a (Y_BASE + i) ∧ a (Y_BASE + i) < 2 ^ SB)
    (hz : ∀ i, i < SK → 0 ≤ a (Z_BASE + i) ∧ a (Z_BASE + i) < 2 ^ SB)
    (hcb : 0 ≤ a ALU_AC_COL ∧ a ALU_AC_COL < 2)
    (hc : ∀ i, i < NA - 1 → 0 ≤ a (ALU_ACAR_BASE + i) ∧ a (ALU_ACAR_BASE + i) < 2 ^ ACB)
    (hgates : ∀ m, m < NA → P ∣ (aluAddSubExpr SEL_ADD pLimb 1 (-1) m).eval a) :
    (pN : ℤ) ∣ (sVal a X_BASE + sVal a Y_BASE - sVal a Z_BASE) := by
  have h := addsub_gates_force_congruence a X_BASE Y_BASE Z_BASE ALU_AC_COL ALU_ACAR_BASE pLimb
    1 (-1) (pN : ℤ) (Or.inl rfl) (Or.inr rfl) hx hy hz pLimb_bounds pLimb_recomposes hcb hc
    (fun m hm => by
      have hg := hgates m hm
      rw [aluAddSubExpr_eval, hsel, one_mul] at hg
      exact hg)
  simpa using h

/-- ⚑ **THE SUB POLARITY**, at `(sy, sc) = (−1, 1)`. -/
theorem alu_sub_forces (a : Assignment) (hsel : a SEL_SUB = 1)
    (hx : ∀ i, i < SK → 0 ≤ a (X_BASE + i) ∧ a (X_BASE + i) < 2 ^ SB)
    (hy : ∀ i, i < SK → 0 ≤ a (Y_BASE + i) ∧ a (Y_BASE + i) < 2 ^ SB)
    (hz : ∀ i, i < SK → 0 ≤ a (Z_BASE + i) ∧ a (Z_BASE + i) < 2 ^ SB)
    (hcb : 0 ≤ a ALU_AC_COL ∧ a ALU_AC_COL < 2)
    (hc : ∀ i, i < NA - 1 → 0 ≤ a (ALU_ACAR_BASE + i) ∧ a (ALU_ACAR_BASE + i) < 2 ^ ACB)
    (hgates : ∀ m, m < NA → P ∣ (aluAddSubExpr SEL_SUB pLimb (-1) 1 m).eval a) :
    (pN : ℤ) ∣ (sVal a X_BASE - sVal a Y_BASE - sVal a Z_BASE) := by
  have h := addsub_gates_force_congruence a X_BASE Y_BASE Z_BASE ALU_AC_COL ALU_ACAR_BASE pLimb
    (-1) 1 (pN : ℤ) (Or.inr rfl) (Or.inl rfl) hx hy hz pLimb_bounds pLimb_recomposes hcb hc
    (fun m hm => by
      have hg := hgates m hm
      rw [aluAddSubExpr_eval, hsel, one_mul] at hg
      exact hg)
  simpa [sub_eq_add_neg] using h

/-- ⚑ **AND THE OTHER POLARITY OF THE SELECTOR: A ROW WITH ITS SELECTOR OFF ASSERTS NOTHING.**
At `s = 0` every gate of that operation reads `0 · body`, which is `0` for EVERY assignment — so
the operation's 32 or 63 gates are satisfied by any witness at all. This is not a defect; it is
what a selector IS. It is stated because a reader who sees "386 constraints" must not read it as
"386 checks on every row": on a multiply row the 64 add/sub gates check nothing, and on an add row
the 63 multiply gates and the whole quotient block check nothing but their ranges. -/
theorem alu_selector_off_asserts_nothing (a : Assignment) (sel : Nat) (pl : Nat → ℤ)
    (sy sc : ℤ) (m : Nat) (h : a sel = 0) :
    (aluAddSubExpr sel pl sy sc m).eval a = 0 := by
  rw [aluAddSubExpr_eval, h, zero_mul]

/-! ## §4 — THE CHAIN, and the exact shape of what it does not do. -/

/-- The chain leg's body at limb `i`, read against a two-row window given as two assignments. -/
def chainBody (cur nxt : Assignment) (i : Nat) : ℤ :=
  cur SEL_CHAIN * (nxt (X_BASE + i) - cur (Z_BASE + i))

/-- ⚑ **A CHAINED TRANSITION FEEDS ONE ROW'S RESULT TO THE NEXT ROW'S FIRST OPERAND.** With the
chain selector on, the deployed reading `P ∣ body` gives limb-wise congruence of the next row's `x`
block with this row's `z` block; the recompositions therefore agree mod `P` as well.

⚠ The conclusion is a congruence mod `P` (BabyBear), not an equality — which is the honest
statement, because that is all the gate checks. Both blocks are separately range-checked into
`[0, 2^8)` by the emitted limb legs, so on any trace the prover can actually carry the two limbs are
equal as integers; that step needs the range facts and is `chain_forces_limb_equality`. -/
theorem chain_forces_limb_congruence (cur nxt : Assignment) (i : Nat)
    (hsel : cur SEL_CHAIN = 1) (h : P ∣ chainBody cur nxt i) :
    nxt (X_BASE + i) ≡ cur (Z_BASE + i) [ZMOD P] := by
  unfold chainBody at h
  rw [hsel, one_mul] at h
  exact Int.ModEq.symm (Int.modEq_iff_dvd.mpr (by simpa using h))

/-- …and with the range facts the emitted limb legs supply, limb-wise EQUALITY over ℤ. Both cells
are 8-bit, so the congruence cannot be hiding a multiple of `P`. -/
theorem chain_forces_limb_equality (cur nxt : Assignment) (i : Nat)
    (hsel : cur SEL_CHAIN = 1) (h : P ∣ chainBody cur nxt i)
    (hn : 0 ≤ nxt (X_BASE + i) ∧ nxt (X_BASE + i) < 2 ^ SB)
    (hc : 0 ≤ cur (Z_BASE + i) ∧ cur (Z_BASE + i) < 2 ^ SB) :
    nxt (X_BASE + i) = cur (Z_BASE + i) := by
  have hmod := chain_forces_limb_congruence cur nxt i hsel h
  have hb : (2 : ℤ) ^ SB ≤ P := by norm_num [SB, Dregg2.Circuit.Emit.EffectLower.P]
  exact Dregg2.Circuit.Emit.EffectLower.eq_of_modEq_canon hn.1 (lt_of_lt_of_le hn.2 hb)
    hc.1 (lt_of_lt_of_le hc.2 hb) hmod

/-- ⚑ **AND THE COUNTERWEIGHT, AS A THEOREM.** With the chain selector OFF the leg's body is `0` on
every assignment — so the next row's operand block is related to this row by NOTHING.

This is the honest boundary of what the emitted AIR establishes. A trace of `N` rows in which every
`sChain` is `0` satisfies the chain legs completely and is `N` UNRELATED Pasta operations. The
number of chained transitions is therefore the measure of how much of a verifier a given trace is,
and it is a property of the TRACE, not of this descriptor. §5's row census prices the operations;
it does not establish that any of them are wired to each other. -/
theorem unchained_transition_relates_nothing (cur nxt : Assignment) (i : Nat)
    (h : cur SEL_CHAIN = 0) : chainBody cur nxt i = 0 := by
  unfold chainBody; rw [h, zero_mul]

/-- ⚑ **THE IR-EXPRESSIBILITY FINDING, as a decidable fact rather than prose.** The chain is the
only inter-row wiring available, and the reason is structural: `WindowLeg.mainRailOk` REFUSES a
`nxt` read under every selector except `.transition`, and `.transition` applies UNIFORMLY to every
row. So a straight-line chain `row i → row i+1` is expressible and an arbitrary dataflow
`row i → row j` is not — there is no copy-permutation leg on the main rail, and a memory-bus
alternative would need `mult ≠ 1` (a padded/conditional query), which `LookupLeg.mainRailOk` also
refuses. Both refusals, exhibited. -/
theorem inter_row_wiring_is_transition_only :
    (WindowLeg.mk RowSel.transition (chainWindowExpr 0)).mainRailOk = true
      ∧ (WindowLeg.mk RowSel.all (chainWindowExpr 0)).mainRailOk = false
      ∧ (WindowLeg.mk RowSel.first (chainWindowExpr 0)).mainRailOk = false
      ∧ (WindowLeg.mk RowSel.last (chainWindowExpr 0)).mainRailOk = false := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> rfl

/-! ## §5 — THE STAGE CENSUS.

⚑ These are PRICES, not coverage proofs. Each stage's row budget is `atom rows × operations`, where
the operation counts are read at o1-labs source (the docblock cites file and line) and the atom
costs are the emitted `pastaAluAir` row. A stage's number moving is a real signal; a stage's number
being right is not evidence that the stage's TRACE is that stage. -/

/-- Complete-addition (Renes–Costello–Batina, `add-2015-rcb`) over a short-Weierstrass Pasta curve,
in ALU rows: **12 multiplies + 29 add/subs = 41**. Strongly unified, so one gadget serves both the
doubling and the addition step and there is no exceptional-case split. -/
def ROWS_PER_COMPLETE_ADD : Nat := 41

/-- ⚑ **A bit-plane MSM over `n` bases costs `256 · (n + 1)` complete adds** — 256 shared doublings
of the accumulator plus `256 · n` conditional adds. This is the in-AIR analogue of the fused
Pippenger the Rust verifier runs: the doublings are SHARED across all `n` bases, which is why the
cost is `n + 1` and not `n` ladders of 256. -/
def msmRows (n : Nat) : Nat := 256 * (n + 1) * ROWS_PER_COMPLETE_ADD

/-- One Kimchi Fq Poseidon ROUND in ALU rows — **21 multiplies + 9 additions = 30**. Three S-boxes
at four multiplies each for `x^7` (the chain is `x²·x²·x²·x`), the 3×3 MDS's nine
constant-multiplies, and then the nine ADDITIONS the matvec's two sums per row and the three round
constants need. A constant-multiply is still a full ALU multiply row in this encoding, but its gate
is degree 1 in the trace rather than degree 2.

⚠ **THIS WAS `3·4 + 9 = 21` UNTIL 2026-08-08 AND THE ADDITIONS WERE SIMPLY NOT COUNTED** — every
price derived below it was 42.9% low, while `MinaWrapVerifierSponge` had *proved* the emitted round
is 30 instructions and the tree carried both numbers side by side. The round is no longer a
free-standing literal: `MinaWrapVerifierSponge.the_census_round_is_the_emitted_round` proves this
`def` equal to `(roundAt r).length` of the EMITTED permutation, for every round, so the two cannot
drift apart again without a build error. -/
def MULS_PER_POSEIDON_ROUND : Nat := 3 * 4 + 9

/-- The nine ADDITIONS of a round: two sums per MDS row (3 × 2 = 6) and one round constant per lane
(3). These are the ones §5 did not count. `MinaWrapVerifierSponge.roundInstrs_opcode_split` is the
same 21/9 split read off the emitted instruction list's opcodes. -/
def ADDS_PER_POSEIDON_ROUND : Nat := 3 * 2 + 3

def ROWS_PER_POSEIDON_ROUND : Nat := MULS_PER_POSEIDON_ROUND + ADDS_PER_POSEIDON_ROUND

/-- Kimchi's Fq sponge is 55 FULL rounds — there is no partial-round schedule to discount. -/
def POSEIDON_ROUNDS : Nat := 55

/-- One Fq Poseidon permutation in ALU rows: **1 650**, welded to `permInstrs.length` downstream by
`MinaWrapVerifierSponge.the_census_perm_is_the_emitted_permutation`. -/
def ROWS_PER_POSEIDON_PERM : Nat := POSEIDON_ROUNDS * ROWS_PER_POSEIDON_ROUND

theorem rows_per_poseidon_round_eq :
    MULS_PER_POSEIDON_ROUND = 21 ∧ ADDS_PER_POSEIDON_ROUND = 9
      ∧ ROWS_PER_POSEIDON_ROUND = 30 := ⟨rfl, rfl, rfl⟩

theorem rows_per_poseidon_perm_eq : ROWS_PER_POSEIDON_PERM = 1650 := rfl

/-- The six stages, in transcript order, as `(name, rows)`. -/
def STAGE_TRANSCRIPT : Nat := 148 * ROWS_PER_POSEIDON_PERM
def STAGE_PUBLIC_COMM : Nat := msmRows 40
def STAGE_F_COMM : Nat := msmRows 1
def STAGE_FT_COMM : Nat := msmRows 9
def STAGE_XI_AGGREGATE : Nat := msmRows 47
def STAGE_OPENING : Nat := msmRows 34

/-- The whole of "everything except the SRS bases". -/
def VERIFIER_ROWS : Nat :=
  STAGE_TRANSCRIPT + STAGE_PUBLIC_COMM + STAGE_F_COMM + STAGE_FT_COMM
    + STAGE_XI_AGGREGATE + STAGE_OPENING

/-- ⚑ **THE PRICE.** `1 671 656` rows — the re-pricing lane's `1.51 M` recomputed from the atom,
and **10.7% above** it. That the two land in the same order of magnitude from independent routes is
what makes the number a measurement of one object; it is not tight agreement and is not claimed as
any.

⚠ This theorem read `1 598 396` and the docblock claimed "within 5.9%" until 2026-08-08, both
inherited from the 21-instruction round. -/
theorem verifier_rows_eq : VERIFIER_ROWS = 1671656 := by native_decide

/-- ⚑ **AND THE STAGE IT IS DOMINATED BY IS THE ξ-AGGREGATE, NOT THE TRANSCRIPT.** 47 bases is the
largest MSM in the verifier, and at `256 · 48` complete adds it is 30.1% of the whole. The transcript
— the stage this campaign's earlier drafts treated as the hard part — is 14.6%. The gap narrowed
when the round was re-counted (it was 31.5% against 10.7%); the ORDER did not change. -/
theorem xi_aggregate_dominates :
    STAGE_XI_AGGREGATE = 503808 ∧ STAGE_TRANSCRIPT = 244200
      ∧ STAGE_TRANSCRIPT < STAGE_XI_AGGREGATE := by native_decide

/-- The 32 768 SRS bases, priced in the SAME units — the leg this construction excludes. -/
def SRS_BASE_ROWS : Nat := msmRows 32768

/-- ⚑ **THE EXCLUDED LEG IS 205× THE INCLUDED ONE.** `343 943 424` rows against `1 671 656`. This
is the arithmetic behind "defer the IPA leg", and it is REAL — what was wrong was never the size,
only what the deferral was pointed at. (It read `215×` while the included side was priced at the
21-instruction round; the excluded leg did not move.)

⚠ The first draft of this theorem asserted `344 084 480` and a `170×` ratio, and `decide` refuted
it. The figure is `256 · 32 769 · 41`, and a hand-carried digit is exactly the kind of number this
campaign has been wrong about forty-seven times; that is the argument for a `theorem` over a
caption. -/
theorem srs_leg_dwarfs_the_rest :
    SRS_BASE_ROWS = 343943424 ∧ 205 * VERIFIER_ROWS < SRS_BASE_ROWS := by native_decide

/-! ## §5b — ⚑⚑ THE PRICE RE-DERIVED IN THE GEOMETRY THAT NOW EXISTS (2026-08-06)

§5's census is in ALU ROWS, and it was correct. What it could not say, because the object did not
exist when it was written, is what a row COSTS — and the standing figure the tree carried
(`LightClientMinaAir` §1b: *"≈10³ BabyBear constraints per Pasta multiplication … one Wrap
verification is then ≈10⁹ constraints … at a generous ~100 constraints packed per row that is ~10⁷
rows ≈ 2^23.3"*) answered that with an ESTIMATE. Two SOUND rows have since been emitted and
measured, so the estimate can be replaced by their declared widths.

⚑ **THE STANDING FIGURE GOT THE SHAPE WRONG, NOT ONLY THE SIZE.** It assumed ~100 constraints
packed per row and therefore 10⁷ rows — near a power-of-two ceiling, which is what made the verdict
*"the construction is wrong"*. The deployed sound rows are **3 048** and **226** columns wide, so the
same work is `2^18.09` rows: **35× fewer, and nearly seven powers of two under the measured `lb = 2`
ceiling of `2^25`.** The binding resource was never rows. It is committed CELLS.

⚠ **AND THE ATOM COUNT WAS CONFLATED.** §1b's *"≈1.06 M Pasta-field multiplications"* is neither
this census's multiply count nor its op count: `RCB` is 12 multiplies and 29 add/subs, so 34 816
complete additions are **417 792 multiplies and 1 009 664 add/subs**, and the transcript stage adds
**170 940 multiplies and 73 260 additions** — `588 732` multiplies inside `1 671 656` operations.
Priced against the two emitted descriptors' own declared constraint counts (253 for the multiply,
160 for the add/sub), charging every operation as a MULTIPLY over-charges by ~1.31×, and charging
each at 10³ constraints over-charges by ~5.2×.

⚠ This paragraph read `~1.34×` and `~4.4×` before 2026-08-08. Neither reproduces from the 253/160
descriptor pair at EITHER census, so they were prose rather than derivation; the two above are
computed from the counts named in the same sentence.

⚑ **WHAT MOVED ON 2026-08-08, WHEN §5's ROUND WENT 21 → 30 INSTRUCTIONS**: cells
`144 751 608 → 161 308 368`, rows `205 756 → 279 016`, witness `~579 MB → ~645 MB`, add/subs
`1 009 664 → 1 082 924`. ⚑ **THE MULTIPLY COUNT DID NOT MOVE** — it was `588 732` before and after,
because the census's `21` per round was the multiply count and was RIGHT; the nine additions per
round were the entire error. The CONCLUSION — rows were never the wall, cells are — survives, which
is the only reason a 35.6% error in the headline sat here for a day. It is welded now
(`MinaWrapVerifierSponge` §8), not restated.

⚠ **WHAT THESE THEOREMS ARE.** Prices, exactly as §5's are — `atom cells × operations`, where the
atom is an EMITTED descriptor's declared width. A number moving is a real signal; a number being
right is not evidence that any trace IS the stage it is named for. The SRS-base leg stays excluded
and §6 stays the reason. -/

/-- The sound complete addition's declared width — ONE row of `dregg-pasta-{pallas,vesta}-rcb-
thread::v1`. `PastaCurveSound.rcb_width_eq` is the same number from the allocator. -/
def RCB_ROW_COLS : Nat := 3048

/-- The sound Pasta ALU row's declared width — one row of `pasta-alu-sound::v1`, which is a multiply
OR an add OR a sub under a selector. `ALU_WIDTH` is the same number from this file's own layout. -/
def ALU_ROW_COLS : Nat := 226

theorem the_atom_widths_are_this_files_own : ALU_ROW_COLS = ALU_WIDTH := by native_decide

/-- The complete additions §5's MSM census implies: `msmRows n / ROWS_PER_COMPLETE_ADD`, summed. -/
def COMPLETE_ADDS : Nat := 256 * 41 + 256 * 2 + 256 * 10 + 256 * 48 + 256 * 35

theorem complete_adds_eq : COMPLETE_ADDS = 34816 := by native_decide

/-- ⚑ **AND IT IS §5's OWN CENSUS, NOT A SECOND ONE.** The five MSM stages' rows are exactly
`ROWS_PER_COMPLETE_ADD` times this count, so the two prices are about one object. -/
theorem the_adds_are_the_censuss_msm_rows :
    ROWS_PER_COMPLETE_ADD * COMPLETE_ADDS
      = STAGE_PUBLIC_COMM + STAGE_F_COMM + STAGE_FT_COMM + STAGE_XI_AGGREGATE + STAGE_OPENING := by
  native_decide

/-- ⚑ **THE COMMITTED-CELL PRICE OF ONE WRAP VERIFICATION**, excluding the SRS-base leg: the curve
work at the threaded sound row's width plus the transcript at the ALU row's. -/
def WRAP_CELLS : Nat := COMPLETE_ADDS * RCB_ROW_COLS + STAGE_TRANSCRIPT * ALU_ROW_COLS

/-- ⚑ **1.61 × 10⁸ committed cells** — `106 119 168` of curve and `55 189 200` of sponge. At four
bytes a felt that is ~645 MB of witness, which is the wall the estimate was reaching for and named
as rows instead. -/
theorem wrap_cells_eq :
    WRAP_CELLS = 161308368
    ∧ COMPLETE_ADDS * RCB_ROW_COLS = 106119168
    ∧ STAGE_TRANSCRIPT * ALU_ROW_COLS = 55189200 := by
  refine ⟨by native_decide, by native_decide, by native_decide⟩

/-- The total ROW count in the two sound geometries. -/
def WRAP_ROWS_SOUND : Nat := COMPLETE_ADDS + STAGE_TRANSCRIPT

/-- ⚑⚑ **THE ROW COUNT WAS NEVER THE WALL.** `279 016 < 2^19`, against the `lb = 2` ceiling of
`2^25` — and 35× under the standing estimate's own `10⁷ ≈ 2^23.3`, which is what made it read as
unreachable. The estimate was not 4× wrong about size and right about shape; it was wrong about
which resource binds.

⚠ The bound here was `< 2^18` and the margin `48×` while the transcript stage was priced at the
21-instruction round. Both moved by exactly the sponge's re-count; the verdict did not. -/
theorem the_row_count_was_never_the_wall :
    WRAP_ROWS_SOUND = 279016
    ∧ WRAP_ROWS_SOUND < 2 ^ 19
    ∧ WRAP_ROWS_SOUND < 2 ^ 25
    ∧ 35 * WRAP_ROWS_SOUND < 10000000 := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- The multiply / add-sub split of the same census — the figure §1b's *"1.06 M multiplications"*
conflated. `RCB` is 12 multiplies and 29 add/subs (`ROWS_PER_COMPLETE_ADD = 41`), and the transcript
stage splits `21 / 9` per round.

⚠ **THE OLD SPLIT SAID "every ALU row of the transcript stage is a multiply"** and charged all of
`STAGE_TRANSCRIPT` to `WRAP_MULS`. That sentence is exactly what §5's re-count refuted: 9 of every
30 transcript rows are additions. Carrying the old shape forward with the new total would have
mis-stated 73 260 additions as multiplies — a re-derivation that reproduces the error it corrects.
The split now comes off `MULS_PER_POSEIDON_ROUND`/`ADDS_PER_POSEIDON_ROUND`, so it moves with the
round. -/
def TRANSCRIPT_MULS : Nat := 148 * POSEIDON_ROUNDS * MULS_PER_POSEIDON_ROUND
def TRANSCRIPT_ADDS : Nat := 148 * POSEIDON_ROUNDS * ADDS_PER_POSEIDON_ROUND
def WRAP_MULS : Nat := COMPLETE_ADDS * 12 + TRANSCRIPT_MULS
def WRAP_ADDSUBS : Nat := COMPLETE_ADDS * 29 + TRANSCRIPT_ADDS

/-- The transcript split is a PARTITION of the transcript stage — no row is counted twice or lost. -/
theorem the_transcript_split_is_the_stage :
    TRANSCRIPT_MULS + TRANSCRIPT_ADDS = STAGE_TRANSCRIPT := by native_decide

theorem the_atom_census_splits :
    WRAP_MULS = 588732
    ∧ WRAP_ADDSUBS = 1082924
    ∧ TRANSCRIPT_MULS = 170940
    ∧ TRANSCRIPT_ADDS = 73260
    ∧ WRAP_MULS + WRAP_ADDSUBS = VERIFIER_ROWS := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- ⚑ **THE EXCLUDED SRS LEG, RE-PRICED IN THE SAME UNITS** — and it is worse in cells than in rows.
`SRS_BASE_ROWS / 41` complete additions at `3 048` columns is `2.56 × 10¹⁰` cells, **158× the rest**,
so §6's exclusion is not a rounding decision. (It read `176×` while the included side carried the
21-instruction round; the excluded leg is pure curve work and did not move.) -/
def SRS_BASE_CELLS : Nat := (SRS_BASE_ROWS / ROWS_PER_COMPLETE_ADD) * RCB_ROW_COLS

theorem the_srs_leg_dwarfs_it_in_cells_too :
    SRS_BASE_CELLS = 25569257472 ∧ 158 * WRAP_CELLS < SRS_BASE_CELLS := by
  refine ⟨by native_decide, by native_decide⟩

/-! ## §6 — THE OPENING IS VACUOUS UNTIL THE SRS-BASE LEG IS DISCHARGED.

⚑ This is the mandate's item 5, and it is here as a THEOREM because a comment cannot be checked.

The IPA opening relation the verifier ends on is, in the shape this construction can carry:

    lhs  =  Σᵢ (challengeᵢ · Lᵢ  +  challengeᵢ⁻¹ · Rᵢ)  +  C
    rhs  =  z₁ · (G + b·U)  +  z₂ · H          with   G := sg

and `sg` — the "shifted group element", `openings_proof.sg` — is a witness the prover supplies. Its
own defining relation is `sg = ⟨s, srs.g⟩`, an MSM over the 32 768 SRS bases, which is exactly the
leg §5 excludes. With that leg absent, `sg` enters this construction as a FREE point.

`opening_is_vacuous_when_sg_is_free` is that fact stated where it cannot be skipped: modelled as
a relation `R sg` which the verifier checks, if `sg` is existentially chosen by the prover and the
relation is solvable for `sg` at every value of the rest, then the relation refutes nothing. -/

/-- A minimal model of the closing check: the verifier accepts when `lhs` equals a value computed
from the prover-chosen `sg`. `f` is everything the rest of the verifier fixes; `g` is the
`sg`-dependent side. -/
def openingAccepts (f : ℤ) (g : ℤ → ℤ) (sg : ℤ) : Prop := f = g sg

/-- ⚑ **THE VACUITY, AS A THEOREM.** If the `sg`-side map `g` is surjective — which it is here,
because `sg` enters `rhs = z₁·(G + b·U) + z₂·H` linearly through `G := sg` with an invertible
coefficient — then for EVERY `f` a prover can choose an `sg` that makes the check pass. The 0.41 M
rows this stage costs therefore refute nothing at all until the SRS-base leg pins `sg` to
`⟨s, srs.g⟩`.

⚠ Read what this does and does not say. It does NOT say the opening stage is worthless: the stage
is the STRUCTURE the discharge plugs into, and every row of it is a real Pasta operation forced by
§3. It says that the stage's ACCEPTANCE is unconditional on `sg` while `sg` is free, so no
soundness claim may be attached to it, and any bound quoted for the construction must exclude it. -/
theorem opening_is_vacuous_when_sg_is_free (g : ℤ → ℤ) (hsurj : Function.Surjective g) (f : ℤ) :
    ∃ sg, openingAccepts f g sg := by
  obtain ⟨sg, hsg⟩ := hsurj f
  exact ⟨sg, hsg.symm⟩

/-- The concrete instance: `sg` enters linearly with a unit coefficient, so the surjectivity
hypothesis above is discharged rather than assumed. `z₁` is the prover's IPA scalar and the map is
`sg ↦ z₁·sg + rest`; at `z₁ = 1` (and generally at any unit) it is a bijection of ℤ. -/
theorem sg_side_is_surjective (rest : ℤ) : Function.Surjective (fun sg : ℤ => sg + rest) :=
  fun y => ⟨y - rest, by ring⟩

/-- ⚑ **THE VACUITY, WITH NO HYPOTHESIS LEFT TO DOUBT.** The opening check as this construction
carries it accepts at EVERY value of everything else, by choosing `sg`. -/
theorem opening_accepts_everything_while_sg_is_free (rest f : ℤ) :
    ∃ sg, openingAccepts f (fun s => s + rest) sg :=
  opening_is_vacuous_when_sg_is_free _ (sg_side_is_surjective rest) f

/-- ⚑ **AND THE POLE THAT MAKES IT NOT A TAUTOLOGY.** Once `sg` is PINNED — which is what the
SRS-base leg does — the same relation refutes: at a fixed `sg₀` the check holds for exactly one
`f`. A vacuity theorem whose companion cannot go the other way would be saying nothing about the
discharge it is waiting for. -/
theorem pinned_sg_makes_the_opening_refute (rest sg₀ f : ℤ) (h : f ≠ sg₀ + rest) :
    ¬ openingAccepts f (fun s => s + rest) sg₀ := h

/-! ## §7 — THE HONEST WITNESS ROWS, generated here.

Rust fills cells; it does not author them. Each row is the corresponding sound module's own honest
witness re-based into the ALU layout, plus the selector that names the operation. The heavy
gate-satisfaction facts are NOT re-`decide`d here — they already exist at
`PastaFieldSound.fpHonest_satisfies_gates` and `PastaAddSubSound.fpAdd/fpSubHonest_satisfies_gates`,
and §3's `aluMulExpr_eval` / `aluAddSubExpr_eval` are the bridge from those bodies to these gates.
What IS proved here is the re-basing: that each row agrees with its source witness on the columns
the operation's gates read, and that every emitted cell is a canonical felt. The DEPLOYED polarity
— honest proves, forged refuses — is checked in Rust against `prove_vm_descriptor2`, which is the
only place it can be checked. -/

/-- The honest MULTIPLY row: `PastaFieldSound`'s witness verbatim in `0..189`, an unused add/sub
reduction block, and `SEL_MUL = 1`. -/
def aluMulRowAsg : Assignment := fun col =>
  if col < MUL_WIDTH then fpHonest col
  else if col = SEL_MUL then 1
  else 0

/-- The honest ADD row: `PastaAddSubSound`'s witness re-based — its `x/y/z` blocks already sit at
the ALU's, its carry BIT moves from `96` to `190` and its 31 carries from `97..127` to `191..221`.
The multiply's quotient block and 62 carries are unused and zero (which their own 8- and 16-bit
range lookups accept). -/
def aluAddRowAsg : Assignment := fun col =>
  if col < 3 * SK then fpAddHonest col
  else if col < ALU_AC_COL then 0
  else if col = ALU_AC_COL then fpAddHonest AC_COL
  else if col < SEL_MUL then fpAddHonest (ACAR_BASE + (col - ALU_ACAR_BASE))
  else if col = SEL_ADD then 1
  else 0

/-- The honest SUB row, with the BORROW set. -/
def aluSubRowAsg : Assignment := fun col =>
  if col < 3 * SK then fpSubHonest col
  else if col < ALU_AC_COL then 0
  else if col = ALU_AC_COL then fpSubHonest AC_COL
  else if col < SEL_MUL then fpSubHonest (ACAR_BASE + (col - ALU_ACAR_BASE))
  else if col = SEL_SUB then 1
  else 0

/-- ⚑ **THE RE-BASING IS AN IDENTITY ON THE COLUMNS THE MULTIPLY GATES READ.** Every column a
`coefExpr` touches is `< MUL_WIDTH = 190`, so the ALU multiply row and `fpHonest` are the same
assignment there — which is why `fpHonest_satisfies_gates` is a fact about THIS row and not about a
similar-looking one. -/
theorem aluMulRow_agrees_with_fpHonest (col : Nat) (h : col < MUL_WIDTH) :
    aluMulRowAsg col = fpHonest col := by
  unfold aluMulRowAsg; rw [if_pos h]

/-- …and the add row's operand blocks are `fpAddHonest`'s. -/
theorem aluAddRow_agrees_on_operands (col : Nat) (h : col < 3 * SK) :
    aluAddRowAsg col = fpAddHonest col := by
  unfold aluAddRowAsg; rw [if_pos h]

/-- …and its carry bit and carry chain are `fpAddHonest`'s, at the moved indices. -/
theorem aluAddRow_carry_bit : aluAddRowAsg ALU_AC_COL = fpAddHonest AC_COL := by
  unfold aluAddRowAsg; norm_num [ALU_AC_COL, SK, NG]

theorem aluAddRow_carry_at (i : Nat) (h : i < NA - 1) :
    aluAddRowAsg (ALU_ACAR_BASE + i) = fpAddHonest (ACAR_BASE + i) := by
  have hi : i < 31 := by rw [show NA - 1 = 31 from rfl] at h; exact h
  have hs : 3 * SK = 96 := rfl
  have h1 : ¬ (ALU_ACAR_BASE + i < 3 * SK) := by rw [ALU_ACAR_BASE_eq, hs]; omega
  have h2 : ¬ (ALU_ACAR_BASE + i < ALU_AC_COL) := by
    rw [ALU_ACAR_BASE_eq, ALU_AC_COL_eq]; omega
  have h3 : ¬ (ALU_ACAR_BASE + i = ALU_AC_COL) := by
    rw [ALU_ACAR_BASE_eq, ALU_AC_COL_eq]; omega
  have h4 : ALU_ACAR_BASE + i < SEL_MUL := by rw [ALU_ACAR_BASE_eq, SEL_MUL_eq]; omega
  unfold aluAddRowAsg
  rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4, Nat.add_sub_cancel_left]

/-- The three emitted rows. -/
def aluMulRow : List ℤ := (List.range ALU_WIDTH).map aluMulRowAsg
def aluAddRow : List ℤ := (List.range ALU_WIDTH).map aluAddRowAsg
def aluSubRow : List ℤ := (List.range ALU_WIDTH).map aluSubRowAsg

/-- ⚑ Every emitted cell is a CANONICAL BabyBear felt (`0 ≤ v < P`), so the Rust fixture parses as
`u32` and no cell is silently folded on the way in. -/
theorem aluMulRow_canonical : (aluMulRow.all fun v => decide (0 ≤ v ∧ v < P)) = true := by native_decide
theorem aluAddRow_canonical : (aluAddRow.all fun v => decide (0 ≤ v ∧ v < P)) = true := by native_decide
theorem aluSubRow_canonical : (aluSubRow.all fun v => decide (0 ≤ v ∧ v < P)) = true := by native_decide

/-- ⚑ **EXACTLY ONE OPERATION SELECTOR IS SET ON EACH ROW, AND THE CHAIN SELECTOR IS OFF.** The
selector-sum gate reads `1` on all three, so all three are gate-legal, and the chain leg is
satisfied vacuously — which is `unchained_transition_relates_nothing` made concrete: the emitted
three-row fixture is three UNRELATED operations, by construction. -/
theorem alu_rows_carry_one_selector_each :
    (aluMulRowAsg SEL_MUL, aluMulRowAsg SEL_ADD, aluMulRowAsg SEL_SUB, aluMulRowAsg SEL_CHAIN)
        = (1, 0, 0, 0)
      ∧ (aluAddRowAsg SEL_MUL, aluAddRowAsg SEL_ADD, aluAddRowAsg SEL_SUB, aluAddRowAsg SEL_CHAIN)
        = (0, 1, 0, 0)
      ∧ (aluSubRowAsg SEL_MUL, aluSubRowAsg SEL_ADD, aluSubRowAsg SEL_SUB, aluSubRowAsg SEL_CHAIN)
        = (0, 0, 1, 0) := by native_decide

theorem aluMulRow_length : aluMulRow.length = 226 := by
  unfold aluMulRow; simp [ALU_WIDTH_eq]

/-! ### §7b — a genuinely CHAINED pair, so the chain leg has an honest polarity too.

A falsifier alone proves a gate can refuse; it does not prove the gate is satisfiable. The pair
below is the positive side: row 0 multiplies `X · Y = Z`, sets `SEL_CHAIN = 1`, and row 1 adds
`Z + 0 = Z` — so row 1's `x` block IS row 0's `z` block, limb for limb, and the 32 chain legs hold
with the selector ON rather than vacuously. -/

/-- The multiply's result, as a natural: the value row 0 hands to row 1. -/
def CHAIN_Z : Nat := PastaField.Ref.fpMul PastaField.Ref.X PastaField.Ref.Y

/-- Row 0 of the chained pair: the honest multiply with the CHAIN selector on. -/
def aluChainRow0Asg : Assignment := fun col =>
  if col = SEL_CHAIN then 1 else aluMulRowAsg col

/-- Row 1 of the chained pair: the honest add `Z + 0 = Z` with carry `0`, whose `x` block is
row 0's `z` block. -/
def aluChainRow1Asg : Assignment := fun col =>
  let w : Assignment := adAsg CHAIN_Z 0 CHAIN_Z 0 pLimb 1 (-1)
  if col < 3 * SK then w col
  else if col < ALU_AC_COL then 0
  else if col = ALU_AC_COL then w AC_COL
  else if col < SEL_MUL then w (ACAR_BASE + (col - ALU_ACAR_BASE))
  else if col = SEL_ADD then 1
  else 0

def aluChainRow0 : List ℤ := (List.range ALU_WIDTH).map aluChainRow0Asg
def aluChainRow1 : List ℤ := (List.range ALU_WIDTH).map aluChainRow1Asg

/-- ⚑ **THE CHAIN LEG HOLDS WITH ITS SELECTOR ON.** Every one of the 32 chain bodies is EXACTLY
zero over ℤ on this pair — not zero because the selector is off, but because row 1's `x` limb
genuinely equals row 0's `z` limb. This is the honest polarity `chain_forces_limb_equality`
quantifies over. -/
theorem alu_chain_pair_satisfies_the_chain :
    ((List.range SK).all fun i => decide (chainBody aluChainRow0Asg aluChainRow1Asg i = 0))
      = true := by native_decide

/-- …and the selector really is ON, so the theorem above is not the vacuous case in disguise. -/
theorem alu_chain_pair_selector_is_on : aluChainRow0Asg SEL_CHAIN = 1 := by native_decide

theorem aluChainRow0_canonical :
    (aluChainRow0.all fun v => decide (0 ≤ v ∧ v < P)) = true := by native_decide
theorem aluChainRow1_canonical :
    (aluChainRow1.all fun v => decide (0 ≤ v ∧ v < P)) = true := by native_decide

#assert_compiled alu_chain_pair_satisfies_the_chain
#assert_compiled alu_chain_pair_selector_is_on
#assert_compiled aluChainRow0_canonical
#assert_compiled aluChainRow1_canonical

#assert_axioms aluMulRow_agrees_with_fpHonest
#assert_axioms aluAddRow_agrees_on_operands
#assert_axioms aluAddRow_carry_bit
#assert_axioms aluAddRow_carry_at
#assert_compiled aluMulRow_canonical
#assert_compiled aluAddRow_canonical
#assert_compiled aluSubRow_canonical
#assert_compiled alu_rows_carry_one_selector_each
#assert_axioms aluMulRow_length

#assert_axioms pastaAluAir_mainRailOk
#assert_axioms pastaAluAir_leg_shape
#assert_axioms aluMulExpr_eval
#assert_axioms aluAddSubExpr_eval
#assert_axioms alu_selector_is_boolean
#assert_axioms alu_mul_forces
#assert_axioms alu_mul_forces_fq
#assert_axioms alu_add_forces
#assert_axioms alu_sub_forces
#assert_axioms alu_selector_off_asserts_nothing
#assert_axioms chain_forces_limb_congruence
#assert_axioms chain_forces_limb_equality
#assert_axioms unchained_transition_relates_nothing
#assert_axioms inter_row_wiring_is_transition_only
-- ⚑ 2026-08-08: the round is 30 instructions, not 21. Welded to the emitted permutation in
-- `MinaWrapVerifierSponge` §8 so the census and the program cannot disagree again.
#assert_axioms rows_per_poseidon_round_eq
#assert_axioms rows_per_poseidon_perm_eq
#assert_compiled the_transcript_split_is_the_stage
#assert_compiled verifier_rows_eq
#assert_compiled xi_aggregate_dominates
#assert_compiled srs_leg_dwarfs_the_rest
-- ⚑ 2026-08-06, §5b: the price re-derived on the emitted sound rows.
#assert_compiled complete_adds_eq
#assert_compiled the_adds_are_the_censuss_msm_rows
#assert_compiled wrap_cells_eq
#assert_compiled the_row_count_was_never_the_wall
#assert_compiled the_atom_census_splits
#assert_compiled the_srs_leg_dwarfs_it_in_cells_too
#assert_compiled the_atom_widths_are_this_files_own
#assert_axioms opening_is_vacuous_when_sg_is_free
#assert_axioms sg_side_is_surjective
#assert_axioms opening_accepts_everything_while_sg_is_free
#assert_axioms pinned_sg_makes_the_opening_refute

/-! ## §7 — ⚑⚑ THE CHEAP MULTIPLY, ON THE ROW THAT CARRIES 588 732 OF THEM.

`§5`'s census is why this section exists: `WRAP_MULS = 588 732` is a `decide`d theorem and it does
NOT move — it is `WRAP_ADDSUBS` at `1 082 924` that moved when the Poseidon round was re-counted.
The ALU row spends **63 of its 386 constraints** and **2 269 of its per-row multiplication nodes**
on the multiply polarity, and `PastaSzMul` collapses exactly that block.

⚑ **THE SELECTOR SURVIVES THE SWAP, AND IT IS THE ONLY NEW ALGEBRA.** `aluMulExpr` is
`sMul · coefExpr m`; `aluSzBody` is `sMul · szBodyAt …`, the same multiplication by the same
selector column, over a `ChalExpr` instead of an `Expr`. Trace degree is unchanged at **3** — the
sz body is degree 2 in the trace and a challenge is DEGREE ZERO for quotient sizing
(`p3-air/src/symbolic/variable.rs:67-72`, `ExtEntry::Challenge => 0`), so the 32-deep Horner chains
cost nothing in the quotient and the row still sits exactly at `ir2_degree_budget = 3`.

⚑ **THE LAYOUT DOES NOT MOVE AT ALL.** `szBodyAt` is relocated to `X_BASE / Y_BASE / Z_BASE /
ALU_Q_BASE / ALU_C_BASE` — the SAME columns `alu_reuses_the_multiply_layout` pins — and it reads the
carry block OFFSET-DECODED at `COFF`, which is what `aluMulRow` already writes. So `ALU_WIDTH` is
still 226, the seven `limbs` legs are the same seven, the committed width is still 794, and **the
honest fixture rows of §4b are the honest fixture rows of both AIRs.**

⚠ **AND WHAT DOES NOT IMPROVE.** Columns, range lookups, committed width, trace height, LDE domain:
all identical. The win is the AIR's constraint count (`386 → 325`) and the prover's and verifier's
per-row evaluation arithmetic (`2 269 → 444` multiplication nodes in the multiply block). At the
wrap workload that is `1.04 × 10⁹` multiplication nodes removed
(`the_wrap_multiply_arithmetic_collapse`) and **zero committed cells**. Anyone selling this as a
trace-size fix is quoting the wrong currency.

⚠ **THE LEDGER RIDES ALONG, AND IT IS A HYPOTHESIS.** The sz polarity forces the congruence only at
a NON-EXCEPTIONAL draw, and `PastaSzMul.sz_single_challenge_is_below_the_bar` is a theorem that ONE
draw unions across this very census to `2^−98.5` — below the repo's ~124-bit bar. That is why
`pastaAluSzAir` carries TWO challenge gates and why the single-challenge form is not offered here.
The two-point form is `2^−197.0` (`sz_two_point_clears_the_bar`). That a drawn challenge is
non-exceptional is the one thing Schwartz–Zippel never discharges; the transcript ordering and the
per-context sampling that make the draw post-commitment are READ off pinned Plonky3 `82cfad7` and
cited, not modelled. -/

section SzAlu

open Dregg2.Circuit.DescriptorIR2
  (ChalExpr ChalConstraint challengeCount chalGateCount chalIndicesDistinctOk)
open Dregg2.Circuit.EffectAirIR (ChalLeg)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.OodQuotientConsistency (exceptionalSet)
open Dregg2.Circuit.Emit.PastaSzMul
  (CHAL_Z CHAL_Z2 szBodyAt szResidual szGate_holdsIn_forces_congruence chalMuls exprMuls
   schoolbookMuls)

/-- ⚑ **THE SELECTOR-GATED SCHWARTZ–ZIPPEL BODY at draw `zi`** — `sMul · szBodyAt` at the ALU row's
own bases. The multiplication by `SEL_MUL` is the only algebra this file adds to the certified
body, exactly as `aluMulExpr` was the only algebra it added to `coefExpr`. -/
def aluSzBody (pl : Nat → ℤ) (zi : Nat) : ChalExpr :=
  .mul (.loc SEL_MUL) (szBodyAt pl zi X_BASE Y_BASE Z_BASE ALU_Q_BASE ALU_C_BASE)

/-- The body's faithful `K`-denotation factors through the selector — the one step that turns a
gated gate into the ungated one `PastaSzMul` quantifies over. -/
theorem aluSzBody_evalIn {K : Type*} [CommRing K] (env : VmRowEnv) (z : Nat → K)
    (pl : Nat → ℤ) (zi : Nat) :
    (aluSzBody pl zi).evalIn env z
      = ((env.loc SEL_MUL : ℤ) : K)
        * (szBodyAt pl zi X_BASE Y_BASE Z_BASE ALU_Q_BASE ALU_C_BASE).evalIn env z := rfl

/-- ⚑ **THE SOURCE AIR OF ONE SCHWARTZ–ZIPPEL PASTA ALU ROW.** Leg for leg `pastaAluAir`, with the
63 multiply gates replaced by TWO challenge legs at two independent draws. Everything else — the 64
add/sub gates, the 4 booleanity gates, the selector-sum gate, the 32 chain windows, the 7 limb legs
— is the same object at the same index. -/
def pastaAluSzAir (pl : Nat → ℤ) : EffectAir :=
  { tables := [ mainTableDef ALU_WIDTH
              , ⟨rangeTidW SB, "range_w8", 1, .rangeLimb SB⟩
              , ⟨rangeTidW CB, "range_w16", 1, .rangeLimb CB⟩
              , ⟨rangeTidW CBITS, "range_w1", 1, .rangeLimb CBITS⟩ ]
  , legs :=
      [ AirLeg.chal ⟨.all, aluSzBody pl CHAL_Z⟩
      , AirLeg.chal ⟨.all, aluSzBody pl CHAL_Z2⟩ ]
      ++ (List.range NA).map
           (fun m => AirLeg.gate ⟨aluAddSubExpr SEL_ADD pl 1 (-1) m, .const 0⟩)
      ++ (List.range NA).map
           (fun m => AirLeg.gate ⟨aluAddSubExpr SEL_SUB pl (-1) 1 m, .const 0⟩)
      ++ [ AirLeg.gate ⟨boolExpr SEL_MUL, .const 0⟩
         , AirLeg.gate ⟨boolExpr SEL_ADD, .const 0⟩
         , AirLeg.gate ⟨boolExpr SEL_SUB, .const 0⟩
         , AirLeg.gate ⟨boolExpr SEL_CHAIN, .const 0⟩
         , AirLeg.gate ⟨selSumExpr, .const 0⟩ ]
      ++ (List.range SK).map (fun i => AirLeg.window ⟨RowSel.transition, chainWindowExpr i⟩)
      ++ [ AirLeg.limbs ⟨limbCols X_BASE, SB, rangeTidW SB⟩
         , AirLeg.limbs ⟨limbCols Y_BASE, SB, rangeTidW SB⟩
         , AirLeg.limbs ⟨limbCols Z_BASE, SB, rangeTidW SB⟩
         , AirLeg.limbs ⟨limbCols ALU_Q_BASE, SB, rangeTidW SB⟩
         , AirLeg.limbs ⟨aluCarryCols, CB, rangeTidW CB⟩
         , AirLeg.limbs ⟨[ALU_AC_COL], CBITS, rangeTidW CBITS⟩
         , AirLeg.limbs ⟨aluAcarCols, ACB, rangeTidW SB⟩ ] }

set_option maxHeartbeats 4000000 in
/-- ⚑ **The compiler ACCEPTS this block, and for the two challenge legs the verdict is real.**
`ChalLeg.mainRailOk` refuses `.first`/`.last` OUTRIGHT — the target's `chalGate` has no boundary
form — and refuses an `.all` body that reads `nxt`. Both new legs are `.all` over bodies that read
no `nxt`, so they lower to every-row `chalGate`s; the 32 window legs are still `.transition`. -/
theorem pastaAluSzAir_mainRailOk (pl : Nat → ℤ) : (pastaAluSzAir pl).mainRailOk = true := by
  unfold pastaAluSzAir EffectAir.mainRailOk
  simp only [List.all_append, List.all_map, Bool.and_eq_true, List.all_eq_true]
  repeat' apply And.intro
  all_goals first
    | decide
    | (intro m _; rfl)
    -- ⚑ The two challenge legs are a LITERAL list, not a `map`, so `List.all_eq_true` leaves a
    -- two-element bounded `∀` that `decide` will not close (the bodies carry the free limb vector
    -- `pl` under `.const`). Destructure it and check each leg's verdict.
    | (intro x hx
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
       rcases hx with rfl | rfl <;> rfl)

/-- ⚑ **THE LEG SHAPE: 110 legs, against `pastaAluAir`'s 171.** `2` challenge gates `+ 32` add
`+ 32` sub `+ 4` booleanity `+ 1` selector-sum `+ 32` chain windows `+ 7` limb legs. The 61 that
came off are the 63 coefficient gates minus the 2 that replace them; the seven limb legs still
carry `222` lookups between them, so the EMITTED constraint count is `110 − 7 + 222 = 325` against
`386`. ⚠ That byte figure is asserted in Rust against the emitted JSON, for the same reason
`pastaAluAir_leg_shape`'s is: kernel-reducing the assembled list did not terminate inside
`maxHeartbeats 4000000`, and the deployed parser checks it far more cheaply than the kernel. -/
theorem pastaAluSzAir_leg_shape (pl : Nat → ℤ) : (pastaAluSzAir pl).legs.length = 110 := by
  simp [pastaAluSzAir, NA, SK]

/-- The collapse against the row it replaces, on the two source objects. -/
theorem alu_sz_leg_collapse (pl : Nat → ℤ) :
    (pastaAluAir pl).legs.length = 171
      ∧ (pastaAluSzAir pl).legs.length = 110
      ∧ (pastaAluAir pl).legs.length - (pastaAluSzAir pl).legs.length = NG - 2 := by
  refine ⟨pastaAluAir_leg_shape pl, pastaAluSzAir_leg_shape pl, ?_⟩
  rw [pastaAluAir_leg_shape, pastaAluSzAir_leg_shape]
  decide

/-- ⚑ **THE TIE VERDICT ON THE SCHWARTZ–ZIPPEL ROW**, same argument as `pastaAluAir_pinsTied` and
same reason it is parametric: the collapse replaced 63 gate legs with two challenge legs and
published nothing new, so the block still carries no `.pin`. -/
theorem pastaAluSzAir_pinsTied (pl : Nat → ℤ) : (pastaAluSzAir pl).pinsTied = true := by
  unfold pastaAluSzAir EffectAir.pinsTied
  simp only [List.all_append, List.all_map, Bool.and_eq_true]
  repeat' apply And.intro
  all_goals rfl

def fpAluSzTiedAir : Dregg2.Circuit.Emit.EffectLower.TiedAir where
  air  := (pastaAluSzAir pLimb)
  ok   := pastaAluSzAir_mainRailOk pLimb
  tied := pastaAluSzAir_pinsTied pLimb

/-- ⚑ **THE `fp` SCHWARTZ–ZIPPEL ALU ROW** — the deployed atom of the transcript stage, at 325
constraints. -/
def fpAluSzDesc : EffectVmDescriptor2 :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-pasta-alu-sz::v1" ALU_WIDTH 0 [] fpAluSzTiedAir).val

theorem fpAluSzDesc_certified :
    Dregg2.Circuit.Emit.EffectLower.CertifiedRefines fpAluSzDesc [] (pastaAluSzAir pLimb) :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-pasta-alu-sz::v1" ALU_WIDTH 0 [] fpAluSzTiedAir).property

theorem fpAluSzDesc_eq_lowerAir :
    fpAluSzDesc = Dregg2.Circuit.Emit.EffectLower.lowerAir "dregg-pasta-alu-sz::v1" ALU_WIDTH 0 [] (pastaAluSzAir pLimb) := rfl

def fqAluSzTiedAir : Dregg2.Circuit.Emit.EffectLower.TiedAir where
  air  := (pastaAluSzAir qLimb)
  ok   := pastaAluSzAir_mainRailOk qLimb
  tied := pastaAluSzAir_pinsTied qLimb

def fqAluSzDesc : EffectVmDescriptor2 :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-pasta-alu-fq-sz::v1" ALU_WIDTH 0 [] fqAluSzTiedAir).val

theorem fqAluSzDesc_certified :
    Dregg2.Circuit.Emit.EffectLower.CertifiedRefines fqAluSzDesc [] (pastaAluSzAir qLimb) :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-pasta-alu-fq-sz::v1" ALU_WIDTH 0 [] fqAluSzTiedAir).property

theorem fqAluSzDesc_eq_lowerAir :
    fqAluSzDesc = Dregg2.Circuit.Emit.EffectLower.lowerAir "dregg-pasta-alu-fq-sz::v1" ALU_WIDTH 0 [] (pastaAluSzAir qLimb) := rfl

/-- ⚑ **THE WIDTH DOES NOT MOVE.** `226` declared before and after, so the committed `794` and the
LDE domain do not move either — the saving is entirely in the algebra. -/
theorem fpAluSzDesc_trace_width :
    fpAluSzDesc.traceWidth = 226 ∧ fpAluSzDesc.traceWidth = fpAluDesc.traceWidth := ⟨rfl, rfl⟩

/-! ### §7a — ⚑ WHAT AN SZ MULTIPLY ROW FORCES.

Same conclusion as `alu_mul_forces`, in the shape `PastaSzMul` proves it in: the hypothesis is
`ChalConstraint.holdsIn` — the `assert_zero_ext` denotation over an arbitrary `CommRing K`, which
the deployed prover instantiates at `BinomialExtensionField<BabyBear,4>` — and not `P ∣ body` over
the `2^31` base lane. Plus the disjunction, which is where the randomness lives. -/

/-- ⚑ **THE SELECTOR COMES OFF, and it is one line.** With `sMul = 1` the gated gate's faithful
denotation IS the ungated body's, so `PastaSzMul`'s theorems apply verbatim at the ALU's bases. -/
theorem alu_sz_gate_strips_the_selector {K : Type*} [CommRing K] (env : VmRowEnv) (z : Nat → K)
    (isLast : Bool) (pl : Nat → ℤ) (zi : Nat) (hsel : env.loc SEL_MUL = 1)
    (h : ChalConstraint.holdsIn env z isLast ⟨aluSzBody pl zi, false⟩) :
    ChalConstraint.holdsIn env z isLast
      ⟨szBodyAt pl zi X_BASE Y_BASE Z_BASE ALU_Q_BASE ALU_C_BASE, false⟩ := by
  have hv : (aluSzBody pl zi).evalIn env z = 0 := h
  rw [aluSzBody_evalIn, hsel, Int.cast_one, one_mul] at hv
  exact hv

/-- ⚑ **THE SZ MULTIPLY POLARITY.** The row's multiply selector is on, the seven emitted `limbs`
legs supply the ranges, BOTH emitted challenge gates hold at the drawn point, and EITHER draw is
non-exceptional. Conclusion: the Pasta congruence at the real Pallas-base prime — the same
conclusion `alu_mul_forces` reaches from 63 gates. -/
theorem alu_sz_mul_forces {K : Type*} [CommRing K] [IsDomain K] [DecidableEq K]
    [CharP K 2013265921]
    (env : VmRowEnv) (z : Nat → K) (isLast : Bool) (hsel : env.loc SEL_MUL = 1)
    (h1 : ChalConstraint.holdsIn env z isLast ⟨aluSzBody pLimb CHAL_Z, false⟩)
    (h2 : ChalConstraint.holdsIn env z isLast ⟨aluSzBody pLimb CHAL_Z2, false⟩)
    (hnonexc : z CHAL_Z ∉ exceptionalSet
        ((szResidual env.loc X_BASE Y_BASE Z_BASE ALU_Q_BASE ALU_C_BASE pLimb).map
          (Int.castRingHom K))
      ∨ z CHAL_Z2 ∉ exceptionalSet
        ((szResidual env.loc X_BASE Y_BASE Z_BASE ALU_Q_BASE ALU_C_BASE pLimb).map
          (Int.castRingHom K)))
    (hx : ∀ i, i < SK → 0 ≤ env.loc (X_BASE + i) ∧ env.loc (X_BASE + i) < 2 ^ SB)
    (hy : ∀ i, i < SK → 0 ≤ env.loc (Y_BASE + i) ∧ env.loc (Y_BASE + i) < 2 ^ SB)
    (hz : ∀ i, i < SK → 0 ≤ env.loc (Z_BASE + i) ∧ env.loc (Z_BASE + i) < 2 ^ SB)
    (hq : ∀ i, i < SK → 0 ≤ env.loc (ALU_Q_BASE + i) ∧ env.loc (ALU_Q_BASE + i) < 2 ^ SB)
    (hc : ∀ i, i < NG - 1 → 0 ≤ env.loc (ALU_C_BASE + i) ∧ env.loc (ALU_C_BASE + i) < 2 ^ CB) :
    (pN : ℤ) ∣ (sVal env.loc X_BASE * sVal env.loc Y_BASE - sVal env.loc Z_BASE) := by
  rcases hnonexc with h | h
  · exact szGate_holdsIn_forces_congruence env z isLast CHAL_Z X_BASE Y_BASE Z_BASE
      ALU_Q_BASE ALU_C_BASE pLimb (pN : ℤ)
      (alu_sz_gate_strips_the_selector env z isLast pLimb CHAL_Z hsel h1) h
      hx hy hz hq pLimb_bounds pLimb_recomposes hc
  · exact szGate_holdsIn_forces_congruence env z isLast CHAL_Z2 X_BASE Y_BASE Z_BASE
      ALU_Q_BASE ALU_C_BASE pLimb (pN : ℤ)
      (alu_sz_gate_strips_the_selector env z isLast pLimb CHAL_Z2 hsel h2) h
      hx hy hz hq pLimb_bounds pLimb_recomposes hc

/-- The same at the Vesta-base / Pallas-scalar modulus — both, because the accumulator leg is
Step/Tick on Vesta. -/
theorem alu_sz_mul_forces_fq {K : Type*} [CommRing K] [IsDomain K] [DecidableEq K]
    [CharP K 2013265921]
    (env : VmRowEnv) (z : Nat → K) (isLast : Bool) (hsel : env.loc SEL_MUL = 1)
    (h1 : ChalConstraint.holdsIn env z isLast ⟨aluSzBody qLimb CHAL_Z, false⟩)
    (h2 : ChalConstraint.holdsIn env z isLast ⟨aluSzBody qLimb CHAL_Z2, false⟩)
    (hnonexc : z CHAL_Z ∉ exceptionalSet
        ((szResidual env.loc X_BASE Y_BASE Z_BASE ALU_Q_BASE ALU_C_BASE qLimb).map
          (Int.castRingHom K))
      ∨ z CHAL_Z2 ∉ exceptionalSet
        ((szResidual env.loc X_BASE Y_BASE Z_BASE ALU_Q_BASE ALU_C_BASE qLimb).map
          (Int.castRingHom K)))
    (hx : ∀ i, i < SK → 0 ≤ env.loc (X_BASE + i) ∧ env.loc (X_BASE + i) < 2 ^ SB)
    (hy : ∀ i, i < SK → 0 ≤ env.loc (Y_BASE + i) ∧ env.loc (Y_BASE + i) < 2 ^ SB)
    (hz : ∀ i, i < SK → 0 ≤ env.loc (Z_BASE + i) ∧ env.loc (Z_BASE + i) < 2 ^ SB)
    (hq : ∀ i, i < SK → 0 ≤ env.loc (ALU_Q_BASE + i) ∧ env.loc (ALU_Q_BASE + i) < 2 ^ SB)
    (hc : ∀ i, i < NG - 1 → 0 ≤ env.loc (ALU_C_BASE + i) ∧ env.loc (ALU_C_BASE + i) < 2 ^ CB) :
    (qN : ℤ) ∣ (sVal env.loc X_BASE * sVal env.loc Y_BASE - sVal env.loc Z_BASE) := by
  rcases hnonexc with h | h
  · exact szGate_holdsIn_forces_congruence env z isLast CHAL_Z X_BASE Y_BASE Z_BASE
      ALU_Q_BASE ALU_C_BASE qLimb (qN : ℤ)
      (alu_sz_gate_strips_the_selector env z isLast qLimb CHAL_Z hsel h1) h
      hx hy hz hq qLimb_bounds qLimb_recomposes hc
  · exact szGate_holdsIn_forces_congruence env z isLast CHAL_Z2 X_BASE Y_BASE Z_BASE
      ALU_Q_BASE ALU_C_BASE qLimb (qN : ℤ)
      (alu_sz_gate_strips_the_selector env z isLast qLimb CHAL_Z2 hsel h2) h
      hx hy hz hq qLimb_bounds qLimb_recomposes hc

/-- ⚑ **AND THE OTHER POLARITY OF THE SELECTOR, for the challenge gate too.** At `sMul = 0` the
gated body is `0` in EVERY carrier at EVERY draw — so an add row's two challenge gates check
nothing, exactly as its 63 coefficient gates checked nothing before. Stated so that "325
constraints" is never read as "325 checks on every row". -/
theorem alu_sz_selector_off_asserts_nothing {K : Type*} [CommRing K] (env : VmRowEnv)
    (z : Nat → K) (pl : Nat → ℤ) (zi : Nat) (h : env.loc SEL_MUL = 0) :
    (aluSzBody pl zi).evalIn env z = 0 := by
  rw [aluSzBody_evalIn, h, Int.cast_zero, zero_mul]

/-! ### §7b — ⚑ THE PRICE, AT THIS FILE'S OWN CENSUS. -/

/-- Multiplication nodes in the SCHOOLBOOK multiply block of one ALU row: the 63 coefficient bodies
plus the 63 selector multiplications. -/
def ALU_SCHOOLBOOK_MULS : Nat := schoolbookMuls + NG

/-- …and in the two-point sz block: two 221-node bodies plus their two selector multiplications. -/
def ALU_SZ_MULS : Nat := 2 * 221 + 2

/-- ⚑ **`2 269 → 444` PER ROW, 5.11×, at the SAME trace degree.** -/
theorem alu_sz_arithmetic_collapse :
    ALU_SCHOOLBOOK_MULS = 2269
      ∧ ALU_SZ_MULS = 444
      ∧ chalMuls (aluSzBody pLimb CHAL_Z) + chalMuls (aluSzBody pLimb CHAL_Z2) = ALU_SZ_MULS
      ∧ 5 * ALU_SZ_MULS < ALU_SCHOOLBOOK_MULS ∧ ALU_SCHOOLBOOK_MULS < 6 * ALU_SZ_MULS := by
  -- `schoolbookMuls` is `decide`d ONCE, in `PastaSzMul`; the inequalities are rewritten through it
  -- rather than re-deciding a 63-body fold three more times.
  have hs : ALU_SCHOOLBOOK_MULS = 2269 := by
    unfold ALU_SCHOOLBOOK_MULS
    rw [Dregg2.Circuit.Emit.PastaSzMul.schoolbook_arithmetic_is_quadratic]
    decide
  exact ⟨hs, by decide, by decide, by rw [hs]; decide, by rw [hs]; decide⟩

/-- ⚑⚑ **THE WIN AT THE CENSUS, IN THE CURRENCY THAT MOVES.** Every one of `WRAP_MULS = 588 732`
foreign-field multiplies drops `2 206 → 442` multiplication nodes in its emitted body:
**`1 038 523 248` multiplication nodes removed** from the wrap verifier's per-row constraint
evaluation.

⚠ **AND ZERO COMMITTED CELLS.** `WRAP_CELLS = 161 308 368` does not move by one, because neither
`RCB_ROW_COLS` nor `ALU_ROW_COLS` moves — `PastaSzMul.width_and_lookups_unchanged` and
`PastaCurveSound.szRcbWidthIsUnchanged` are the two theorems that say so. The row count
(`WRAP_ROWS_SOUND = 279 016`) does not move either. This is the whole honest statement of the
saving: **evaluation arithmetic and recursion constraint count, not memory.** -/
theorem the_wrap_multiply_arithmetic_collapse :
    WRAP_MULS = 588732
      ∧ WRAP_MULS * (2206 - 442) = 1038523248
      ∧ WRAP_CELLS = 161308368
      ∧ WRAP_ROWS_SOUND = 279016 := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

set_option maxHeartbeats 8000000 in
/-- ⚑ **THE INDEPENDENCE LICENCE, DISCHARGED ON THE EMITTED ALU ROW** at `(CHAL_Z, CHAL_Z2) =
(0, 1)` — the `α` and `β` of the instance's first lookup context, the only pairing the MEASURED
sampler guarantees is two distinct post-commitment draws. A same-slot pairing across two contexts
is refused, and rightly: this row's 222 lookups are all range lookups and every one rides the one
byte bus, so a "distinct bus" criterion would be unsatisfiable here. -/
theorem fpAluSzDesc_chal_indices_distinct :
    chalIndicesDistinctOk fpAluSzDesc CHAL_Z CHAL_Z2 = true := by
  rw [fpAluSzDesc_eq_lowerAir]; decide

set_option maxHeartbeats 8000000 in
theorem fqAluSzDesc_chal_indices_distinct :
    chalIndicesDistinctOk fqAluSzDesc CHAL_Z CHAL_Z2 = true := by
  rw [fqAluSzDesc_eq_lowerAir]; decide

end SzAlu

#assert_axioms aluSzBody_evalIn
#assert_axioms pastaAluSzAir_mainRailOk
#assert_axioms pastaAluSzAir_leg_shape
#assert_axioms alu_sz_leg_collapse
#assert_axioms fpAluSzDesc_trace_width
#assert_axioms alu_sz_gate_strips_the_selector
#assert_axioms alu_sz_mul_forces
#assert_axioms alu_sz_mul_forces_fq
#assert_axioms alu_sz_selector_off_asserts_nothing
#assert_axioms alu_sz_arithmetic_collapse
#assert_compiled the_wrap_multiply_arithmetic_collapse
#assert_axioms fpAluSzDesc_chal_indices_distinct
#assert_axioms fqAluSzDesc_chal_indices_distinct

end Dregg2.Circuit.Emit.MinaWrapVerifierAir
