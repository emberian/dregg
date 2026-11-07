/-
# `Dregg2.Circuit.Emit.MinaPreambleLegsAir` — **FIVE PREAMBLE LEGS STOP BEING A DECISION THE
OBSERVER CALLS AND BECOME EMITTED POLYNOMIALS.**

⚑ SUBSTRATE, SAID OUT LOUD (House Law #1): this is a **Lean-authored AIR**. `preambleDesc` is
`EffectLower.lowerTiedAir` applied to the `EffectAir` source `preambleAir` (§3). There is **no
hand-written `VmConstraint2` in this file** and Rust authors nothing; Rust proves the artifact
(`circuit/tests/mina_preamble_legs_proves.rs`).

## ⚑⚑ THE STATE THIS MOVES, in the audit's own words

`docs/PICKLES-VERIFY-BLOCK-LEG-TABLE.md` §6, 2026-08-08: *"How many of upstream's legs does dregg
close BY CONSTRAINT? **Zero**, at every layer this table covers. No AIR row forces any leg of
`verify_block`."* The strongest closures were CODEC and CONSUMER REFUSAL — the node evaluates
compiled Lean (`picklesWrapShapeOk` → `dregg_mina_wrap_shape_ok`) and refuses the block. Real, on
the deployed path, and **not what "closed by constraint" means.**

This file renders the legs whose arithmetic is already proven in
`Circuit.Emit.PicklesVerifyPreamble` as one emitted descriptor, `dregg-mina-preamble-legs::v1`:

| leg | upstream | the emitted polynomial |
|---|---|---|
| **B1** `non_chunking` (wire max) | `verification.rs:628` | `MAXLEN·(MAXLEN−1) = 0` — the summary is a bit, and `maxPairLen_le_one_iff_nonChunking` proves the bit decides EXACTLY the list predicate |
| **B1** non-empty walk | `nonChunking_nil`'s vacuous accept | `PAIR_COUNT·PAIR_INV − 1 = 0` — zero has no inverse, so an empty walk has NO satisfying row |
| **B3** step domain ≤ 16 | `verification.rs:648-651` | `DOMAIN_LOG2 + Σ 2ⁱ·SBITᵢ − 16 = 0` with all bits boolean — a slack decomposition, so `> 16` has NO satisfying row over the canonical range |
| **C3** packing length | `prepared_statement.rs:179` | `PUB_LEN − 24 − N_CHAL = 0` — the produced length is COMPUTED from the challenge count, in-constraint |
| **D1a** prev-challenge count | `verifier.rs:810-815` | `PROOF_PREV − IDX_PREV = 0` |
| **D1b** public-input length | `verifier.rs:816-820` | `PUB_LEN − IDX_PUBLIC = 0` — ⚑ **the equality the vacuous `decide (0 < publicLen)` never was** |

⚑ **D1b is the marquee.** `KimchiVerify.shapeOkRec`'s public-input conjunct compared trusted
config against zero and could not fail (`the_old_public_conjunct_could_not_fail_on_this_path`);
`PicklesWrapShapeGate.the_old_gate_admits_a_public_input_it_should_refuse` exhibits the 41-word
index it accepted, and `MinaWrapVkDigestChain.the_index_digest_cannot_see_the_circuit_shape`
proves the VK digest cannot separate that pair either. The consumer-refusal repair
(`preambleLegsOk`, 2026-08-08) made the equality a compiled decision; **this file makes it a
polynomial**: `the_41_word_index_has_no_accepted_row` is that NO row of this AIR — not one forged
fixture, any row — carries `N_CHAL = 16` against `IDX_PUBLIC = 41`.

## ⚑ WHERE EACH FORCING LIVES — said per leg, because a theorem can be true about the wrong object

* **AIR** (this file): the RELATIONS. Booleanity, the three bit decompositions, the slack sum,
  the two equalities, the schedule sum, the inverse gate — every one an emitted constraint a
  prover cannot satisfy on a violating row, refused by the deployed constraint system with no
  producer pre-flight, no table, no lookup.
* **HOST** (stated, not hidden): the BINDING of the eight published slots to the real wire —
  `mina_pickles::WrapProofShape`'s `bulletproof_challenge_count` / `prev_eval_pairs` /
  `prev_eval_max_len` / `branch_domain_log2` and `MinaWrapIndexParams::DEVNET_BLOCKCHAIN`'s
  `public_len` / `prev_challenges`. Whoever verifies a proof of this descriptor supplies those
  eight numbers as the PI vector, exactly as the compiled gate is handed them today. Publication
  is what makes a future fold weld REACHABLE (`air_public_targets`), same as
  `MinaBodyPreimageBitsAir`'s 302 limbs; until that fold exists the slot-to-wire tie is the
  verifying host's.
* **SEAM**: none. No `proofBind` here — a `bound := none` bind emits ZERO polynomials over its
  commit lanes (`descriptor_ir2.rs:4017`) and a sibling is repairing that class; this file does
  not add another.

## ⚠ WHAT THIS DOES NOT MOVE

* **B2, D2 stay CODEC** — the wire admits no encoding of a violation. That closure is real and
  stronger than a runtime compare; rebuilding it here would be checking what the type forces.
* **C2's digest and C3's 40 word VALUES stay VALUE LAYER** — 16 Fq absorb links of the shape
  `MinaWrapVkDigestChain` runs at 28, undone work, not touched by this file.
* **The mod-`p` envelope**: the emitted gates force congruences at BabyBear (`PMOD`); the ℤ-level
  readings below are exact for canonical rows, which is what the deployed prover commits. Same
  envelope every descriptor in this tree carries (`EffectLowerCore.eq_of_modEq_canon`).

## Layout — ONE ROW, eight published slots, and the row is the preamble tuple

    col 0  PROOF_PREV   the proof's prev-challenge count        → PI 0
    col 1  IDX_PREV     the index's declared `prev_challenges`  → PI 1
    col 2  N_CHAL       `bulletproof_challenges.len()`          → PI 2
    col 3  PUB_LEN      the packing length `to_public_input` produces → PI 3
    col 4  IDX_PUBLIC   the index's declared `public`           → PI 4
    col 5  DOMAIN_LOG2  `branch_data.domain_log2`               → PI 5
    col 6  MAXLEN       max `prev_evals` pair length            → PI 6
    col 7  PAIR_COUNT   `prev_evals` pairs yielded              → PI 7
    col 8  PAIR_INV     witness: PAIR_COUNT⁻¹ mod p (unpublished)
    col 9..13   NBIT i  bits of N_CHAL       (5 → N_CHAL < 32)
    col 14..18  DBIT i  bits of DOMAIN_LOG2  (5 → DOMAIN_LOG2 < 32)
    col 19..23  SBIT i  bits of 16 − DOMAIN_LOG2 (the B3 slack)
    col 24..29  CBIT i  bits of PAIR_COUNT   (6 → PAIR_COUNT < 64)

## ⚑ COMMITTED WIDTH, RE-DERIVED FOR THIS SHAPE

These legs are field-only — booleanity, affine sums, one two-column product. **No curve ops**, so
neither the scheduled row's 4.60× leaf blow-up nor the 6.6× wrap figure applies; there is nothing
to inherit. NO table, NO range lookup (`preambleAir_has_no_lookups`), so `MainLayout::build`
appends no nibble aux block: **30 declared, 30 committed, 1.00×**
(`the_committed_width_is_the_declared_width`, re-derived from the emitted bytes in the Rust §0).

## ⚑ WHAT THIS BREAKS (flag day, stated so it is findable)

**2026-08-08 — A NEW DESCRIPTOR, `dregg-mina-preamble-legs::v1`.** Nothing existing changes
shape. It emits `circuit/descriptors/by-name/dregg-mina-preamble-legs-v1.json` and MINTS a VK for
it; no VK rotates, nothing re-genesises, and `PROVENANCE.json` gains no row that this file stamps
— the stamp is the operator's ceremony.

## Import line for the root: `import Dregg2.Circuit.Emit.MinaPreambleLegsAir`
-/
import Dregg2.Circuit.Emit.EffectLowerCertified
import Dregg2.Circuit.GateExpr
import Dregg2.Circuit.Emit.PicklesVerifyPreamble

namespace Dregg2.Circuit.Emit.MinaPreambleLegsAir

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg PiPinLeg WindowLeg PMOD)
open Dregg2.Circuit.TableAirIR (RowSel)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRow)
open Dregg2.Circuit.Emit.PicklesVerifyPreamble
  (toPublicInputLen PUBLIC_INPUT_FIXED_WORDS publicInputLenOk prevChallengesLenOk stepDomainOk
   BACKEND_TICK_ROUNDS_N nonChunking maxPairLen maxPairLen_le_one_iff_nonChunking)

set_option autoImplicit false
set_option maxRecDepth 20000

/-! ## §1 — the column layout and the PI slots. -/

def PROOF_PREV : Nat := 0
def IDX_PREV : Nat := 1
def N_CHAL : Nat := 2
def PUB_LEN : Nat := 3
def IDX_PUBLIC : Nat := 4
def DOMAIN_LOG2 : Nat := 5
def MAXLEN : Nat := 6
def PAIR_COUNT : Nat := 7
def PAIR_INV : Nat := 8
def NBIT (i : Nat) : Nat := 9 + i
def DBIT (i : Nat) : Nat := 14 + i
def SBIT (i : Nat) : Nat := 19 + i
def CBIT (i : Nat) : Nat := 24 + i

def PREAMBLE_WIDTH : Nat := 30
/-- The eight published slots — PI slot `s` is column `s`, by construction. -/
def PREAMBLE_PI_COUNT : Nat := 8

theorem the_layout_is_wellformed :
    CBIT 5 = PREAMBLE_WIDTH - 1
      ∧ PREAMBLE_PI_COUNT = PAIR_COUNT + 1
      ∧ NBIT 4 < DBIT 0 ∧ DBIT 4 < SBIT 0 ∧ SBIT 4 < CBIT 0 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩ <;> decide

/-! ## §2 — ⚑ THE TERM LISTS. One list per decomposition, shared VERBATIM between the emitted
legs (§3, through `termSum`) and the row predicate (§4, through `valOf`) — the mirroring is by
construction, not by agreement. -/

/-- `(coefficient, column)` terms of `N_CHAL`'s binary expansion, LSB first. -/
def nbitTerms : List (Nat × Nat) :=
  [(1, NBIT 0), (2, NBIT 1), (4, NBIT 2), (8, NBIT 3), (16, NBIT 4)]

def dbitTerms : List (Nat × Nat) :=
  [(1, DBIT 0), (2, DBIT 1), (4, DBIT 2), (8, DBIT 3), (16, DBIT 4)]

def sbitTerms : List (Nat × Nat) :=
  [(1, SBIT 0), (2, SBIT 1), (4, SBIT 2), (8, SBIT 3), (16, SBIT 4)]

def cbitTerms : List (Nat × Nat) :=
  [(1, CBIT 0), (2, CBIT 1), (4, CBIT 2), (8, CBIT 3), (16, CBIT 4), (32, CBIT 5)]

/-- Every boolean-gated column: the wire maximum and the three decompositions' bits plus the B3
slack bits. ⚠ `MAXLEN` is in this list because booleanity IS its leg — the bit is B1's bound. -/
def BOOL_COLS : List Nat :=
  [MAXLEN]
    ++ (nbitTerms ++ dbitTerms ++ sbitTerms ++ cbitTerms).map Prod.snd

theorem bool_cols_count : BOOL_COLS.length = 22 := rfl

/-! ## §3 — the SOURCE legs. Every one is a window gate; not one is a lookup. -/

open WindowExpr (loc)

/-- ⚑ **THE BOOLEANITY LEG** — `x·(x−1) = 0`, `GateExpr.gBool`'s five-node encoding, at `.all` so
a padding row is pinned too. On `MAXLEN` this IS leg B1: the wire summary is a bit, and
`maxPairLen_le_one_iff_nonChunking` is why a bit decides the upstream universal. -/
def boolLeg (c : Nat) : AirLeg :=
  .window ⟨RowSel.all, Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toWindow
    (Dregg2.Circuit.GateExpr.gBool (.leaf (.loc c)))⟩

theorem boolLeg_eq (c : Nat) :
    boolLeg c = .window ⟨RowSel.all, .mul (loc c) (.add (loc c) (.const (-1)))⟩ := rfl

/-- `Σ cᵢ · loc colᵢ`, right-folded — `MinaBodyPreimageBitsAir.termSum`'s shape. -/
def termSum : List (Nat × Nat) → WindowExpr
  | [] => .const 0
  | (c, col) :: rest => .add (.mul (.const (c : ℤ)) (loc col)) (termSum rest)

/-- A decomposition leg: `whole − Σ 2ⁱ·bitᵢ = 0`. -/
def decompLeg (whole : Nat) (ts : List (Nat × Nat)) : AirLeg :=
  .window ⟨RowSel.all, .add (loc whole) (.mul (.const (-1)) (termSum ts))⟩

/-- ⚑ **THE B3 LEG** — `DOMAIN_LOG2 + Σ 2ⁱ·SBITᵢ − 16 = 0`. With the slack bits boolean this is
`domain_log2 ≤ BACKEND_TICK_ROUNDS_N` as a POLYNOMIAL: a domain above 16 leaves the slack no
in-range value, so there is no satisfying row rather than a failed comparison. -/
def domainSlackLeg : AirLeg :=
  .window ⟨RowSel.all, .add (.add (loc DOMAIN_LOG2) (termSum sbitTerms)) (.const (-16))⟩

/-- ⚑ **THE C3 LEG** — `PUB_LEN − (24 + N_CHAL) = 0`: `to_public_input`'s produced length,
COMPUTED from the wire's challenge count in-constraint (`prepared_statement.rs:100-179`,
`toPublicInputLen`). -/
def pubLenScheduleLeg : AirLeg :=
  .window ⟨RowSel.all, .add (loc PUB_LEN) (.mul (.const (-1)) (.add (.const 24) (loc N_CHAL)))⟩

/-- ⚑⚑ **THE D1b LEG** — `PUB_LEN − IDX_PUBLIC = 0`, `verifier.rs:816-820`'s equality. The
polynomial the vacuous `decide (0 < publicLen)` never was. -/
def pubLenIndexLeg : AirLeg :=
  .window ⟨RowSel.all, .add (loc PUB_LEN) (.mul (.const (-1)) (loc IDX_PUBLIC))⟩

/-- **THE D1a LEG** — `PROOF_PREV − IDX_PREV = 0`, `verifier.rs:810-815`. -/
def prevAgreeLeg : AirLeg :=
  .window ⟨RowSel.all, .add (loc PROOF_PREV) (.mul (.const (-1)) (loc IDX_PREV))⟩

/-- ⚑ **THE NON-EMPTY-WALK LEG** — `PAIR_COUNT · PAIR_INV − 1 = 0`. Zero has no inverse in a
field, so the empty walk — which `nonChunking_nil` proves the upstream `all` accepts VACUOUSLY —
has no satisfying row. The one two-column product in this AIR. -/
def walkNonEmptyLeg : AirLeg :=
  .window ⟨RowSel.all, .add (.mul (loc PAIR_COUNT) (loc PAIR_INV)) (.const (-1))⟩

/-- The eight first-row PI pins: column `s` published at slot `s`. -/
def slotPin (s : Nat) : AirLeg := .pin ⟨VmRow.first, s, s⟩

/-- ⚑ **THE SOURCE.** Eight arithmetic legs, then 22 booleanity legs, then eight pins. -/
def preambleAir : EffectAir :=
  { tables := []
  , legs :=
      [ decompLeg N_CHAL nbitTerms
      , decompLeg DOMAIN_LOG2 dbitTerms
      , decompLeg PAIR_COUNT cbitTerms
      , domainSlackLeg
      , pubLenScheduleLeg
      , pubLenIndexLeg
      , prevAgreeLeg
      , walkNonEmptyLeg ]
        ++ (BOOL_COLS.map boolLeg)
        ++ ((List.range PREAMBLE_PI_COUNT).map slotPin) }

theorem preambleAir_leg_count : preambleAir.legs.length = 38 := by rfl

theorem preambleAir_mainRailOk : preambleAir.mainRailOk = true := by rfl

/-- ⚑ **EVERY PUBLISHED COLUMN IS DERIVED BY ANOTHER LEG** — `EffectAir.pinsTied`. `MAXLEN`'s tie
is its booleanity gate, which is not decoration: the gate IS leg B1.

⚑ Named so `preambleTiedAir` is handed both verdicts. Its fields are `autoParam`s defaulting to
`by decide`; a field left blank re-derives the verdict inside the elaborator's `whnf`. -/
theorem preambleAir_pinsTied : preambleAir.pinsTied = true := by rfl

theorem preambleAir_pinsFit : preambleAir.pinsFit PREAMBLE_PI_COUNT = true := by rfl

/-- ⚑ **NO LOOKUP, NO TABLE — the committed-width result, decided on the source.** No range table
means no refusal can hide in one: every refusal below is a NAMED window gate's. -/
theorem preambleAir_has_no_lookups :
    preambleAir.tables = [] ∧ preambleAir.ranges = []
      ∧ preambleAir.limbsCount = 0 ∧ preambleAir.totalRangeLookups = 0 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> rfl

/-- ⚑ **THE TIED SOURCE** — every published column is derived by another leg, carried in the
type. `MAXLEN`'s tie is its booleanity gate, which is not decoration: the gate IS leg B1. -/
def preambleTiedAir : Dregg2.Circuit.Emit.EffectLower.TiedAir where
  air  := preambleAir
  ok   := preambleAir_mainRailOk
  tied := preambleAir_pinsTied

/-- **`preambleDesc` — COMPILER OUTPUT.** -/
def preambleDesc : EffectVmDescriptor2 :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-mina-preamble-legs::v1" PREAMBLE_WIDTH PREAMBLE_PI_COUNT [] preambleTiedAir).val

/-- ⚑ **THE CERTIFICATE, produced by the emit**: any row window satisfying the emitted
descriptor's constraints satisfies every source leg's own claim — stated in the source's
vocabulary, so it is not `P → P`. -/
theorem preambleDesc_certified :
    Dregg2.Circuit.Emit.EffectLower.CertifiedRefines preambleDesc [] preambleAir :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-mina-preamble-legs::v1" PREAMBLE_WIDTH PREAMBLE_PI_COUNT [] preambleTiedAir).property

theorem preambleDesc_name : preambleDesc.name = "dregg-mina-preamble-legs::v1" := rfl
theorem preambleDesc_width : preambleDesc.traceWidth = 30 := rfl
theorem preambleDesc_piCount : preambleDesc.piCount = 8 := rfl
theorem preambleDesc_tables : preambleDesc.tables = [] := rfl
theorem preambleDesc_ranges : preambleDesc.ranges = [] := rfl
theorem preambleDesc_hashSites : preambleDesc.hashSites = [] := rfl
theorem preambleDesc_constraint_count : preambleDesc.constraints.length = 38 := rfl

/-- ⚑ **THE COMMITTED WIDTH IS THE DECLARED WIDTH.** No lookup constraint in the emitted bytes,
so `MainLayout::build` appends no nibble aux block: 30 declared, 30 committed, 1.00×. Re-derived
from `decomp_cols_pub` on the emitted bytes in `circuit/tests/mina_preamble_legs_proves.rs` §0. -/
theorem the_committed_width_is_the_declared_width :
    (preambleDesc.constraints.filter fun c =>
      match c with | .lookup _ => true | _ => false).length = 0
    ∧ preambleDesc.tables = []
    ∧ preambleDesc.traceWidth = 30 := by
  refine ⟨?_, rfl, rfl⟩
  rfl

/-! ## §4 — ⚑ THE ROW PREDICATE — the emitted constraint set's content, one field per leg
family, term lists shared with §3 verbatim.

⚠ `walkNonEmpty` is stated mod `PMOD` where every other field is ℤ: an inverse exists only in the
field, so the ℤ form would be UNSATISFIABLE and every polarity theorem below vacuous. The other
fields' ℤ readings are exact for canonical rows (the envelope named in the header). -/

/-- `Σ cᵢ · row colᵢ` — the value `termSum ts` denotes at a row. -/
def valOf (row : Nat → ℤ) (ts : List (Nat × Nat)) : ℤ :=
  ts.foldr (fun t acc => (t.1 : ℤ) * row t.2 + acc) 0

/-- ⚑ **`PreambleRowOk` — what the 38 emitted constraints say, as named conjuncts.** -/
structure PreambleRowOk (row pub : Nat → ℤ) : Prop where
  bits : ∀ c ∈ BOOL_COLS, row c * (row c - 1) = 0
  nchalDecomp : row N_CHAL = valOf row nbitTerms
  domainDecomp : row DOMAIN_LOG2 = valOf row dbitTerms
  pairDecomp : row PAIR_COUNT = valOf row cbitTerms
  domainSlack : row DOMAIN_LOG2 + valOf row sbitTerms = 16
  pubLenSchedule : row PUB_LEN = 24 + row N_CHAL
  pubLenIndex : row PUB_LEN = row IDX_PUBLIC
  prevAgree : row PROOF_PREV = row IDX_PREV
  walkNonEmpty : row PAIR_COUNT * row PAIR_INV ≡ 1 [ZMOD PMOD]
  published : ∀ s < PREAMBLE_PI_COUNT, pub s = row s

/-- A gated bit is 0 or 1 — with its two bounds, the form the sum arguments consume. -/
theorem bit_bounds {x : ℤ} (h : x * (x - 1) = 0) : (x = 0 ∨ x = 1) ∧ 0 ≤ x ∧ x ≤ 1 := by
  rcases mul_eq_zero.mp h with h0 | h1
  · exact ⟨Or.inl h0, by simp [h0], by simp [h0]⟩
  · have hx : x = 1 := by linarith
    exact ⟨Or.inr hx, by simp [hx], by simp [hx]⟩

/-! ## §5 — ⚑⚑⚑ THE FORCING THEOREMS: an accepted row satisfies the UPSTREAM leg, in
`PicklesVerifyPreamble`'s own vocabulary — the tie that keeps this AIR from being a paraphrase. -/

section Forcing
variable {row pub : Nat → ℤ}

/-- ⚑ **B3 IS FORCED.** Any accepted row's `DOMAIN_LOG2` is between 0 and 16 over ℤ — the slack
decomposition leaves a 17 nowhere to live — and `stepDomainOk` (the upstream decision,
`verification.rs:648-651`) accepts it. -/
theorem the_row_forces_the_step_domain_bound (h : PreambleRowOk row pub) :
    0 ≤ row DOMAIN_LOG2 ∧ row DOMAIN_LOG2 ≤ 16
      ∧ stepDomainOk (row DOMAIN_LOG2).toNat = true := by
  have hd0 := (bit_bounds (h.bits (DBIT 0) (by decide))).2
  have hd1 := (bit_bounds (h.bits (DBIT 1) (by decide))).2
  have hd2 := (bit_bounds (h.bits (DBIT 2) (by decide))).2
  have hd3 := (bit_bounds (h.bits (DBIT 3) (by decide))).2
  have hd4 := (bit_bounds (h.bits (DBIT 4) (by decide))).2
  have hs0 := (bit_bounds (h.bits (SBIT 0) (by decide))).2
  have hs1 := (bit_bounds (h.bits (SBIT 1) (by decide))).2
  have hs2 := (bit_bounds (h.bits (SBIT 2) (by decide))).2
  have hs3 := (bit_bounds (h.bits (SBIT 3) (by decide))).2
  have hs4 := (bit_bounds (h.bits (SBIT 4) (by decide))).2
  have hdval : valOf row dbitTerms
      = 1 * row (DBIT 0) + (2 * row (DBIT 1) + (4 * row (DBIT 2)
        + (8 * row (DBIT 3) + (16 * row (DBIT 4) + 0)))) := rfl
  have hsval : valOf row sbitTerms
      = 1 * row (SBIT 0) + (2 * row (SBIT 1) + (4 * row (SBIT 2)
        + (8 * row (SBIT 3) + (16 * row (SBIT 4) + 0)))) := rfl
  have hlow : 0 ≤ row DOMAIN_LOG2 := by
    rw [h.domainDecomp, hdval]
    linarith [hd0.1, hd1.1, hd2.1, hd3.1, hd4.1]
  have hslack : 0 ≤ valOf row sbitTerms := by
    rw [hsval]
    linarith [hs0.1, hs1.1, hs2.1, hs3.1, hs4.1]
  have hhigh : row DOMAIN_LOG2 ≤ 16 := by linarith [h.domainSlack]
  refine ⟨hlow, hhigh, ?_⟩
  unfold stepDomainOk
  refine decide_eq_true ?_
  show (row DOMAIN_LOG2).toNat ≤ 16
  omega

/-- ⚑⚑ **D1b + C3-LENGTH ARE FORCED.** Any accepted row's declared `public` IS the packing
length `to_public_input` produces from its challenge count — `publicInputLenOk (toPublicInputLen
nChal) idxPublic`, the equality `verifier.rs:816-820` checks and `decide (0 < publicLen)` never
did. The bit decomposition makes the ℤ reading exact: `N_CHAL < 32`, so no wraparound reading
exists. -/
theorem the_row_forces_the_public_length_equality (h : PreambleRowOk row pub) :
    row IDX_PUBLIC = 24 + row N_CHAL
      ∧ 0 ≤ row N_CHAL ∧ row N_CHAL ≤ 31
      ∧ publicInputLenOk (toPublicInputLen (row N_CHAL).toNat) (row IDX_PUBLIC).toNat = true := by
  have hn0 := (bit_bounds (h.bits (NBIT 0) (by decide))).2
  have hn1 := (bit_bounds (h.bits (NBIT 1) (by decide))).2
  have hn2 := (bit_bounds (h.bits (NBIT 2) (by decide))).2
  have hn3 := (bit_bounds (h.bits (NBIT 3) (by decide))).2
  have hn4 := (bit_bounds (h.bits (NBIT 4) (by decide))).2
  have hnval : valOf row nbitTerms
      = 1 * row (NBIT 0) + (2 * row (NBIT 1) + (4 * row (NBIT 2)
        + (8 * row (NBIT 3) + (16 * row (NBIT 4) + 0)))) := rfl
  have hlow : 0 ≤ row N_CHAL := by
    rw [h.nchalDecomp, hnval]
    linarith [hn0.1, hn1.1, hn2.1, hn3.1, hn4.1]
  have hhigh : row N_CHAL ≤ 31 := by
    rw [h.nchalDecomp, hnval]
    linarith [hn0.2, hn1.2, hn2.2, hn3.2, hn4.2]
  have heq : row IDX_PUBLIC = 24 + row N_CHAL := by
    rw [← h.pubLenIndex, h.pubLenSchedule]
  refine ⟨heq, hlow, hhigh, ?_⟩
  unfold publicInputLenOk
  refine decide_eq_true ?_
  show 24 + (row N_CHAL).toNat = (row IDX_PUBLIC).toNat
  omega

/-- **D1a IS FORCED.** `prevChallengesLenOk`, `verifier.rs:810-815`. -/
theorem the_row_forces_the_prev_challenge_equality (h : PreambleRowOk row pub) :
    prevChallengesLenOk (row PROOF_PREV).toNat (row IDX_PREV).toNat = true := by
  simp only [prevChallengesLenOk, decide_eq_true_eq, h.prevAgree]

/-- ⚑ **B1 IS FORCED.** Any accepted row's wire maximum is a bit, so ANY `prev_evals` walk whose
maximum it summarises satisfies upstream's `non_chunking` universal —
`maxPairLen_le_one_iff_nonChunking` is the reduction that makes the summary the list predicate
and not a number travelling beside it. -/
theorem the_row_forces_non_chunking (h : PreambleRowOk row pub) :
    (row MAXLEN = 0 ∨ row MAXLEN = 1)
      ∧ ∀ l : List (Nat × Nat), maxPairLen l = (row MAXLEN).toNat → nonChunking l = true := by
  have hb := bit_bounds (h.bits MAXLEN (by decide))
  refine ⟨hb.1, fun l hl => ?_⟩
  refine (maxPairLen_le_one_iff_nonChunking l).mp ?_
  rw [hl]
  rcases hb.1 with h0 | h1
  · simp [h0]
  · simp [h1]

/-- ⚑ **AND THE WALK IS NOT EMPTY.** `nonChunking_nil` proves the upstream `all` accepts an
empty walk vacuously; here zero has no inverse, so an accepted row's pair count is a NON-ZERO
value below 64. -/
theorem the_row_forces_a_nonempty_walk (h : PreambleRowOk row pub) :
    row PAIR_COUNT ≠ 0 ∧ 0 ≤ row PAIR_COUNT ∧ row PAIR_COUNT ≤ 63 := by
  have hc0 := (bit_bounds (h.bits (CBIT 0) (by decide))).2
  have hc1 := (bit_bounds (h.bits (CBIT 1) (by decide))).2
  have hc2 := (bit_bounds (h.bits (CBIT 2) (by decide))).2
  have hc3 := (bit_bounds (h.bits (CBIT 3) (by decide))).2
  have hc4 := (bit_bounds (h.bits (CBIT 4) (by decide))).2
  have hc5 := (bit_bounds (h.bits (CBIT 5) (by decide))).2
  have hcval : valOf row cbitTerms
      = 1 * row (CBIT 0) + (2 * row (CBIT 1) + (4 * row (CBIT 2)
        + (8 * row (CBIT 3) + (16 * row (CBIT 4) + (32 * row (CBIT 5) + 0))))) := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    have h01 : (0 : ℤ) ≡ 1 [ZMOD PMOD] := by
      have := h.walkNonEmpty
      rwa [h0, zero_mul] at this
    exact absurd h01 (by decide)
  · rw [h.pairDecomp, hcval]
    linarith [hc0.1, hc1.1, hc2.1, hc3.1, hc4.1, hc5.1]
  · rw [h.pairDecomp, hcval]
    linarith [hc0.2, hc1.2, hc2.2, hc3.2, hc4.2, hc5.2]

/-- ⚑⚑ **THE MARQUEE, AS A UNIVERSAL: THE 41-WORD INDEX HAS NO ACCEPTED ROW.** Not one forged
fixture — ANY row of this AIR carrying the real block's 16 challenges refuses an index declaring
41. This is the pair `the_index_digest_cannot_see_the_circuit_shape` proves the VK digest cannot
separate, separated by an emitted polynomial. -/
theorem the_41_word_index_has_no_accepted_row :
    ∀ row pub : Nat → ℤ, PreambleRowOk row pub →
      row N_CHAL = 16 → row IDX_PUBLIC ≠ 41 := by
  intro row pub h h16 h41
  have := (the_row_forces_the_public_length_equality h).1
  rw [h16, h41] at this
  norm_num at this

/-- ⚑ **AND A 17 DOMAIN HAS NO ACCEPTED ROW** — the whole-space form of B3's refusal. -/
theorem a_17_domain_has_no_accepted_row :
    ∀ row pub : Nat → ℤ, PreambleRowOk row pub → row DOMAIN_LOG2 ≠ 17 := by
  intro row pub h h17
  have := (the_row_forces_the_step_domain_bound h).2.1
  rw [h17] at this
  norm_num at this

end Forcing

/-! ## §6 — ⚑ THE REAL WIRE ROW, AND BOTH POLARITIES.

The honest row is the real devnet block 539508's preamble tuple as
`bridge/src/mina_pickles.rs` measures it on the wire (`decode_proof_at`'s asserts): 2
prev-challenges against an index declaring 2, 16 IPA challenges packing to 40 words against
`public = 40`, `domain_log2 = 16` (⚠ the BOUNDARY of B3 — a bound transcribed `< 16` refuses
every real Mina block), a 43-pair walk with maximum length 1. -/

def PAIR_INV_43 : ℤ := 468201377

/-- `43 · 468201377 = 20132659211 = 10 · PMOD + 1` — the inverse witness is real. -/
theorem the_inverse_witness_is_real : (43 : ℤ) * PAIR_INV_43 ≡ 1 [ZMOD PMOD] := by decide

/-- Columns 0..29 of the honest row. -/
def REAL_CELLS : List ℤ :=
  [2, 2, 16, 40, 40, 16, 1, 43, PAIR_INV_43,
   0, 0, 0, 0, 1,        -- NBIT: 16
   0, 0, 0, 0, 1,        -- DBIT: 16
   0, 0, 0, 0, 0,        -- SBIT: slack 0 (the boundary case)
   1, 1, 0, 1, 0, 1]     -- CBIT: 43

def realRow : Nat → ℤ := fun c => REAL_CELLS.getD c 0

def realPub : Nat → ℤ := fun s => if s < PREAMBLE_PI_COUNT then realRow s else 0

/-- ⚑⚑ **THE HONEST POLE: the real block's preamble tuple is ACCEPTED.** -/
theorem the_real_wire_row_is_accepted : PreambleRowOk realRow realPub := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ### The falsifiers. Every target carries a NON-ZERO honest value, every mutation MOVES it,
and every mutated value is a valid BabyBear element — and since this AIR has no range table, no
refusal below can be a lookup's; each is the named window gate's. Where a mutation must also move
a published slot or a decomposition bit to isolate the refusing gate, it does, and the theorem
says which gate is left refusing. -/

/-- The 41-word index: `IDX_PUBLIC` 40 → 41 in the row AND at its slot, everything else honest —
so the pin holds and the D1b equality gate is what refuses. -/
def forgedIdxRow : Nat → ℤ := fun c => if c = IDX_PUBLIC then 41 else realRow c
def forgedIdxPub : Nat → ℤ := fun s => if s = IDX_PUBLIC then 41 else realPub s

/-- A 17 step domain: `DOMAIN_LOG2` 16 → 17 with its decomposition bits moved to 17's
(`10001`) and its slot moved — so the decomposition and pin hold, and the SLACK gate (the bound
itself) is what refuses. -/
def forgedDomainRow : Nat → ℤ := fun c =>
  if c = DOMAIN_LOG2 then 17 else if c = DBIT 0 then 1 else realRow c
def forgedDomainPub : Nat → ℤ := fun s => if s = DOMAIN_LOG2 then 17 else realPub s

/-- A chunked walk summary: `MAXLEN` 1 → 2, slot moved — booleanity is what refuses. -/
def forgedMaxLenRow : Nat → ℤ := fun c => if c = MAXLEN then 2 else realRow c
def forgedMaxLenPub : Nat → ℤ := fun s => if s = MAXLEN then 2 else realPub s

/-- The empty walk: `PAIR_COUNT` 43 → 0 with its bits zeroed and its slot moved — the inverse
gate is what refuses, exactly where upstream's `all` accepts vacuously. -/
def forgedEmptyWalkRow : Nat → ℤ := fun c =>
  if c = PAIR_COUNT then 0
  else if c ∈ cbitTerms.map Prod.snd then 0
  else realRow c
def forgedEmptyWalkPub : Nat → ℤ := fun s => if s = PAIR_COUNT then 0 else realPub s

/-- A mismatched recursion count: `IDX_PREV` 2 → 1, slot moved — D1a is what refuses. -/
def forgedPrevRow : Nat → ℤ := fun c => if c = IDX_PREV then 1 else realRow c
def forgedPrevPub : Nat → ℤ := fun s => if s = IDX_PREV then 1 else realPub s

/-- One challenge short: `N_CHAL` 16 → 15 with its bits moved to 15's (`01111`) and its slot
moved — the C3 schedule gate refuses, because 24 + 15 = 39 ≠ 40. -/
def forgedNChalRow : Nat → ℤ := fun c =>
  if c = N_CHAL then 15
  else if c = NBIT 0 then 1 else if c = NBIT 1 then 1
  else if c = NBIT 2 then 1 else if c = NBIT 3 then 1 else if c = NBIT 4 then 0
  else realRow c
def forgedNChalPub : Nat → ℤ := fun s => if s = N_CHAL then 15 else realPub s

/-- ⚑ **THE FALSIFIERS FALSIFY**: every target non-zero honest, every mutation moves. -/
theorem the_falsifier_targets_are_non_zero_and_move :
    realRow IDX_PUBLIC = 40 ∧ forgedIdxRow IDX_PUBLIC = 41
    ∧ realRow DOMAIN_LOG2 = 16 ∧ forgedDomainRow DOMAIN_LOG2 = 17
    ∧ realRow MAXLEN = 1 ∧ forgedMaxLenRow MAXLEN = 2
    ∧ realRow PAIR_COUNT = 43 ∧ forgedEmptyWalkRow PAIR_COUNT = 0
    ∧ realRow IDX_PREV = 2 ∧ forgedPrevRow IDX_PREV = 1
    ∧ realRow N_CHAL = 16 ∧ forgedNChalRow N_CHAL = 15 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ⚑⚑ **THE 41-WORD INDEX IS REFUSED — by the D1b equality gate.** The forgery the old gate
waved through (`the_old_gate_admits_a_public_input_it_should_refuse`), refused by an emitted
polynomial. -/
theorem the_41_word_index_is_refused : ¬ PreambleRowOk forgedIdxRow forgedIdxPub := by
  intro h
  exact absurd h.pubLenIndex (by decide)

/-- ⚑ **A 17 DOMAIN IS REFUSED — by the slack gate**, its decomposition and pin intact. -/
theorem a_17_domain_is_refused : ¬ PreambleRowOk forgedDomainRow forgedDomainPub := by
  intro h
  exact absurd h.domainSlack (by decide)

/-- ⚑ **A CHUNKED WALK SUMMARY IS REFUSED — by booleanity on `MAXLEN`.** -/
theorem a_chunked_walk_summary_is_refused : ¬ PreambleRowOk forgedMaxLenRow forgedMaxLenPub := by
  intro h
  exact absurd (h.bits MAXLEN (by decide)) (by decide)

/-- ⚑ **THE EMPTY WALK IS REFUSED — by the inverse gate.** `0 · x ≡ 1` has no solution. -/
theorem an_empty_walk_is_refused : ¬ PreambleRowOk forgedEmptyWalkRow forgedEmptyWalkPub := by
  intro h
  have hbad := h.walkNonEmpty
  rw [show forgedEmptyWalkRow PAIR_COUNT = 0 from rfl, zero_mul] at hbad
  exact absurd hbad (by decide)

/-- **A MISMATCHED RECURSION COUNT IS REFUSED — by the D1a equality gate.** -/
theorem a_mismatched_recursion_count_is_refused : ¬ PreambleRowOk forgedPrevRow forgedPrevPub := by
  intro h
  exact absurd h.prevAgree (by decide)

/-- ⚑ **ONE CHALLENGE SHORT IS REFUSED — by the C3 schedule gate**: a 15-challenge packing
produces 39 words and the row still claims 40. -/
theorem one_challenge_short_is_refused : ¬ PreambleRowOk forgedNChalRow forgedNChalPub := by
  intro h
  exact absurd h.pubLenSchedule (by decide)

/-- ⚑ **BOTH POLARITIES, AS ONE STATEMENT.** -/
theorem preamble_legs_discriminate :
    PreambleRowOk realRow realPub
    ∧ ¬ PreambleRowOk forgedIdxRow forgedIdxPub
    ∧ ¬ PreambleRowOk forgedDomainRow forgedDomainPub
    ∧ ¬ PreambleRowOk forgedMaxLenRow forgedMaxLenPub
    ∧ ¬ PreambleRowOk forgedEmptyWalkRow forgedEmptyWalkPub
    ∧ ¬ PreambleRowOk forgedPrevRow forgedPrevPub
    ∧ ¬ PreambleRowOk forgedNChalRow forgedNChalPub :=
  ⟨the_real_wire_row_is_accepted, the_41_word_index_is_refused, a_17_domain_is_refused,
   a_chunked_walk_summary_is_refused, an_empty_walk_is_refused,
   a_mismatched_recursion_count_is_refused, one_challenge_short_is_refused⟩

/-! ## §7 — ⚠ RESIDUALS, NAMED.

1. ⚑⚑ **THE SLOT-TO-WIRE BINDING IS THE HOST'S.** The eight slots are PUBLISHED, which is what
   makes a weld reachable; until a fold `cb.connect`s them to the wire the observer decodes, the
   party that verifies a proof of this descriptor supplies the eight numbers — the same position
   `MinaBodyPreimageBitsAir`'s 302 limbs are in. **A prover chooses the tuple; this AIR says the
   tuple satisfies the five legs.** The compiled gate (`picklesWrapShapeOk`) keeps running on the
   deployed path unchanged; this descriptor is the same verdict as polynomials, for any consumer
   that will not run our process.
2. ⚠ **THE OTHER PREAMBLE CONJUNCTS.** `shapeOkRec`'s column/permutation counts, D3's
   `t_comm` bound, D4's chunk-size pin: still consumer refusal. B2/D2: CODEC, deliberately not
   rebuilt here. C2's digest, C3's 40 word values: value layer, undone.
3. ⚠ **THE MOD-`p` ENVELOPE.** The emitted gates are congruences at BabyBear; §5's ℤ readings
   are exact for canonical rows, which the deployed prover commits.
4. ⚠ **THE RECURSION BOUNDARY.** That a verifying STARK implies its statement is the FRI
   obligation this whole stack carries; this rung stands at that resolution.
-/

#assert_axioms the_layout_is_wellformed
#assert_axioms bool_cols_count
#assert_axioms boolLeg_eq
#assert_axioms preambleAir_leg_count
#assert_axioms preambleAir_mainRailOk
#assert_axioms preambleAir_pinsFit
#assert_axioms preambleAir_has_no_lookups
#assert_axioms preambleDesc_name
#assert_axioms preambleDesc_width
#assert_axioms preambleDesc_piCount
#assert_axioms preambleDesc_tables
#assert_axioms preambleDesc_ranges
#assert_axioms preambleDesc_hashSites
#assert_axioms preambleDesc_constraint_count
#assert_axioms the_committed_width_is_the_declared_width
#assert_axioms bit_bounds
#assert_axioms the_row_forces_the_step_domain_bound
#assert_axioms the_row_forces_the_public_length_equality
#assert_axioms the_row_forces_the_prev_challenge_equality
#assert_axioms the_row_forces_non_chunking
#assert_axioms the_row_forces_a_nonempty_walk
#assert_axioms the_41_word_index_has_no_accepted_row
#assert_axioms a_17_domain_has_no_accepted_row
#assert_axioms the_inverse_witness_is_real
#assert_axioms the_real_wire_row_is_accepted
#assert_axioms the_falsifier_targets_are_non_zero_and_move
#assert_axioms the_41_word_index_is_refused
#assert_axioms a_17_domain_is_refused
#assert_axioms a_chunked_walk_summary_is_refused
#assert_axioms an_empty_walk_is_refused
#assert_axioms a_mismatched_recursion_count_is_refused
#assert_axioms one_challenge_short_is_refused
#assert_axioms preamble_legs_discriminate

end Dregg2.Circuit.Emit.MinaPreambleLegsAir
