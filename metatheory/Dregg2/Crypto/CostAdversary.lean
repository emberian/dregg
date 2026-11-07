/-
# `Dregg2.Crypto.CostAdversary` — a COST MODEL that gives `Eff` in-logic content, at COST-VECTOR
resolution.

`FloorGames` §8 names the residual precisely and does NOT close it: the tree has no cost model, so the
adversary class `Eff` of `Hard G Eff := ∀ A, Eff A → Negl (gameAdv G A)` is a bare parameter. `§2`'s
`hard_top_iff_solvableFrac_negl` proves the escape is `Eff` and ONLY `Eff` — at `Eff := ⊤` the floor is
FALSE (a brute-force solver wins), at `Eff := ⊥` it is vacuous. The root cause (§8) is the adversary type:

    Adversary G := ∀ l, Inst l → Ans l

is a RAW FUNCTION carrying no cost, so no non-trivial `Eff` can even be *stated*. This is exactly the
EasyCrypt 2021 (eprint 2021/156) cost-model motivation — "an unbounded adversary's advantage is often 1,
so bounding resources is critical" — and FCF's (arXiv:1410.3735) reason for a `Comp` monad.

This module builds that cost model at the resolution EasyCrypt uses: **a cost VECTOR**, not a scalar.

  **§0 — COST IS A VECTOR: `⟨intr, qry⟩`.** EasyCrypt's judgement is `[intr : t_c, H.o : k_c]` — an
  *intrinsic* instruction count PLUS *per-abstract-procedure CALL COUNTS*. `Cost O` is exactly that:
  `intr : ℕ` (the adversary's OWN instructions) and `qry : O → ℕ` (how many times it calls each named
  oracle `o : O`). The old scalar is RECOVERED as a projection, `Cost.total = intr + ∑ o, qry o`, and
  more generally `Cost.billed oc = intr + ∑ o, qry o * oc o` prices the calls at whatever the oracle
  actually costs — `billed 1 = total`.

  ⚑ **THE ORACLE'S COST IS NOT THE ADVERSARY'S.** `cost` never mentions a price for answering a query:
  a `query` node contributes `⟨0, o ↦ 1⟩` — a CALL, no instructions. Who pays for running the oracle is
  the *environment's* business, and `billed_le_of_polyTime` is the theorem that composes the two: an
  adversary with poly `intr` and poly `qry`, against an oracle of per-call price `≤ B`, runs in poly
  total. `polyTime_iff_intr_and_queries` proves the vector is the object: `PolyTime` factors EXACTLY
  into "poly intrinsic work" ∧ "poly query counts" — and `queryHog` PROVES the two conjuncts are
  independent (an adversary with `l` instructions and `2^l` calls passes the first and fails the second),
  so the second component is load-bearing rather than decorative.

  **§1 — the cost-carrying adversary is a DEEP-EMBEDDED PROGRAM.** `FreeOracle O Q R α` is a small free
  monad / interaction tree over a FAMILY of oracles named by `O`, each with its own query type `Q o` and
  (finite) response type `R o`: `pure` (return), `tick` (one instruction), and `query o q k` (one call to
  oracle `o`, branching on the response).

  ⚑ **THE LOAD-BEARING CORRECTNESS RULE — cost is DERIVED FROM SYNTAX, never asserted.** `cost` is an
  instrumented interpreter of the PROGRAM: it counts `tick`s into `intr` and `query`s into `qry o`
  STRUCTURALLY. It is a function OF the program, not a field ON the structure. An asserted `cost := 0`
  field would re-admit brute force (the raw-function hole, one level up); here cost cannot be faked
  because the scan's `tick`s ARE in the syntax and `cost` sees all of them.

  ⚑ **AND THE ADVERSARY PAYS FOR WHAT IT WRITES.** `cost sz (.pure a) = ⟨sz a, 0⟩`: returning a value
  costs its SIZE under the game's encoding `sz`. This is what makes §3's overhead DERIVED rather than
  supplied — `maxOut_le_intr` then says *every value the program can return is no larger than its own
  intrinsic cost*, i.e. "a poly-time adversary writes poly-many bits" is a THEOREM here, not a wish.

  **SOUNDNESS OF THE WORST CASE.** Branching over responses is worst-cased (`Cost.supOver`), and
  `runCost_le_cost` PROVES that the vector upper-bounds the cost of every ACTUAL execution under every
  concrete oracle — component by component. `cost` can never undercount a run.

  **§2 — `PolyTime` and the two poles, PROVED.** `PolyTime sz A := ∃ C k, ∀ l i, (cost (sz l)
  (A.prog l i)).total ≤ C·lᵏ+C`. BOTH POLES are theorems at the tighter model:
    * `bruteForce_not_polyTime` (`Eff ≠ ⊤`): the enumeration adversary that scans a `2^l`-sized answer
      space has `cost.intr = 2^l + l`, super-polynomial — so the collapse witness of
      `hard_top_iff_solvableFrac_negl` is EXCLUDED at `Eff := PolyTime`. `bruteForce_solves` confirms it
      is a genuine solver (advantage `1` at `⊤`), so the exclusion is not vacuous.
    * `idAdv_polyTime` (`Eff ≠ ⊥`): the return adversary costs exactly the size of the answer it writes,
      so it is `PolyTime` whenever that answer is poly-size — and `idAdv_polyTime_expGame` exhibits the
      class INHABITED with NO hypothesis at all, at the very game the ⊤ pole uses.

  **§3 — `hclosed` (efficiency preservation) as a THEOREM, with the overhead DERIVED.**
  `cost_postMapProg_tight` is the EasyCrypt-shaped tight composition lemma

      cost (C[A]) ≤ cost A + δ,   δ = ⟨L.slope · (cost A).intr + L.base, L.qadd⟩

  with δ EXPLICIT — the reduction's own intrinsic cost (linear in the size of the value it is handed,
  which is bounded by `A`'s own cost) plus the calls IT adds, per oracle. `polyTime_postMapProg` then
  takes NO poly-overhead hypothesis: poly-ness of the overhead FOLLOWS from `PolyTime A` and the
  reduction's syntax. That is the honest successor to the old bare `hEff`, and to the earlier version of
  this module which took the overhead as a supplied `hov : PolyBoundedNat ov`.

  **§4 — CONNECTION to `FloorGames`.** `IsPolyTime sz : Adversary G → Prop` (a raw adversary is efficient
  iff SOME poly-time program denotes to it) makes `Hard G (IsPolyTime sz)` — e.g.
  `HashCRHardQuant F (IsPolyTime sz)` — a meaningful floor: `isPolyTime_inhabited` (non-vacuous),
  `bruteForce_not_polyTime` (proper restriction of ⊤). `isPolyTime_postMap` is the theorem the spine
  consumes to discharge `hEff` (`Market.WideCommitBoundary.stateCommit_binds_from_polyTime`), and it now
  asks for two NAT CONSTANTS (the reshaper's work, linear in input size) and a PROVED non-blow-up bound
  on the reshaper's output, instead of a floating `PolyBoundedNat ov`.

## ⚑ DESIGN COMMITMENTS THE LITERATURE DOES NOT SETTLE — stated, not silently taken.

1. **WORST-CASE, not expected.** Branching is `sup`-ed and the bound is `∀ l i`, so `PolyTime` is
   worst-case over instances and over oracle answers. Under an *expected*-PPT commitment (Feige, Goldreich–
   Levin's motivation) `sup` would become an average against the response distribution, `PolyTime` would
   be a strictly LARGER class, and `runCost_le_cost` would become "expectation ≤ bound" rather than a
   pointwise inequality. Nothing else in the module would change shape.
2. **UNIFORM, not non-uniform.** A `CostAdversary` is ONE program family `prog : ∀ l, Inst l → …`; there
   is no per-`l` advice string. Under a NON-uniform commitment the adversary would carry `advice : ∀ l,
   Advice l` with `size (advice l)` charged into `intr`, `PolyTime` would be a strictly larger class, and
   the ⊤-pole witness `bruteForce` would STILL be excluded (its work is `2^l` regardless of advice) while
   single-instance floors would collapse by hardcoding — the trap `CryptoFloorTeeth` §5 documents, which
   is why the λ-indexed instance space exists.
3. **DETERMINISTIC.** No coin tape; `gameAdv` is the counting probability over the instance space only.
   Randomised adversaries would add a `flip` node whose cost is `1` and whose branching is averaged, not
   `sup`-ed — i.e. commitment (1) again, one level down.
4. **THE SIZE MEASURE BELONGS TO THE GAME, NOT THE ADVERSARY.** `sz : ∀ l, G.Ans l → ℕ` is the encoding
   length of an answer. It is an argument of `PolyTime`, never a field of `CostAdversary`, precisely so
   an adversary cannot assert its own output is free — the same rule as cost. It is nevertheless a real
   modelling choice: a DEGENERATE `sz := 0` makes output free again and weakens §3's derivation back
   toward the supplied-overhead version. Consumers should instantiate it CONCRETELY (see
   `Market.WideCommitBoundary.stateAnsSize`/`wireAnsSize`/`hashAnsSize`), not leave it open.
5. **A REDUCTION'S OWN WORK IS DECLARED, because Lean functions have no runtime.** `isPolyTime_postMap`
   takes `cw bw : ℕ` — the reshaper costs `cw · (input size) + bw`. That number is not derivable from a
   Lean `fun`; what IS derived, and was not before, is (a) that the declared work is charged IN THE
   SYNTAX (`tickN`), (b) that it is LINEAR IN THE INPUT SIZE rather than a free polynomial in `l`, and
   (c) that the resulting overhead is poly — from `A`'s own bound, not from an assumption.

## Axiom hygiene

`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no fresh `axiom`, no
`native_decide`. `Classical.choice` enters only via `bruteForce`'s solver (the same witness `FloorGames`
§2 uses) and the non-vacuity default answer.
-/
import Dregg2.Crypto.FloorGames
import Dregg2.Crypto.ConcreteSecurity
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Crypto.CostAdversary

open Dregg2.Crypto.FloorGames
open Dregg2.Crypto.ConcreteSecurity (Negl PolyBoundedNat expBound expBound_not_ppt)

set_option autoImplicit false
set_option linter.dupNamespace false

/-! ## §0 — COST VECTORS: intrinsic work, and per-oracle CALL COUNTS. -/

/-- **A COST VECTOR over the oracle-name space `O`** — EasyCrypt's `[intr : t, o : k]`.

  * `intr` — the number of instructions the adversary itself executes (its `tick`s, plus the size of
    the value it writes out).
  * `qry o` — the number of CALLS it makes to the oracle named `o`. Not the oracle's cost: answering a
    query is the environment's expense, priced separately by `billed`.

Keeping these apart is the whole point of the vector. A scalar model cannot state "this reduction adds
`3` queries and `O(n)` instructions", which is exactly what a tight reduction must say. -/
structure Cost (O : Type) where
  /-- The adversary's OWN instruction count. -/
  intr : ℕ
  /-- The number of calls made to each named oracle. -/
  qry : O → ℕ

namespace Cost

variable {O : Type}

/-- Componentwise extensionality. -/
theorem ext' {c d : Cost O} (h1 : c.intr = d.intr) (h2 : ∀ o, c.qry o = d.qry o) : c = d := by
  cases c; cases d
  simp only [mk.injEq]
  exact ⟨h1, funext h2⟩

instance : Zero (Cost O) := ⟨⟨0, fun _ => 0⟩⟩
instance : Add (Cost O) := ⟨fun c d => ⟨c.intr + d.intr, fun o => c.qry o + d.qry o⟩⟩

/-- Costs are ordered COMPONENTWISE: no component may be undercounted. -/
instance : Preorder (Cost O) where
  le c d := c.intr ≤ d.intr ∧ ∀ o, c.qry o ≤ d.qry o
  le_refl _ := ⟨Nat.le_refl _, fun _ => Nat.le_refl _⟩
  le_trans _ _ _ h h' := ⟨Nat.le_trans h.1 h'.1, fun o => Nat.le_trans (h.2 o) (h'.2 o)⟩

@[simp] theorem zero_intr : (0 : Cost O).intr = 0 := rfl
@[simp] theorem zero_qry (o : O) : (0 : Cost O).qry o = 0 := rfl
@[simp] theorem add_intr (c d : Cost O) : (c + d).intr = c.intr + d.intr := rfl
@[simp] theorem add_qry (c d : Cost O) (o : O) : (c + d).qry o = c.qry o + d.qry o := rfl

theorem le_mk {c d : Cost O} (h1 : c.intr ≤ d.intr) (h2 : ∀ o, c.qry o ≤ d.qry o) : c ≤ d := ⟨h1, h2⟩
theorem le_intr {c d : Cost O} (h : c ≤ d) : c.intr ≤ d.intr := h.1
theorem le_qry {c d : Cost O} (h : c ≤ d) (o : O) : c.qry o ≤ d.qry o := h.2 o

theorem add_le_add {a b c d : Cost O} (h : a ≤ b) (h' : c ≤ d) : a + c ≤ b + d :=
  ⟨Nat.add_le_add h.1 h'.1, fun o => Nat.add_le_add (h.2 o) (h'.2 o)⟩

theorem add_assoc' (a b c : Cost O) : a + (b + c) = (a + b) + c :=
  ext' (by simp [Nat.add_assoc]) (by intro o; simp [Nat.add_assoc])

/-- **ONE INSTRUCTION.** -/
def tickC : Cost O := ⟨1, fun _ => 0⟩

/-- **ONE CALL to oracle `o`** — a call, and NO instructions. The oracle's own work is not the
adversary's cost. -/
def callC [DecidableEq O] (o : O) : Cost O := ⟨0, fun o' => if o' = o then 1 else 0⟩

@[simp] theorem tickC_intr : (tickC : Cost O).intr = 1 := rfl
@[simp] theorem tickC_qry (o : O) : (tickC : Cost O).qry o = 0 := rfl
@[simp] theorem callC_intr [DecidableEq O] (o : O) : (callC o).intr = 0 := rfl
@[simp] theorem callC_qry [DecidableEq O] (o o' : O) :
    (callC o).qry o' = if o' = o then 1 else 0 := rfl

/-- **WORST CASE over a finite branching**, componentwise. Each component is worst-cased on its own,
which is an UPPER bound on the true worst case of any single run (`runCost_le_cost`) and is what lets
"how many queries can this program make" be answered independently of "how much work does it do". -/
def supOver {ι : Type} [Fintype ι] (f : ι → Cost O) : Cost O :=
  ⟨Finset.univ.sup (fun i => (f i).intr), fun o => Finset.univ.sup (fun i => (f i).qry o)⟩

@[simp] theorem supOver_intr {ι : Type} [Fintype ι] (f : ι → Cost O) :
    (supOver f).intr = Finset.univ.sup (fun i => (f i).intr) := rfl

@[simp] theorem supOver_qry {ι : Type} [Fintype ι] (f : ι → Cost O) (o : O) :
    (supOver f).qry o = Finset.univ.sup (fun i => (f i).qry o) := rfl

theorem le_supOver {ι : Type} [Fintype ι] (f : ι → Cost O) (i : ι) : f i ≤ supOver f :=
  ⟨Finset.le_sup (f := fun j => (f j).intr) (Finset.mem_univ i),
   fun o => Finset.le_sup (f := fun j => (f j).qry o) (Finset.mem_univ i)⟩

theorem supOver_le {ι : Type} [Fintype ι] {f : ι → Cost O} {d : Cost O} (h : ∀ i, f i ≤ d) :
    supOver f ≤ d :=
  ⟨Finset.sup_le (fun i _ => (h i).1), fun o => Finset.sup_le (fun i _ => (h i).2 o)⟩

/-- Branchwise domination lifts through the worst case, with a shared additive slack. -/
theorem supOver_le_add {ι : Type} [Fintype ι] {f g : ι → Cost O} {d : Cost O}
    (h : ∀ i, f i ≤ g i + d) : supOver f ≤ supOver g + d :=
  supOver_le (fun i => (h i).trans (add_le_add (le_supOver g i) (le_refl d)))

/-- The worst case over a constant branching is that constant. -/
theorem supOver_const {ι : Type} [Fintype ι] [Nonempty ι] (c : Cost O) :
    supOver (fun _ : ι => c) = c :=
  ext' (by simp [supOver, Finset.sup_const Finset.univ_nonempty])
    (fun o => by simp [supOver, Finset.sup_const Finset.univ_nonempty])

/-! ### Pricing the vector: the scalar is a PROJECTION. -/

/-- **`billed oc c`** — the vector priced against a per-oracle cost `oc`: the adversary's own
instructions plus, for each oracle, its call count times what a call to that oracle costs. THE
SEPARATION MADE ARITHMETIC: `cost` produces the vector without knowing `oc`; the environment supplies
`oc`. -/
def billed [Fintype O] (oc : O → ℕ) (c : Cost O) : ℕ := c.intr + ∑ o, c.qry o * oc o

/-- **`total`** — the OLD SCALAR MODEL, recovered as the projection at unit oracle price. Every flat
"one step per query" statement is `billed (fun _ => 1)`. -/
def total [Fintype O] (c : Cost O) : ℕ := c.intr + ∑ o, c.qry o

@[simp] theorem billed_one [Fintype O] (c : Cost O) : billed (fun _ => 1) c = c.total := by
  simp [billed, total]

theorem total_mono [Fintype O] {c d : Cost O} (h : c ≤ d) : c.total ≤ d.total :=
  Nat.add_le_add h.1 (Finset.sum_le_sum (fun o _ => h.2 o))

theorem total_add [Fintype O] (c d : Cost O) : (c + d).total = c.total + d.total := by
  simp only [total, add_intr, add_qry, Finset.sum_add_distrib]
  omega

theorem intr_le_total [Fintype O] (c : Cost O) : c.intr ≤ c.total := Nat.le_add_right _ _

theorem qry_le_total [Fintype O] (c : Cost O) (o : O) : c.qry o ≤ c.total :=
  le_trans (Finset.single_le_sum (f := fun o => c.qry o) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ o)) (Nat.le_add_left _ _)

/-- The scalar is at most the intrinsic work plus `|O| · (largest query count)`; the converse direction
of `intr_le_total`/`qry_le_total`, and what makes `polyTime_iff_intr_and_queries` an `↔`. -/
theorem total_le [Fintype O] (c : Cost O) (a b : ℕ) (ha : c.intr ≤ a) (hb : ∀ o, c.qry o ≤ b) :
    c.total ≤ a + Fintype.card O * b := by
  have hsum : ∑ o, c.qry o ≤ Finset.univ.card • b :=
    Finset.sum_le_card_nsmul _ _ b (fun o _ => hb o)
  simp only [smul_eq_mul, Finset.card_univ] at hsum
  simp only [total]
  omega

/-- Pricing at `oc ≤ B` costs at most `B+1` times the unit-priced scalar. The composition of the
adversary's vector with the ORACLE's price, explicitly. -/
theorem billed_le [Fintype O] (oc : O → ℕ) (B : ℕ) (hB : ∀ o, oc o ≤ B) (c : Cost O) :
    billed oc c ≤ (B + 1) * c.total := by
  have hsum : ∑ o, c.qry o * oc o ≤ ∑ o, c.qry o * B :=
    Finset.sum_le_sum (fun o _ => Nat.mul_le_mul_left _ (hB o))
  have hmul : ∑ o, c.qry o * B = (∑ o, c.qry o) * B := by
    rw [Finset.sum_mul]
  simp only [billed, total]
  nlinarith [hsum, hmul, Nat.zero_le c.intr, Nat.zero_le (∑ o, c.qry o), Nat.zero_le B]

end Cost

/-- **AN EXPLICIT LINEAR OVERHEAD `δ`** — the shape a TIGHT reduction's own cost has: `slope` units of
work per unit of INPUT SIZE, `base` fixed units, and `qadd o` extra calls to oracle `o`. This is the `δ`
of `cost (C[A]) ≤ cost A + δ`; naming it keeps the composition lemma from degenerating into a blob. -/
structure LinCost (O : Type) where
  /-- Instructions per unit of input size. -/
  slope : ℕ
  /-- Fixed instructions. -/
  base : ℕ
  /-- Calls the reduction itself adds, per oracle. -/
  qadd : O → ℕ

namespace LinCost

variable {O : Type}

/-- The overhead vector at input size `n`. -/
def at' (L : LinCost O) (n : ℕ) : Cost O := ⟨L.slope * n + L.base, L.qadd⟩

@[simp] theorem at'_intr (L : LinCost O) (n : ℕ) : (L.at' n).intr = L.slope * n + L.base := rfl
@[simp] theorem at'_qry (L : LinCost O) (n : ℕ) (o : O) : (L.at' n).qry o = L.qadd o := rfl

theorem at'_mono (L : LinCost O) {m n : ℕ} (h : m ≤ n) : L.at' m ≤ L.at' n :=
  Cost.le_mk (Nat.add_le_add_right (Nat.mul_le_mul_left (k := L.slope) h) L.base)
    (fun _ => Nat.le_refl _)

theorem total_at' [Fintype O] (L : LinCost O) (n : ℕ) :
    (L.at' n).total = L.slope * n + L.base + ∑ o, L.qadd o := rfl

end LinCost

/-! ## §1 — the deep-embedded oracle program, and SYNTACTIC cost. -/

/-- **A COST-CARRYING ADVERSARY PROGRAM** — a small free monad / interaction tree over a FAMILY of
oracles named by `O`, where oracle `o` takes queries in `Q o` and returns responses in the (finite)
type `R o`.

  * `pure a` — return `a`. Costs the SIZE of `a` (you must write your answer down).
  * `tick k` — one instruction, then continue as `k`.
  * `query o q k` — one CALL to oracle `o` on `q`, branching on the response `r : R o` into `k r`.

The response-branching is what lets a real finder USE its query results; `R o` finite is what lets the
worst case over answers be a genuine `ℕ`. Naming oracles by `O` is what lets the cost vector carry
PER-ORACLE call counts, EasyCrypt-style, instead of one anonymous total. -/
inductive FreeOracle (O : Type) (Q R : O → Type) (α : Type) where
  /-- Return a value; costs its encoded size. -/
  | protected pure : α → FreeOracle O Q R α
  /-- One instruction of internal computation, then continue. -/
  | protected tick : FreeOracle O Q R α → FreeOracle O Q R α
  /-- One call to oracle `o` on `q`, continuing with the response. -/
  | protected query : (o : O) → Q o → (R o → FreeOracle O Q R α) → FreeOracle O Q R α

namespace FreeOracle

variable {O : Type} {Q R : O → Type} {α β : Type}

/-- **⚑ THE INSTRUMENTED INTERPRETER — cost is DERIVED FROM THE PROGRAM'S SYNTAX, as a VECTOR.**

  * `pure a ↦ ⟨sz a, 0⟩` — writing the answer costs its size, no calls.
  * `tick k ↦ ⟨1, 0⟩ + cost k` — one instruction, no calls.
  * `query o _ k ↦ ⟨0, o ↦ 1⟩ + sup_r cost (k r)` — ONE CALL to `o`, ZERO instructions, and the
    worst case over the oracle's possible answers of what the adversary does NEXT.

⚑ Read the third clause carefully: the adversary is charged for MAKING the call, never for the oracle's
work in answering it; the `sup` worst-cases only the adversary's OWN continuation. `runCost_le_cost`
proves the result upper-bounds every actual execution, so nothing is undercounted.

This is the load-bearing rule of the module: cost is a FUNCTION of `prog`, never a field on a structure.
A program that scans `n` answers has `n` `tick`s in its syntax, so `intr ≥ n` is forced — there is no
`cost := 0` to assert. -/
def cost [DecidableEq O] [∀ o, Fintype (R o)] (sz : α → ℕ) : FreeOracle O Q R α → Cost O
  | .pure a => ⟨sz a, fun _ => 0⟩
  | .tick k => Cost.tickC + cost sz k
  | .query o _ k => Cost.callC o + Cost.supOver (fun r => cost sz (k r))

variable [DecidableEq O] [∀ o, Fintype (R o)]

@[simp] theorem cost_pure (sz : α → ℕ) (a : α) :
    cost (Q := Q) (R := R) sz (.pure a) = ⟨sz a, fun _ => 0⟩ := rfl

@[simp] theorem cost_tick (sz : α → ℕ) (k : FreeOracle O Q R α) :
    cost sz (.tick k) = Cost.tickC + cost sz k := rfl

@[simp] theorem cost_query (sz : α → ℕ) (o : O) (q : Q o) (k : R o → FreeOracle O Q R α) :
    cost sz (.query o q k) = Cost.callC o + Cost.supOver (fun r => cost sz (k r)) := rfl

/-- **THE SCALAR MODEL, AS A PROJECTION.** `stepCost` is the old flat "one unit per instruction, one
per query" number — now definitionally `Cost.total` of the vector. Nothing about the scalar is lost;
what is gained is that the components can be spoken about separately. -/
def stepCost [Fintype O] (sz : α → ℕ) (m : FreeOracle O Q R α) : ℕ := (cost sz m).total

/-! ### What the program can RETURN, and why that is bounded by what it COSTS. -/

/-- **THE LARGEST VALUE THE PROGRAM CAN RETURN**, worst-cased over oracle answers. -/
def maxOut (sz : α → ℕ) : FreeOracle O Q R α → ℕ
  | .pure a => sz a
  | .tick k => maxOut sz k
  | .query _ _ k => Finset.univ.sup (fun r => maxOut sz (k r))

@[simp] theorem maxOut_pure (sz : α → ℕ) (a : α) :
    maxOut (Q := Q) (R := R) sz (.pure a) = sz a := rfl

@[simp] theorem maxOut_tick (sz : α → ℕ) (k : FreeOracle O Q R α) :
    maxOut sz (.tick k) = maxOut sz k := rfl

@[simp] theorem maxOut_query (sz : α → ℕ) (o : O) (q : Q o) (k : R o → FreeOracle O Q R α) :
    maxOut sz (.query o q k) = Finset.univ.sup (fun r => maxOut sz (k r)) := rfl

/-- **⚑ "A POLY-TIME ADVERSARY WRITES POLY-MANY BITS" — A THEOREM, NOT A WISH.** Whatever value the
program can return is no larger than its own intrinsic cost. This is the consequence of charging `sz a`
at the `pure` leaf, and it is the hinge that makes §3's reduction overhead DERIVED: the reduction's work
is linear in the size of the value it is handed, and that size is bounded by the adversary's own cost
bound. -/
theorem maxOut_le_intr (sz : α → ℕ) (m : FreeOracle O Q R α) :
    maxOut sz m ≤ (cost sz m).intr := by
  induction m with
  | pure a => simp
  | tick k ih => simp only [maxOut_tick, cost_tick, Cost.add_intr, Cost.tickC_intr]; omega
  | query o q k ih =>
      simp only [maxOut_query, cost_query, Cost.add_intr, Cost.callC_intr, Cost.supOver_intr,
        Nat.zero_add]
      exact Finset.sup_le (fun r _ =>
        le_trans (ih r) (Finset.le_sup (f := fun r => (cost sz (k r)).intr) (Finset.mem_univ r)))

/-! ### The ACTUAL run, and the soundness of the worst case. -/

/-- **THE COST OF ONE ACTUAL EXECUTION** under a concrete oracle implementation `orc`. No `sup`: the
oracle answers, and the program follows exactly one branch. -/
def runCost (orc : ∀ o, Q o → R o) (sz : α → ℕ) : FreeOracle O Q R α → Cost O
  | .pure a => ⟨sz a, fun _ => 0⟩
  | .tick k => Cost.tickC + runCost orc sz k
  | .query o q k => Cost.callC o + runCost orc sz (k (orc o q))

/-- **⚑ THE WORST CASE IS SOUND — COMPONENT BY COMPONENT.** Every actual execution, under every concrete
oracle, costs at most the syntactic vector: neither the instruction count nor ANY oracle's call count can
be undercounted by `cost`. This is what licenses reading `PolyTime` as a bound on real runs. -/
theorem runCost_le_cost (orc : ∀ o, Q o → R o) (sz : α → ℕ) (m : FreeOracle O Q R α) :
    runCost orc sz m ≤ cost sz m := by
  induction m with
  | pure a => exact le_refl _
  | tick k ih => exact Cost.add_le_add (le_refl _) ih
  | query o q k ih =>
      refine Cost.add_le_add (le_refl _) ?_
      exact (ih (orc o q)).trans (Cost.le_supOver (fun r => cost sz (k r)) (orc o q))

/-! ### Sequencing, straight-line work, and the per-oracle probe. -/

/-- **Monadic bind — graft `k` onto every leaf of `m`.** The derived sequencing; `tick`/`query`
structure is preserved and the continuation is spliced at each `pure` leaf. -/
def bind : FreeOracle O Q R α → (α → FreeOracle O Q R β) → FreeOracle O Q R β
  | .pure a, k => k a
  | .tick m, k => .tick (bind m k)
  | .query o q c, k => .query o q (fun r => bind (c r) k)

/-- **`n` instructions, then `m`.** Models a straight-line computation of declared length. -/
def tickN : ℕ → FreeOracle O Q R α → FreeOracle O Q R α
  | 0, m => m
  | n + 1, m => .tick (tickN n m)

@[simp] theorem cost_tickN (sz : α → ℕ) (n : ℕ) (m : FreeOracle O Q R α) :
    cost sz (tickN n m) = ⟨n, fun _ => 0⟩ + cost sz m := by
  induction n with
  | zero => exact (Cost.ext' (by simp [tickN]) (by intro o; simp [tickN]))
  | succ n ih =>
      refine Cost.ext' ?_ ?_
      · simp only [tickN, cost_tick, Cost.add_intr, Cost.tickC_intr, ih]; omega
      · intro o; simp only [tickN, cost_tick, Cost.add_qry, Cost.tickC_qry, ih]; omega

@[simp] theorem maxOut_tickN (sz : α → ℕ) (n : ℕ) (m : FreeOracle O Q R α) :
    maxOut sz (tickN n m) = maxOut sz m := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [tickN] using ih

/-- **A `query`-only probe of length `n` against ONE named oracle** — `n` calls to `o`, each ignoring
the response, then `pure a`. Its vector is `⟨sz a, o ↦ n⟩`: ZERO intrinsic instructions and EXACTLY `n`
calls to `o` and none to any other oracle. The demonstration that per-oracle call counting is real and
not decorative — a scalar model cannot state this. -/
def probe (o : O) (q : Q o) : ℕ → α → FreeOracle O Q R α
  | 0, a => .pure a
  | n + 1, a => .query o q (fun _ => probe o q n a)

@[simp] theorem cost_probe [∀ o, Nonempty (R o)] (sz : α → ℕ) (o : O) (q : Q o) (n : ℕ) (a : α) :
    cost (Q := Q) (R := R) sz (probe o q n a) = ⟨sz a, fun o' => if o' = o then n else 0⟩ := by
  induction n with
  | zero => exact Cost.ext' rfl (fun o' => by simp [probe])
  | succ n ih =>
      have hstep : cost (Q := Q) (R := R) sz (probe o q (n + 1) a)
          = Cost.callC o + (⟨sz a, fun o' => if o' = o then n else 0⟩ : Cost O) := by
        show Cost.callC o + Cost.supOver (fun _ : R o => cost sz (probe o q n a)) = _
        simp only [ih, Cost.supOver_const]
      rw [hstep]
      refine Cost.ext' (by simp) (fun o' => ?_)
      by_cases h : o' = o <;> simp [h] <;> omega

/-- **A STRAIGHT-LINE RESHAPER** — declare `w` instructions of work, then emit `out`. The concrete shape
every post-processing reduction has; its cost is `w` PLUS the size of what it writes, both derived from
this syntax. -/
def reshape (w : ℕ) (out : α) : FreeOracle O Q R α := tickN w (.pure out)

@[simp] theorem cost_reshape (sz : α → ℕ) (w : ℕ) (out : α) :
    cost (Q := Q) (R := R) sz (reshape w out) = ⟨w + sz out, fun _ => 0⟩ := by
  refine Cost.ext' ?_ ?_ <;> simp [reshape]

/-- A reshaper whose declared work and whose output are both linear in the INPUT size fits the explicit
overhead `δ` of the tight composition lemma. -/
theorem cost_reshape_le (sz : α → ℕ) (n w : ℕ) (out : α) (cw bw co bo : ℕ)
    (hw : w ≤ cw * n + bw) (ho : sz out ≤ co * n + bo) :
    cost (Q := Q) (R := R) sz (reshape w out)
      ≤ (LinCost.mk (cw + co) (bw + bo) (fun _ => 0)).at' n := by
  refine Cost.le_mk ?_ (fun o => ?_)
  · simp only [cost_reshape, LinCost.at'_intr]
    have : (cw + co) * n = cw * n + co * n := by ring
    omega
  · simp [LinCost.at']

/-- **⚑ BOUNDED-OVERHEAD COMPOSITION AT THE COST LEVEL, WITH `δ` EXPLICIT.** Grafting a continuation
whose cost is LINEAR IN THE SIZE OF THE VALUE IT IS HANDED raises the cost by exactly that linear
overhead, evaluated at the largest value `m` can produce. The engine of efficiency-preservation, and the
reason §3's overhead need not be assumed. -/
theorem cost_bind_le_lin (sz : α → ℕ) (sz' : β → ℕ) (L : LinCost O)
    (m : FreeOracle O Q R α) (k : α → FreeOracle O Q R β)
    (hk : ∀ a, cost sz' (k a) ≤ L.at' (sz a)) :
    cost sz' (bind m k) ≤ cost sz m + L.at' (maxOut sz m) := by
  induction m with
  | pure a =>
      refine Cost.le_mk ?_ (fun o => ?_)
      · have h := Cost.le_intr (hk a)
        simp only [bind, cost_pure, maxOut_pure, Cost.add_intr, LinCost.at'_intr] at h ⊢
        omega
      · have h := Cost.le_qry (hk a) o
        simp only [bind, cost_pure, maxOut_pure, Cost.add_qry, LinCost.at'_qry] at h ⊢
        omega
  | tick m ih =>
      refine Cost.le_mk ?_ (fun o => ?_)
      · have h := Cost.le_intr ih
        simp only [bind, cost_tick, maxOut_tick, Cost.add_intr, Cost.tickC_intr,
          LinCost.at'_intr] at h ⊢
        omega
      · have h := Cost.le_qry ih o
        simp only [bind, cost_tick, maxOut_tick, Cost.add_qry, Cost.tickC_qry,
          LinCost.at'_qry] at h ⊢
        omega
  | query o q c ih =>
      show Cost.callC o + Cost.supOver (fun r => cost sz' (bind (c r) k))
        ≤ (Cost.callC o + Cost.supOver (fun r => cost sz (c r)))
          + L.at' (Finset.univ.sup (fun r => maxOut sz (c r)))
      rw [← Cost.add_assoc']
      refine Cost.add_le_add (le_refl _) (Cost.supOver_le_add (fun r => ?_))
      refine (ih r).trans (Cost.add_le_add (le_refl _) (L.at'_mono ?_))
      exact Finset.le_sup (f := fun r => maxOut sz (c r)) (Finset.mem_univ r)

/-! ### Denotation — running the program under an oracle to recover the raw answer. -/

/-- **Run the program under an oracle implementation `orc`** to recover the plain value: `tick`/`query`
are erased, queries resolved by `orc`. This is the bridge back to `FloorGames.Adversary` (a raw
function). -/
def denote (orc : ∀ o, Q o → R o) : FreeOracle O Q R α → α
  | .pure a => a
  | .tick k => denote orc k
  | .query o q c => denote orc (c (orc o q))

@[simp] theorem denote_pure (orc : ∀ o, Q o → R o) (a : α) :
    denote (Q := Q) (R := R) orc (.pure a) = a := rfl

@[simp] theorem denote_tickN (orc : ∀ o, Q o → R o) (n : ℕ) (m : FreeOracle O Q R α) :
    denote orc (tickN n m) = denote orc m := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [tickN, denote] using ih

@[simp] theorem denote_reshape (orc : ∀ o, Q o → R o) (w : ℕ) (out : α) :
    denote (Q := Q) (R := R) orc (reshape w out) = out := by
  simp [reshape]

theorem denote_bind (orc : ∀ o, Q o → R o) (m : FreeOracle O Q R α) (k : α → FreeOracle O Q R β) :
    denote orc (bind m k) = denote orc (k (denote orc m)) := by
  induction m with
  | pure a => rfl
  | tick m ih => simpa [bind, denote] using ih
  | query o q c ih => simpa [bind, denote] using ih (orc o q)

/-- The size of the value an actual run returns is bounded by the worst-case output size, hence (by
`maxOut_le_intr`) by the program's own intrinsic cost. -/
theorem sz_denote_le_maxOut (orc : ∀ o, Q o → R o) (sz : α → ℕ) (m : FreeOracle O Q R α) :
    sz (denote orc m) ≤ maxOut sz m := by
  induction m with
  | pure a => exact Nat.le_refl _
  | tick k ih => simpa [denote] using ih
  | query o q k ih =>
      refine le_trans (ih (orc o q)) ?_
      exact Finset.le_sup (f := fun r => maxOut sz (k r)) (Finset.mem_univ (orc o q))

end FreeOracle

open FreeOracle

/-! ## §2 — the cost-carrying adversary, `PolyTime`, and BOTH POLES. -/

/-- **A COST ADVERSARY against `G`** — a deep-embedded program per instance, over the oracle family
named by `O`. Unlike `FloorGames.Adversary` (a raw `∀ l, Inst l → Ans l` carrying NO cost), this one has
a cost VECTOR derived from its syntax, so an efficiency class over it is meaningful.

⚑ There is EXACTLY ONE field. No cost, no query budget, no size measure is assertable here. -/
structure CostAdversary (G : Game) (O : Type) (Q R : O → Type) where
  /-- The adversary's PROGRAM on instance `i` at parameter `l`. -/
  prog : ∀ l, G.Inst l → FreeOracle O Q R (G.Ans l)

/-- **AN ANSWER-SIZE MEASURE for a game** — the encoding length of an answer. It belongs to the GAME
(design commitment 4 in the header): it is how many symbols the adversary must write to produce its
output, and it is NOT the adversary's to choose. -/
abbrev AnsSize (G : Game) : Type := ∀ l, G.Ans l → ℕ

variable {G G' G'' : Game} {O : Type} {Q R : O → Type}

/-- **`PolyTime sz A`** — the program's cost VECTOR, priced at unit oracle cost, is polynomially bounded
in the security parameter, uniformly over instances. Equivalently (`polyTime_iff_intr_and_queries`):
poly-many instructions AND poly-many calls to each oracle. Setting `Eff := PolyTime` is what §2's two
poles justify. -/
def PolyTime [Fintype O] [DecidableEq O] [∀ o, Fintype (R o)]
    (sz : AnsSize G) (A : CostAdversary G O Q R) : Prop :=
  ∃ C k : ℕ, ∀ l (i : G.Inst l), (cost (sz l) (A.prog l i)).total ≤ C * l ^ k + C

/-- The INTRINSIC half of `PolyTime` — the adversary's own instruction count is poly. -/
def PolyIntr [DecidableEq O] [∀ o, Fintype (R o)]
    (sz : AnsSize G) (A : CostAdversary G O Q R) : Prop :=
  ∃ C k : ℕ, ∀ l (i : G.Inst l), (cost (sz l) (A.prog l i)).intr ≤ C * l ^ k + C

/-- The QUERY half of `PolyTime` — the adversary makes poly-many calls to each named oracle. This is the
half a scalar cost model cannot state, and the half a tight reduction must track. -/
def PolyQueries [DecidableEq O] [∀ o, Fintype (R o)]
    (sz : AnsSize G) (A : CostAdversary G O Q R) : Prop :=
  ∃ C k : ℕ, ∀ l (i : G.Inst l) (o : O), (cost (sz l) (A.prog l i)).qry o ≤ C * l ^ k + C

/-- **`PolyBoundedNat` is closed under pointwise sum** (poly + poly = poly). The arithmetic core of
efficiency-preservation. -/
theorem polyBoundedNat_add {a b : ℕ → ℕ} (ha : PolyBoundedNat a) (hb : PolyBoundedNat b) :
    PolyBoundedNat (fun l => a l + b l) := by
  obtain ⟨k₁, C₁, ha⟩ := ha
  obtain ⟨k₂, C₂, hb⟩ := hb
  refine ⟨max k₁ k₂, 2 * (C₁ + C₂), fun l => ?_⟩
  show a l + b l ≤ 2 * (C₁ + C₂) * l ^ max k₁ k₂ + 2 * (C₁ + C₂)
  have hA := ha l
  have hB := hb l
  rcases Nat.eq_zero_or_pos l with hl | hl
  · subst hl
    have e1 : (0 : ℕ) ^ k₁ ≤ 1 := by rcases k₁ with _ | k₁ <;> simp
    have e2 : (0 : ℕ) ^ k₂ ≤ 1 := by rcases k₂ with _ | k₂ <;> simp
    have hc1 : C₁ * (0 : ℕ) ^ k₁ ≤ C₁ := by
      have h := Nat.mul_le_mul_left (k := C₁) e1
      simpa using h
    have hc2 : C₂ * (0 : ℕ) ^ k₂ ≤ C₂ := by
      have h := Nat.mul_le_mul_left (k := C₂) e2
      simpa using h
    have hM : 0 ≤ 2 * (C₁ + C₂) * (0 : ℕ) ^ max k₁ k₂ := Nat.zero_le _
    omega
  · have hkm : l ^ k₁ ≤ l ^ max k₁ k₂ := Nat.pow_le_pow_right hl (le_max_left k₁ k₂)
    have hk'm : l ^ k₂ ≤ l ^ max k₁ k₂ := Nat.pow_le_pow_right hl (le_max_right k₁ k₂)
    have h1 : C₁ * l ^ k₁ ≤ C₁ * l ^ max k₁ k₂ := by gcongr
    have h2 : C₂ * l ^ k₂ ≤ C₂ * l ^ max k₁ k₂ := by gcongr
    nlinarith [hA, hB, h1, h2, Nat.zero_le (l ^ max k₁ k₂), Nat.zero_le C₁, Nat.zero_le C₂]

/-- Constants are poly. -/
theorem polyBoundedNat_const (c : ℕ) : PolyBoundedNat (fun _ => c) :=
  ⟨0, c, fun _ => by simpa using Nat.le_add_left c c⟩

/-- Poly is closed under scaling by a constant. -/
theorem polyBoundedNat_const_mul (N : ℕ) {a : ℕ → ℕ} (ha : PolyBoundedNat a) :
    PolyBoundedNat (fun l => N * a l) := by
  obtain ⟨k, C, ha⟩ := ha
  refine ⟨k, N * C, fun l => ?_⟩
  have := ha l
  calc N * a l ≤ N * (C * l ^ k + C) := Nat.mul_le_mul_left _ this
    _ = N * C * l ^ k + N * C := by ring

/-- Poly is downward closed. -/
theorem polyBoundedNat_mono {a b : ℕ → ℕ} (h : ∀ l, a l ≤ b l) (hb : PolyBoundedNat b) :
    PolyBoundedNat a := by
  obtain ⟨k, C, hb⟩ := hb
  exact ⟨k, C, fun l => (h l).trans (hb l)⟩

variable [Fintype O] [DecidableEq O] [∀ o, Fintype (R o)]

/-- **⚑ THE VECTOR IS THE OBJECT.** `PolyTime` factors EXACTLY into its two components: poly intrinsic
work AND poly per-oracle query counts. The `→` direction is what a reduction consumes (it needs the query
count separately); the `←` direction is what makes the scalar an honest summary. -/
theorem polyTime_iff_intr_and_queries (sz : AnsSize G) (A : CostAdversary G O Q R) :
    PolyTime sz A ↔ (PolyIntr sz A ∧ PolyQueries sz A) := by
  constructor
  · rintro ⟨C, k, h⟩
    exact ⟨⟨C, k, fun l i => (Cost.intr_le_total _).trans (h l i)⟩,
           ⟨C, k, fun l i o => (Cost.qry_le_total _ o).trans (h l i)⟩⟩
  · rintro ⟨⟨C₁, k₁, h₁⟩, ⟨C₂, k₂, h₂⟩⟩
    have hpoly : PolyBoundedNat (fun l => (C₁ * l ^ k₁ + C₁)
        + Fintype.card O * (C₂ * l ^ k₂ + C₂)) :=
      polyBoundedNat_add ⟨k₁, C₁, fun _ => le_rfl⟩
        (polyBoundedNat_const_mul _ ⟨k₂, C₂, fun _ => le_rfl⟩)
    obtain ⟨k, C, hC⟩ := hpoly
    exact ⟨C, k, fun l i =>
      (Cost.total_le _ _ _ (h₁ l i) (fun o => h₂ l i o)).trans (hC l)⟩

/-- **⚑ THE ORACLE'S PRICE COMPOSES WITH THE ADVERSARY'S VECTOR, EXPLICITLY.** Charge each call to
oracle `o` whatever the oracle really costs (`oc o ≤ B`); a `PolyTime` adversary against a bounded-price
oracle still runs in poly TOTAL time. The adversary's own `cost` never mentions `oc` — that is the
separation this module's §0 buys, and this is the theorem that puts the two halves back together when a
total is wanted. -/
theorem billed_le_of_polyTime {sz : AnsSize G} {A : CostAdversary G O Q R} (hA : PolyTime sz A)
    (oc : O → ℕ) (B : ℕ) (hB : ∀ o, oc o ≤ B) :
    ∃ C k : ℕ, ∀ l (i : G.Inst l), Cost.billed oc (cost (sz l) (A.prog l i)) ≤ C * l ^ k + C := by
  obtain ⟨C, k, h⟩ := hA
  obtain ⟨k', C', hC'⟩ :=
    polyBoundedNat_const_mul (B + 1) (⟨k, C, fun _ => le_rfl⟩ : PolyBoundedNat _)
  exact ⟨C', k', fun l i =>
    ((Cost.billed_le oc B hB _).trans (Nat.mul_le_mul_left _ (h l i))).trans (hC' l)⟩

/-- **Denotation to a raw `FloorGames.Adversary`** — run each program under the trivial (default)
oracle. This is how a `CostAdversary` induces a member of the class the floor quantifies over. -/
def CostAdversary.toAdversary [∀ o, Inhabited (R o)] (A : CostAdversary G O Q R) : Adversary G where
  run := fun l i => denote (fun _ _ => default) (A.prog l i)

/-! ### The ⊥ pole — the class is INHABITED (not vacuous). -/

/-- **The return adversary** — outputs a fixed answer, does no computation. Under the tighter model it
is not FREE: it still pays for writing its answer. -/
def idAdv (a₀ : ∀ l, G.Inst l → G.Ans l) : CostAdversary G O Q R where
  prog := fun l i => .pure (a₀ l i)

/-- The return adversary's vector: the size of the answer, and NO oracle calls. -/
@[simp] theorem idAdv_cost (sz : AnsSize G) (a₀ : ∀ l, G.Inst l → G.Ans l) (l : ℕ) (i : G.Inst l) :
    cost (sz l) ((idAdv (O := O) (Q := Q) (R := R) a₀).prog l i) = ⟨sz l (a₀ l i), fun _ => 0⟩ := rfl

/-- **⚑ THE ⊥ POLE — `PolyTime` is INHABITED, so the floor at `Eff := PolyTime` is NOT vacuous.** The
return adversary is efficient exactly when the answer it writes is poly-size — the tighter model's
honest statement, since an adversary that emits an exponentially long string is NOT poly-time. Contrast
`FloorGames.hard_bot_vacuous`: at `Eff := ⊥` the class is empty and the floor holds for any game. -/
theorem idAdv_polyTime (sz : AnsSize G) (a₀ : ∀ l, G.Inst l → G.Ans l)
    (hsz : ∃ C k : ℕ, ∀ l (i : G.Inst l), sz l (a₀ l i) ≤ C * l ^ k + C) :
    PolyTime sz (idAdv (O := O) (Q := Q) (R := R) a₀) := by
  obtain ⟨C, k, h⟩ := hsz
  refine ⟨C, k, fun l i => ?_⟩
  simpa [Cost.total] using h l i

/-! ### The ⊤ pole — an EXPONENTIAL-search game and the brute-force enumerator that is NOT `PolyTime`. -/

/-- **A game with an exponential answer space.** One instance, `2^l` candidate answers, `wins` iff the
answer is the canonical winner `0` — so every instance is solvable (a brute-force scan finds `0`). The
minimal carrier on which "scanning the answer space" is super-polynomial. -/
def expGame : Game where
  Inst := fun _ => Unit
  Ans := fun l => Fin (2 ^ l)
  instFin := fun _ => inferInstance
  instNe := fun _ => inferInstance
  wins := fun l _ a => a = ⟨0, by positivity⟩
  winsDec := fun l _ a => inferInstance

/-- The canonical winning answer of `expGame` at parameter `l`. -/
def expWinner (l : ℕ) : Fin (2 ^ l) := ⟨0, by positivity⟩

/-- **THE HONEST ENCODING of an `expGame` answer** — an element of `Fin (2^l)` is `l` bits. Concrete,
not degenerate: writing an answer costs `l`, which is poly, so the ⊥ pole survives, while SCANNING the
`2^l` answers costs `2^l`, which does not. -/
def expSize : AnsSize expGame := fun l _ => l

/-- **THE BRUTE-FORCE ENUMERATOR.** Its PROGRAM scans all `2^l` answers (`2^l` instructions), then
returns the winner. Its cost is `2^l` BY CONSTRUCTION OF THE SYNTAX — there is no cost field to zero out.
This is the computable twin of `FloorGames.choiceAdv`, the witness that refutes the ⊤ floor. -/
def bruteForce : CostAdversary expGame Unit (fun _ => Unit) (fun _ => Unit) where
  prog := fun l _ => tickN (2 ^ l) (.pure (expWinner l))

/-- The brute-force enumerator's cost VECTOR: `2^l + l` instructions (the scan, plus writing the
answer), and ZERO oracle calls. -/
theorem bruteForce_cost (l : ℕ) (i : expGame.Inst l) :
    cost (expSize l) (bruteForce.prog l i) = ⟨2 ^ l + l, fun _ => 0⟩ := by
  refine Cost.ext' ?_ ?_ <;> simp [bruteForce, expSize,
    cost_pure (Q := fun _ : Unit => Unit) (R := fun _ => Unit) (expSize l) (expWinner l)]

/-- **⚑ THE ⊤ POLE — the brute-force solver is NOT `PolyTime`.** Its cost is `2^l + l`, which no
`C·lᵏ + C` bounds (`ConcreteSecurity.expBound_not_ppt`, exp dominates poly). So at `Eff := PolyTime` the
collapse witness of `FloorGames.hard_top_iff_solvableFrac_negl` — the enumeration solver — is EXCLUDED:
`Eff := PolyTime` is a PROPER restriction of `⊤`, and the ⊤-collapse does not refute the floor. -/
theorem bruteForce_not_polyTime : ¬ PolyTime expSize bruteForce := by
  rintro ⟨C, k, h⟩
  refine expBound_not_ppt ⟨k, C, fun l => ?_⟩
  have hl := h l ()
  rw [bruteForce_cost l ()] at hl
  simp only [Cost.total, Finset.univ_unique, Finset.sum_singleton] at hl
  simpa [expBound] using Nat.le_trans (Nat.le_add_right (2 ^ l) l) hl

/-- **THE BRUTE-FORCE ENUMERATOR GENUINELY SOLVES** `expGame` — it wins on every instance, so its
advantage is `1` and it WOULD refute the ⊤ floor. Hence its exclusion by `PolyTime` (above) is not
vacuous: a real solver is being kept out, exactly the one an unbounded class admits. -/
theorem bruteForce_solves (l : ℕ) (i : expGame.Inst l) :
    expGame.wins l i (bruteForce.toAdversary.run l i) := by
  show bruteForce.toAdversary.run l i = expWinner l
  simp [CostAdversary.toAdversary, bruteForce, FreeOracle.denote_tickN, FreeOracle.denote, expWinner]
  rfl

/-- **THE ⊥ POLE AT THE SAME GAME, WITH NO HYPOTHESIS.** The return adversary that outputs the winner
costs exactly `l` (the bits of its answer) — poly. So at the very game where the enumerator is excluded,
the class is inhabited. -/
theorem idAdv_polyTime_expGame :
    PolyTime expSize (idAdv (O := Unit) (Q := fun _ => Unit) (R := fun _ => Unit)
      (fun l _ => expWinner l)) :=
  idAdv_polyTime expSize _ ⟨1, 1, fun l _ => by simp [expSize]⟩

/-- **The ⊤ floor over `expGame` is FALSE** (every instance solvable — `FloorGames`
`not_hard_top_of_always_solvable`). This is the floor that `PolyTime` rescues by excluding
`bruteForce`. -/
theorem expGame_top_false : ¬ Hard expGame (fun _ => True) :=
  not_hard_top_of_always_solvable expGame (fun _ => ⟨expWinner _⟩)
    (fun l _ => ⟨expWinner l, rfl⟩)

/-- **⚑ NON-COLLAPSE.** `PolyTime` is strictly between `⊥` and `⊤` at the SAME game and the SAME
(concrete, non-degenerate) size measure: the brute-force enumerator is excluded, the return adversary is
admitted. Exactly the content `FloorGames` §8 said the tree could not supply. -/
theorem polyTime_proper :
    (∃ A : CostAdversary expGame Unit (fun _ => Unit) (fun _ => Unit), ¬ PolyTime expSize A)
      ∧ (∃ A : CostAdversary expGame Unit (fun _ => Unit) (fun _ => Unit), PolyTime expSize A) :=
  ⟨⟨bruteForce, bruteForce_not_polyTime⟩,
   ⟨idAdv (fun l _ => expWinner l), idAdv_polyTime_expGame⟩⟩

/-! ### THE TWO COMPONENTS ARE INDEPENDENT — why the vector is not decorative. -/

/-- **A QUERY-HUNGRY ADVERSARY** — it does NO internal computation beyond writing its answer, and makes
`2^l` oracle calls. The witness that "intrinsic work" and "query count" are genuinely different
resources. -/
def queryHog : CostAdversary expGame Unit (fun _ => Unit) (fun _ => Unit) where
  prog := fun l _ => probe () () (2 ^ l) (expWinner l)

/-- Its vector: `l` instructions (just writing the answer), and `2^l` calls. -/
theorem queryHog_cost (l : ℕ) (i : expGame.Inst l) :
    cost (expSize l) (queryHog.prog l i) = ⟨l, fun _ => 2 ^ l⟩ := by
  refine Cost.ext' ?_ (fun o => ?_) <;> simp [queryHog, expSize,
    cost_probe (Q := fun _ : Unit => Unit) (R := fun _ => Unit) (expSize l) () () (2 ^ l)
      (expWinner l)]

/-- **⚑ THE INTRINSIC COMPONENT ALONE IS NOT ENOUGH.** The query hog's own instruction count is poly …
-/
theorem queryHog_polyIntr : PolyIntr expSize queryHog :=
  ⟨1, 1, fun l i => by rw [queryHog_cost l i]; simp⟩

/-- … yet its CALL COUNT is exponential, so it is not efficient. A scalar cost model that folded the
call into the instruction count could not tell these two failures apart — and a reduction that must
report "I add three queries" could not be stated at all. -/
theorem queryHog_not_polyQueries : ¬ PolyQueries expSize queryHog := by
  rintro ⟨C, k, h⟩
  refine expBound_not_ppt ⟨k, C, fun l => ?_⟩
  have hl := h l () ()
  rw [queryHog_cost l ()] at hl
  simpa [expBound] using hl

/-- Hence `PolyIntr` is STRICTLY weaker than `PolyTime`: the query hog passes the first and fails the
second. `polyTime_iff_intr_and_queries` says the missing conjunct is exactly the query counts. -/
theorem queryHog_not_polyTime : ¬ PolyTime expSize queryHog :=
  fun h => queryHog_not_polyQueries ((polyTime_iff_intr_and_queries expSize queryHog).mp h).2

/-! ## §3 — TIGHT COMPOSITION, and `hclosed` with the overhead DERIVED. -/

/-- **THE POST-PROCESSING WRAPPER at the cost level, as a PROGRAM.** The reduction `red` is itself a
`FreeOracle` program — so its cost is DERIVED from its syntax, not supplied as a number. The instance
families of the two games agree (`hI`, `rfl` at every use site of the spine). -/
def CostAdversary.postMapProg (hI : ∀ l, G'.Inst l = G.Inst l)
    (red : ∀ l, G.Inst l → G.Ans l → FreeOracle O Q R (G'.Ans l))
    (A : CostAdversary G O Q R) : CostAdversary G' O Q R where
  prog := fun l i => bind (A.prog l (hI l ▸ i)) (red l (hI l ▸ i))

/-- **⚑ THE TIGHT COMPOSITION LEMMA — `cost (C[A]) ≤ cost A + δ`, with `δ` EXPLICIT.**

Given a reduction whose own cost is linear in the size of the value it is handed (`L`), the composed
adversary costs at most the original PLUS

    δ = ⟨ L.slope · (cost A).intr + L.base , L.qadd ⟩

— the reduction's own intrinsic work (linear in `A`'s output size, which `maxOut_le_intr` bounds by
`A`'s own intrinsic cost) plus, PER ORACLE, exactly the calls the reduction adds. Not a blob: every
component of `δ` is a named quantity of the reduction. This is what lets reductions compose without
slack accumulating — chaining two reductions adds `δ₁ + δ₂`, and the query counts add per oracle. -/
theorem cost_postMapProg_tight (hI : ∀ l, G'.Inst l = G.Inst l)
    (red : ∀ l, G.Inst l → G.Ans l → FreeOracle O Q R (G'.Ans l))
    (sz : AnsSize G) (sz' : AnsSize G') (L : LinCost O)
    (hred : ∀ l (i : G.Inst l) (a : G.Ans l), cost (sz' l) (red l i a) ≤ L.at' (sz l a))
    (A : CostAdversary G O Q R) (l : ℕ) (i : G'.Inst l) :
    cost (sz' l) ((A.postMapProg hI red).prog l i)
      ≤ cost (sz l) (A.prog l (hI l ▸ i))
        + L.at' (cost (sz l) (A.prog l (hI l ▸ i))).intr :=
  (cost_bind_le_lin (sz l) (sz' l) L _ _ (hred l (hI l ▸ i))).trans
    (Cost.add_le_add (le_refl _) (L.at'_mono (maxOut_le_intr (sz l) _)))

/-- **⚑ `hclosed` — EFFICIENCY IS PRESERVED, AND THE OVERHEAD IS DERIVED.** If `A` is `PolyTime` and the
reduction's cost is linear in the size of the value it is handed, the composed adversary is `PolyTime`.

⚑ There is NO `hov : PolyBoundedNat ov` hypothesis. The overhead's poly-ness is a CONSEQUENCE: by
`maxOut_le_intr`, the value `A` hands the reduction is no bigger than `A`'s own cost bound, so the
reduction's linear-in-that-size work is bounded by `L.slope · P(l) + L.base` — and the added calls are
the fixed `L.qadd`. This is the honest successor to the earlier version of this lemma, which took the
overhead as an unconnected poly of `l`. -/
theorem polyTime_postMapProg (hI : ∀ l, G'.Inst l = G.Inst l)
    (red : ∀ l, G.Inst l → G.Ans l → FreeOracle O Q R (G'.Ans l))
    (sz : AnsSize G) (sz' : AnsSize G') (L : LinCost O)
    (hred : ∀ l (i : G.Inst l) (a : G.Ans l), cost (sz' l) (red l i a) ≤ L.at' (sz l a))
    (A : CostAdversary G O Q R) (hA : PolyTime sz A) :
    PolyTime sz' (A.postMapProg hI red) := by
  obtain ⟨C, k, hC⟩ := hA
  have hstep : ∀ l (i : G'.Inst l),
      (cost (sz' l) ((A.postMapProg hI red).prog l i)).total
        ≤ (C * l ^ k + C) + (L.slope * (C * l ^ k + C) + L.base + ∑ o, L.qadd o) := by
    intro l i
    have htight := cost_postMapProg_tight hI red sz sz' L hred A l i
    have hbase := hC l (hI l ▸ i)
    have hintr : (cost (sz l) (A.prog l (hI l ▸ i))).intr ≤ C * l ^ k + C :=
      (Cost.intr_le_total _).trans hbase
    have hmono := Cost.total_mono htight
    rw [Cost.total_add, LinCost.total_at'] at hmono
    have hslope : L.slope * (cost (sz l) (A.prog l (hI l ▸ i))).intr ≤ L.slope * (C * l ^ k + C) :=
      Nat.mul_le_mul_left _ hintr
    omega
  have hpoly : PolyBoundedNat (fun l =>
      (C * l ^ k + C) + (L.slope * (C * l ^ k + C) + L.base + ∑ o, L.qadd o)) :=
    polyBoundedNat_add ⟨k, C, fun _ => le_rfl⟩
      (polyBoundedNat_add
        (polyBoundedNat_add (polyBoundedNat_const_mul L.slope ⟨k, C, fun _ => le_rfl⟩)
          (polyBoundedNat_const L.base))
        (polyBoundedNat_const (∑ o, L.qadd o)))
  obtain ⟨k', C', hC'⟩ := hpoly
  exact ⟨C', k', fun l i => (hstep l i).trans (hC' l)⟩

/-! ### The raw-adversary shadow, and the denotation square. -/

/-- **THE POST-PROCESSING WRAPPER at the raw-`Adversary` level** — the shape the spine reductions
literally have (`run l i := f l i (A.run l i)`, instance passed through). -/
def Adversary.postMap (hI : ∀ l, G'.Inst l = G.Inst l)
    (f : ∀ l, G.Inst l → G.Ans l → G'.Ans l) (A : Adversary G) : Adversary G' where
  run := fun l i => f l (hI l ▸ i) (A.run l (hI l ▸ i))

/-- **THE STRAIGHT-LINE REDUCTION PROGRAM for a pure reshaping `f`** — declare `cw · (input size) + bw`
instructions of work, then emit `f l i a`. Its cost is DERIVED from this syntax by `cost_reshape`. -/
def reduceProg (sz : AnsSize G) (f : ∀ l, G.Inst l → G.Ans l → G'.Ans l) (cw bw : ℕ) :
    ∀ l, G.Inst l → G.Ans l → FreeOracle O Q R (G'.Ans l) :=
  fun l i a => reshape (cw * sz l a + bw) (f l i a)

/-- **THE DENOTATION SQUARE** — denoting the cost-level wrapper equals raw-wrapping the denotation. So a
cost program's reshaping tracks the raw reduction exactly. -/
theorem toAdversary_postMapProg [∀ o, Inhabited (R o)] (hI : ∀ l, G'.Inst l = G.Inst l)
    (sz : AnsSize G) (f : ∀ l, G.Inst l → G.Ans l → G'.Ans l) (cw bw : ℕ)
    (A : CostAdversary G O Q R) :
    (A.postMapProg hI (reduceProg (Q := Q) (R := R) sz f cw bw)).toAdversary
      = Adversary.postMap hI f A.toAdversary := by
  unfold CostAdversary.toAdversary Adversary.postMap
  congr 1
  funext l i
  show denote (fun _ _ => default)
      (bind (A.prog l (hI l ▸ i)) (reduceProg sz f cw bw l (hI l ▸ i)))
    = f l (hI l ▸ i) (A.toAdversary.run l (hI l ▸ i))
  rw [denote_bind]
  simp [reduceProg, CostAdversary.toAdversary]

/-! ## §4 — the `FloorGames` connection: `IsPolyTime` as a class over raw adversaries. -/

/-- **`IsPolyTime sz A`** — a raw `FloorGames.Adversary` is EFFICIENT iff SOME poly-time cost program
denotes to it, at the game's answer-size measure `sz`. This is the `Eff` predicate with content: plugging
it into `FloorGames.Hard`/`HashCRHardQuant` yields a floor that quantifies over EFFICIENT adversaries,
not all functions. (Oracle interface fixed to the trivial single oracle `(Unit, Unit, Unit)`; the spine
reductions need no oracle branching. The per-oracle machinery of §0 is what a richer interface uses.) -/
def IsPolyTime (sz : AnsSize G) (A : Adversary G) : Prop :=
  ∃ B : CostAdversary G Unit (fun _ => Unit) (fun _ => Unit), B.toAdversary = A ∧ PolyTime sz B

/-- **THE FLOOR AT `Eff := IsPolyTime` IS NON-VACUOUS.** The class contains the return adversary whenever
the answer it writes is poly-size. -/
theorem isPolyTime_inhabited (sz : AnsSize G) (a₀ : ∀ l, G.Inst l → G.Ans l)
    (hsz : ∃ C k : ℕ, ∀ l (i : G.Inst l), sz l (a₀ l i) ≤ C * l ^ k + C) :
    IsPolyTime sz (idAdv (O := Unit) (Q := fun _ => Unit) (R := fun _ => Unit) a₀).toAdversary :=
  ⟨idAdv a₀, rfl, idAdv_polyTime sz a₀ hsz⟩

/-- **⚑ `IsPolyTime` IS CLOSED UNDER SIZE-LINEAR POST-COMPOSITION — the theorem the spine consumes to
discharge `hEff`.**

The reduction is a pure reshaping `f` that
  * costs `cw · (input size) + bw` instructions (DECLARED — design commitment 5: a Lean `fun` has no
    runtime; what is now structural is that the work is charged in the syntax and is LINEAR IN THE INPUT
    SIZE, not a free polynomial in `l`), and
  * does not BLOW UP its input: `sz' (f l i a) ≤ co · sz l a + bo` (a PROVED fact about the concrete
    reduction at every spine use site).

Then the reshaped adversary is `IsPolyTime`, with NO poly-overhead hypothesis: the overhead is derived
from `A`'s own bound via `maxOut_le_intr`.

⚑ The declared work is the one thing a caller could understate (`cw = bw = 0` claims a free reduction).
Even then the reduction is NOT free: `cost_reshape` charges `sz' (f l i a)` for the value it writes, so
the floor on a reduction's cost is the size of its own output, and `hout` is what bounds that. -/
theorem isPolyTime_postMap (hI : ∀ l, G'.Inst l = G.Inst l)
    (f : ∀ l, G.Inst l → G.Ans l → G'.Ans l) (sz : AnsSize G) (sz' : AnsSize G')
    (cw bw co bo : ℕ)
    (hout : ∀ l (i : G.Inst l) (a : G.Ans l), sz' l (f l i a) ≤ co * sz l a + bo)
    {A : Adversary G} (hA : IsPolyTime sz A) :
    IsPolyTime sz' (Adversary.postMap hI f A) := by
  obtain ⟨B, hBA, hBpoly⟩ := hA
  refine ⟨B.postMapProg hI (reduceProg sz f cw bw), ?_, ?_⟩
  · rw [toAdversary_postMapProg, hBA]
  · refine polyTime_postMapProg hI _ sz sz' ⟨cw + co, bw + bo, fun _ => 0⟩ ?_ B hBpoly
    intro l i a
    exact cost_reshape_le (sz' l) (sz l a) _ (f l i a) cw bw co bo le_rfl (hout l i a)

/-- **A self-contained rehearsal of the spine discharge**, over abstract games standing in for the
spine's two reduction hops. Given `A` efficient and both reshapings size-linear and non-blowing-up, the
composed finder is efficient — which is precisely `hEff`. No `hEff` parameter is assumed; it is PROVED,
and no poly overhead is assumed either. -/
theorem composed_reduction_isPolyTime
    (hI' : ∀ l, G'.Inst l = G.Inst l) (hI'' : ∀ l, G''.Inst l = G'.Inst l)
    (f : ∀ l, G.Inst l → G.Ans l → G'.Ans l) (g : ∀ l, G'.Inst l → G'.Ans l → G''.Ans l)
    (sz : AnsSize G) (sz' : AnsSize G') (sz'' : AnsSize G'')
    (cwf bwf cof bof cwg bwg cog bog : ℕ)
    (hf : ∀ l (i : G.Inst l) (a : G.Ans l), sz' l (f l i a) ≤ cof * sz l a + bof)
    (hg : ∀ l (i : G'.Inst l) (a : G'.Ans l), sz'' l (g l i a) ≤ cog * sz' l a + bog)
    {A : Adversary G} (hA : IsPolyTime sz A) :
    IsPolyTime sz'' (Adversary.postMap hI'' g (Adversary.postMap hI' f A)) :=
  isPolyTime_postMap hI'' g sz' sz'' cwg bwg cog bog hg
    (isPolyTime_postMap hI' f sz sz' cwf bwf cof bof hf hA)

/-! ### The spine discharge, spelled out.

`Market.WideCommitBoundary.stateCommit_binds_from_polyTime` instantiates
`composed_reduction_isPolyTime` at the two spine hops (`stateCommitBreakGame → wireCommitBreakGame →
hashGame (wideFamily D)`, all with `Inst := fun _ => D.Tag`), with CONCRETE size measures and with both
non-blow-up bounds PROVED (`kernelPayload_length` gives a 358-symbol wire answer; the chain walk returns
two lists of at most 11 felts). No `PolyBoundedNat ov` is passed. -/

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  Cost.total_le,
  Cost.billed_le,
  FreeOracle.maxOut_le_intr,
  FreeOracle.runCost_le_cost,
  FreeOracle.cost_tickN,
  FreeOracle.cost_probe,
  FreeOracle.cost_reshape,
  FreeOracle.cost_bind_le_lin,
  FreeOracle.denote_bind,
  FreeOracle.sz_denote_le_maxOut,
  polyTime_iff_intr_and_queries,
  billed_le_of_polyTime,
  idAdv_polyTime,
  idAdv_polyTime_expGame,
  bruteForce_cost,
  bruteForce_not_polyTime,
  queryHog_cost,
  queryHog_polyIntr,
  queryHog_not_polyQueries,
  queryHog_not_polyTime,
  bruteForce_solves,
  expGame_top_false,
  polyBoundedNat_add,
  cost_postMapProg_tight,
  polyTime_postMapProg,
  toAdversary_postMapProg,
  isPolyTime_inhabited,
  isPolyTime_postMap,
  polyTime_proper,
  composed_reduction_isPolyTime
]

end Dregg2.Crypto.CostAdversary
