/-
# Dregg2.Sat.LratCert — propositional UNSAT as a committed certificate family (L2).

Lane E of `docs/automata/SUBSTRATE-DECISION.md` §7; the "propositional UNSAT" row of
`docs/automata/SEMANTIC-CEILING.md` §2 and its §5 item 3. 2026-11-06.

## The object

A **statement** is `(root, claim := unsat)`: the MMR root of the injective, length-prefixed
flattening of a CNF (`flattenCnf`, `flattenCnf_injective`; the `FixpointCert.flatten` shape). A
**certificate** is the CNF (DIMACS literals, `List (List Int)`) and an LRAT proof: addition steps
`(id, clause, hints)` and deletion steps. `verify hash st c` recomputes the root and runs
`checkLrat`: input clauses get ids `1 … |f|`; each addition must use a fresh id and pass the RUP
check over its hints IN ORDER (each hinted clause, with the literals the running assignment
falsifies removed, must be a unit, which is assigned, or empty, which is the conflict); a deletion
drops ids from the table; the proof is accepted when the empty clause is added.

## Two checkers, and why this file has its own [READ, MEASURED]

The toolchain ships a verified LRAT checker: `Std.Tactic.BVDecide.LRAT.check : Array IntAction →
CNF Nat → Bool` with `check_sound : check proof cnf → cnf.Unsat` (Lean core `Std`, the checker
`bv_decide` trusts; RUP and RAT, deletion). It is REUSED here as `checkStd` with `checkStd_sound`;
this file adds the DIMACS translation (`toStdLit` maps DIMACS `v` to `Std` variable `v - 1`,
because `CNF.convertLRAT` adds one; the input must be zero-free, `wf`). What it cannot do here
[MEASURED, this session]: its acceptance is not kernel-reducible from an importing module (`decide
+kernel`, `rfl` and `Eq.refl` all fail on `check php3Proof php3`; the cause is [INFERRED]: the
`Std` modules are compiled with the module system and its well-founded `go` loop), so its acceptance on a concrete proof is only a compiled `#guard`, and a
kernel-checked `Unsat` term through it would need `native_decide`.

So the certificate's checker is `checkLrat`, a RUP-only LRAT checker over lists with structural
recursion (no `Array`, no well-founded recursion), proved sound here (`rup_sound`, `run_sound`,
`checkLrat_sound`); its acceptance and every falsifier are kernel-decided theorems. The shipped
checker is the cross-check: `#guard`s show the two agree on every example below. It is also the
shape an arithmetization would follow (a clause table looked up by id, one unit step per hint),
which `CompactLRATChecker`'s array formula with assignment arrays is not.

## What is proved (kernel-clean, §7)

  * `rup_sound`: a clause passing the RUP check over a table is satisfied by every assignment
    satisfying the table.
  * `checkLrat_sound : checkLrat f p = true → Unsat f`.
  * `checkStd_sound : checkStd f p = true → Unsat f` (the shipped theorem plus the translation).
  * `verify_sound : verify hash st c = true → mroot hash (flattenCnf c.cnf) = st.root ∧ Unsat c.cnf`.
  * `refutes_intended_or_collides`: for an intended CNF `E` committed at `st.root`, an accepted
    certificate refutes `E`, or the sponge collides at the pair `mrootFind` names (floor-free).
  * `php3_unsat : Unsat php3`, a term, through `checkLrat_sound` and a kernel `decide`.

## Falsifiers (§6; kernel-decided theorems AND `#guard`s)

PHP(3,2) — three pigeons, two holes, 9 clauses over 6 variables — with its LRAT refutation as
CaDiCaL 3.0.1 `--lrat --binary=false` printed it (7 additions, no deletions):
  (a) the refutation is ACCEPTED (`checkLrat`, `verify`, and the shipped `checkStd`);
  (b) the same proof with one hint removed (the last step loses clause 9) is REFUSED;
  (c) `checkNoRup` — a no-RUP comparator retaining fresh ids and requiring EVERY hint to
      resolve (not an acceptance superset, as `noRup_not_superset` proves) — ACCEPTS a bogus
      addition (`¬x₁` from `x₁ ∨ x₂`, then the empty clause) on a satisfiable CNF that `checkLrat` refuses;
  (d) a SATISFIABLE CNF with a forged empty-clause step is refused by `checkLrat` and ACCEPTED by
      `checkNoRup`; through `verifyNoRup` / `verify` the same split holds at a correct root;
  (e) a wrong root is refused (the PHP certificate at the root of the satisfiable CNF);
  (f) `reusedId_separation`: `[[1],[-1]]` with `.add 1 [] [1,2]` passes every RUP obligation
      but is refused solely by freshness; `checkNoFresh` accepts it.

## Counts (§6, pinned) and per-step cost

For the PHP(3,2) proof: 7 steps, 18 hint lookups in all, at most 5 in one step, clause width 2 in
the CNF and 1 in the proof (`k = 2`, the width normalized chaining pads to, 2609.19353), 29 literal
reads by the RUP checks. Per step, in substrate-neutral units (SEMANTIC-CEILING §2): one hint = one
clause-table lookup by id plus `|clause|` literal reads against the running assignment, each read a
membership of the negated literal (one equality gate per comparison, the "pivot check"); the
deletion step is one table update per id. The AIR is NOT built; no Tower256 or BabyBear count is
claimed for this family.

## NOT claimed

Completeness (that every valid LRAT proof is accepted; RAT steps are refused by construction,
since `Step` has no RAT form); anything about a solver; any circuit; uniqueness of a claim (the
claim is the constant `unsat`, so the content binding IS the theorem). `flattenCnf` is injective
over `ℤ`; a deployed hash reducing leaves modulo a prime aliases `e(0)` and `e(p)` (§2 obligation
(vi) of the substrate decision). Prior art, not a first: Lammich's GRAT, Heule-Hunt-Kaufmann-
Wetzler's verified LRAT checker (ACL2), Lean's `BVDecide` checker (reused above); ZKUNSAT
(ePrint 2022/206) arithmetizes resolution.

## Axiom hygiene
`#assert_all_clean` on every theorem; no `sorry`, no `native_decide`. NEW file; imports read-only.
-/
import Std.Tactic.BVDecide.LRAT.Checker
import Dregg2.Lightclient.MMR
import Dregg2.Tactics

namespace Dregg2.Sat.LratCert

open Dregg2.Lightclient.MMR (mroot MRootColl mroot_binds_or_collides)

set_option autoImplicit false

/-! ## §1 — CNF and satisfaction. -/

/-- A clause is a disjunction of DIMACS literals (`v > 0` is variable `v`, `-v` its negation, `0` is
no literal). -/
abbrev Clause := List Int
/-- A CNF is a conjunction of clauses. -/
abbrev Cnf := List Clause

/-- The value of a literal under an assignment of the DIMACS variables. `0` is never true. -/
def litVal (a : Nat → Bool) (l : Int) : Bool :=
  if 0 < l then a l.natAbs else if l < 0 then !a l.natAbs else false

/-- `a` satisfies `f`: every clause has a true literal. -/
def Satisfies (a : Nat → Bool) (f : Cnf) : Prop := ∀ c ∈ f, ∃ l ∈ c, litVal a l = true

/-- **The claim.** No assignment satisfies `f`. -/
def Unsat (f : Cnf) : Prop := ∀ a : Nat → Bool, ¬ Satisfies a f

theorem litVal_neg_true {a : Nat → Bool} {l : Int} (h : litVal a (-l) = true) :
    litVal a l = false := by
  unfold litVal at *
  rcases lt_trichotomy l 0 with hl | hl | hl
  · have h1 : 0 < -l := by omega
    rw [if_pos h1, Int.natAbs_neg] at h
    rw [if_neg (by omega), if_pos hl, h]; rfl
  · subst hl; simp at h
  · have h1 : ¬ 0 < -l := by omega
    have h2 : -l < 0 := by omega
    rw [if_neg h1, if_pos h2, Int.natAbs_neg] at h
    rw [if_pos hl]; simpa using h

theorem litVal_neg_of_false {a : Nat → Bool} {l : Int} (h0 : l ≠ 0) (h : litVal a l = false) :
    litVal a (-l) = true := by
  unfold litVal at *
  rcases lt_trichotomy l 0 with hl | hl | hl
  · rw [if_neg (by omega), if_pos hl] at h
    rw [if_pos (by omega), Int.natAbs_neg]; simpa using h
  · exact absurd hl h0
  · rw [if_pos hl] at h
    rw [if_neg (by omega), if_pos (by omega), Int.natAbs_neg, h]; rfl

/-! ## §2 — The RUP check and its soundness. -/

/-- The clause table: `(id, clause)`, newest first; lookup takes the first match. -/
abbrev Table := List (Nat × Clause)

def lookup : Table → Nat → Option Clause
  | [], _ => none
  | (j, c) :: t, i => if j = i then some c else lookup t i

theorem lookup_mem : ∀ {t : Table} {i : Nat} {c : Clause}, lookup t i = some c → (i, c) ∈ t
  | [], _, _, h => by simp [lookup] at h
  | (j, d) :: t, i, c, h => by
    unfold lookup at h
    split at h
    · cases h; rename_i hj; subst hj; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem h)

/-- `asg` lists the literals assumed true. A hinted clause, with every literal whose negation is
assumed removed, must be empty (conflict: accept) or a unit (assume it: continue). -/
def propagate (t : Table) : List Int → List Nat → Bool
  | _, [] => false
  | asg, h :: hs =>
    match lookup t h with
    | none => false
    | some c =>
      match c.filter (fun l => !asg.contains (-l)) with
      | [] => true
      | [u] => propagate t (u :: asg) hs
      | _ => false

/-- **The RUP check**: assume the negation of every (nonzero) literal of `c`, propagate. -/
def rupCheck (t : Table) (c : Clause) (hints : List Nat) : Bool :=
  propagate t ((c.filter (· != 0)).map (- ·)) hints

/-- The table is satisfied by `a`. -/
def TableSat (a : Nat → Bool) (t : Table) : Prop := ∀ e ∈ t, ∃ l ∈ e.2, litVal a l = true

theorem propagate_sound {a : Nat → Bool} {t : Table} (ht : TableSat a t) :
    ∀ (hs : List Nat) (asg : List Int), (∀ l ∈ asg, litVal a l = true) →
      propagate t asg hs = true → False
  | [], _, _, h => by simp [propagate] at h
  | h :: hs, asg, hasg, hp => by
    unfold propagate at hp
    split at hp
    · exact Bool.false_ne_true hp
    · rename_i c hc
      obtain ⟨l, hl, hlv⟩ := ht _ (lookup_mem hc)
      -- the satisfied literal survives the filter: its negation is not assumed
      have hsurv : l ∈ c.filter (fun l => !asg.contains (-l)) := by
        refine List.mem_filter.mpr ⟨hl, ?_⟩
        cases hcon : asg.contains (-l)
        · rfl
        · have := litVal_neg_true (hasg _ (by simpa using hcon))
          rw [hlv] at this; exact absurd this (by decide)
      split at hp
      · rename_i heq; rw [heq] at hsurv; simp at hsurv
      · rename_i u heq
        rw [heq, List.mem_singleton] at hsurv
        subst hsurv
        exact propagate_sound ht hs (l :: asg)
          (by intro x hx; rcases List.mem_cons.mp hx with rfl | hx; exacts [hlv, hasg x hx]) hp
      · exact Bool.false_ne_true hp

/-- ⚑ **`rup_sound`** — a clause passing the RUP check is implied by the table. -/
theorem rup_sound {t : Table} {c : Clause} {hints : List Nat} (h : rupCheck t c hints = true)
    (a : Nat → Bool) (ht : TableSat a t) : ∃ l ∈ c, litVal a l = true := by
  by_contra hno
  push Not at hno
  refine propagate_sound ht hints _ ?_ h
  intro x hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
  have ⟨hlc, hl0⟩ := List.mem_filter.mp hl
  have hl0' : l ≠ 0 := by simpa using hl0
  have hf : litVal a l = false := by simpa using hno l hlc
  exact litVal_neg_of_false hl0' hf

/-! ## §3 — LRAT proofs and the checker. -/

/-- An LRAT step (RUP only). `add id c hints`: add `c` (the empty clause concludes) under the hint
chain; `del ids`: delete. -/
inductive Step where
  | add (id : Nat) (c : Clause) (hints : List Nat)
  | del (ids : List Nat)
  deriving Repr, DecidableEq

/-- Replay a proof against a table. -/
def run : Table → List Step → Bool
  | _, [] => false
  | t, .add id c hints :: rest =>
    (lookup t id).isNone && rupCheck t c hints &&
      (c.isEmpty || run ((id, c) :: t) rest)
  | t, .del ids :: rest => run (t.filter fun e => !ids.contains e.1) rest

/-- The input clauses with ids `n, n+1, …`. -/
def index : Nat → Cnf → Table
  | _, [] => []
  | n, c :: cs => (n, c) :: index (n + 1) cs

theorem mem_index : ∀ {n : Nat} {f : Cnf} {e : Nat × Clause}, e ∈ index n f → e.2 ∈ f
  | _, [], _, h => by simp [index] at h
  | n, c :: cs, e, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_index h)

/-- **The checker**: replay from the input clauses numbered `1 … |f|`. -/
def checkLrat (f : Cnf) (p : List Step) : Bool := run (index 1 f) p

theorem run_sound {a : Nat → Bool} : ∀ (p : List Step) (t : Table), TableSat a t →
    run t p = true → False
  | [], _, _, h => by simp [run] at h
  | .add id c hints :: rest, t, ht, h => by
    simp only [run, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨⟨_, hr⟩, hk⟩ := h
    obtain ⟨l, hl, hlv⟩ := rup_sound hr a ht
    rcases hk with he | hk
    · rw [List.isEmpty_iff.mp he] at hl; simp at hl
    · refine run_sound (a := a) rest _ ?_ hk
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨l, hl, hlv⟩
      · exact ht e he
  | .del ids :: rest, t, ht, h => by
    simp only [run] at h
    exact run_sound (a := a) rest _ (fun e he => ht e (List.mem_filter.mp he).1) h

/-- ⚑ **`checkLrat_sound`** — an accepted LRAT proof refutes the CNF. -/
theorem checkLrat_sound (f : Cnf) (p : List Step) (h : checkLrat f p = true) : Unsat f := by
  intro a hsat
  exact run_sound p _ (fun e he => hsat _ (mem_index he)) h

/-! ## §4 — The shipped checker, reused as the cross-check. -/

/-- A DIMACS literal as a `Std.Sat` literal: variable `v - 1` (the shipped `CNF.convertLRAT` adds
one back), polarity the sign. -/
def toStdLit (l : Int) : Std.Sat.Literal Nat := (l.natAbs - 1, decide (0 < l))

def toStd (f : Cnf) : Std.Sat.CNF Nat := { clauses := (f.map fun c => c.map toStdLit).toArray }

/-- Zero-free: the translation is faithful only on DIMACS literals. -/
def wf (f : Cnf) : Bool := f.all fun c => c.all (· != 0)

def Step.toAction : Step → Std.Tactic.BVDecide.LRAT.IntAction
  | .add id [] hints => .addEmpty id hints.toArray
  | .add id c hints  => .addRup id c.toArray hints.toArray
  | .del ids         => .del ids.toArray

/-- The shipped `LRAT.check` on the translated CNF and proof. -/
def checkStd (f : Cnf) (p : List Step) : Bool :=
  wf f && Std.Tactic.BVDecide.LRAT.check (p.map Step.toAction).toArray (toStd f)

theorem toStd_eval_of_satisfies {a : Nat → Bool} {f : Cnf} (hw : wf f = true)
    (hs : Satisfies a f) : (toStd f).eval (fun v => a (v + 1)) = true := by
  simp only [Std.Sat.CNF.eval, toStd, Std.Sat.CNF.Clause.eval, List.all_toArray, List.all_map,
    List.all_eq_true, Function.comp_def, List.any_map, List.any_eq_true, beq_iff_eq]
  intro c hc
  obtain ⟨l, hl, hlv⟩ := hs c hc
  have hl0 : l ≠ 0 := by
    have := (List.all_eq_true.mp ((List.all_eq_true.mp hw) c hc)) l hl
    simpa using this
  refine ⟨l, hl, ?_⟩
  simp only [toStdLit]
  have hpos : l.natAbs - 1 + 1 = l.natAbs := by omega
  rw [hpos]
  unfold litVal at hlv
  rcases lt_trichotomy l 0 with h | h | h
  · rw [if_neg (by omega), if_pos h] at hlv
    simp only [Bool.not_eq_true'] at hlv
    rw [hlv]; simp; omega
  · exact absurd h hl0
  · rw [if_pos h] at hlv; rw [hlv]; simp [h]

/-- ⚑ **`checkStd_sound`** — the shipped `LRAT.check_sound`, plus the DIMACS translation. -/
theorem checkStd_sound (f : Cnf) (p : List Step) (h : checkStd f p = true) : Unsat f := by
  intro a hsat
  simp only [checkStd, Bool.and_eq_true] at h
  have hu := Std.Tactic.BVDecide.LRAT.check_sound _ _ h.2 (fun v => a (v + 1))
  rw [toStd_eval_of_satisfies h.1 hsat] at hu
  exact Bool.false_ne_true hu.symm

/-! ## §5 — The committed statement and the binding. -/

/-- Length-prefixed flattening of a CNF: `|c|, literals…` per clause. Injective. -/
def flattenCnf (f : Cnf) : List ℤ := f.flatMap fun c => (c.length : ℤ) :: c

theorem flattenCnf_injective : ∀ (f₁ f₂ : Cnf), flattenCnf f₁ = flattenCnf f₂ → f₁ = f₂
  | [], [], _ => rfl
  | [], (c :: _), h => by simp [flattenCnf] at h
  | (c :: _), [], h => by simp [flattenCnf] at h
  | (c₁ :: r₁), (c₂ :: r₂), h => by
    simp only [flattenCnf, List.flatMap_cons, List.cons_append, List.cons.injEq] at h
    obtain ⟨hl, hrest⟩ := h
    have hl' : c₁.length = c₂.length := by exact_mod_cast hl
    obtain ⟨hc, hr⟩ := List.append_inj hrest hl'
    have := flattenCnf_injective r₁ r₂ (by simpa [flattenCnf] using hr)
    rw [hc, this]

/-- The statement: the committed CNF root. The claim is the constant `unsat`. -/
structure Statement where
  root : ℤ
  deriving Repr

/-- The certificate: the CNF (opened against the root) and the LRAT proof. -/
structure Certificate where
  cnf : Cnf
  proof : List Step
  deriving Repr

/-- **The verifier.** -/
def verify (hash : List ℤ → ℤ) (st : Statement) (c : Certificate) : Bool :=
  (mroot hash (flattenCnf c.cnf) == st.root) && checkLrat c.cnf c.proof

/-- ⚑ **`verify_sound`** — an accepted certificate opens the root and refutes its CNF. -/
theorem verify_sound (hash : List ℤ → ℤ) (st : Statement) (c : Certificate)
    (h : verify hash st c = true) :
    mroot hash (flattenCnf c.cnf) = st.root ∧ Unsat c.cnf := by
  simp only [verify, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1, checkLrat_sound _ _ h.2⟩

/-- ⚑ **`refutes_intended_or_collides`** — THE BINDING THEOREM. If `E` is the CNF intended at
`st.root`, an accepted certificate refutes `E` itself, or the sponge collides at the pair
`mrootFind` names between the certificate's CNF and `E`. -/
theorem refutes_intended_or_collides (hash : List ℤ → ℤ) (st : Statement) (c : Certificate)
    (h : verify hash st c = true) (E : Cnf) (hE : mroot hash (flattenCnf E) = st.root) :
    Unsat E ∨ MRootColl hash (flattenCnf c.cnf) (flattenCnf E) := by
  obtain ⟨hroot, hunsat⟩ := verify_sound hash st c h
  rcases mroot_binds_or_collides hash (hroot.trans hE.symm) with heq | hc
  · exact Or.inl (flattenCnf_injective _ _ heq ▸ hunsat)
  · exact Or.inr hc

/-! ## §6 — Non-vacuity, falsifiers, counts. -/

namespace Reference

/-- A concrete hash for the examples (NOT Poseidon2; the theorems are abstract in `hash`). -/
def hash0 (l : List ℤ) : ℤ := l.foldl (fun a x => (a * 1000003 + x) % 2013265921) 17

/-- PHP(3,2): variable `2(i-1)+j` says pigeon `i` sits in hole `j`. -/
def php3 : Cnf :=
  [[1, 2], [3, 4], [5, 6], [-1, -3], [-1, -5], [-3, -5], [-2, -4], [-2, -6], [-4, -6]]

/-- Its LRAT refutation, as CaDiCaL 3.0.1 `--lrat --binary=false` printed it. -/
def php3Proof : List Step :=
  [ .add 10 [-2] [7, 8, 2, 3, 6]
  , .add 11 [1] [10, 1]
  , .add 12 [-3] [11, 4]
  , .add 13 [-5] [11, 5]
  , .add 14 [4] [12, 2]
  , .add 15 [6] [13, 3]
  , .add 16 [] [14, 15, 9] ]

/-- The same proof with ONE hint removed: the last step loses clause 9 (`¬x₄ ∨ ¬x₆`). -/
def php3DropHint : List Step := php3Proof.take 6 ++ [.add 16 [] [14, 15]]

/-- A malformed replay: the first step reuses input id `1`, and later hints still cite `10`.
This is not an isolated freshness falsifier; see `reusedId_separation`. -/
def php3ReusedId : List Step := .add 1 [-2] [7, 8, 2, 3, 6] :: php3Proof.drop 1

/-- A satisfiable CNF: `x₁`, `x₁ ∨ x₂`. -/
def satCnf : Cnf := [[1], [1, 2]]
/-- A forged empty-clause step citing both clauses. -/
def forgedEmpty : List Step := [.add 3 [] [1, 2]]
/-- A bogus addition: `¬x₁` cited from `x₁ ∨ x₂` (not RUP), then the empty clause. -/
def bogusAdd : List Step := [.add 3 [-1] [2], .add 4 [] [1, 3]]

/-- A no-RUP comparator retaining fresh ids and requiring EVERY hint to name a live clause.
It separates the examples below, but is not an acceptance superset of `run`: RUP may return
early on a conflict without reading later hints. See `noRup_not_superset`. -/
def runNoRup : Table → List Step → Bool
  | _, [] => false
  | t, .add id c hints :: rest =>
    (lookup t id).isNone && hints.all (fun h => (lookup t h).isSome) &&
      (c.isEmpty || runNoRup ((id, c) :: t) rest)
  | t, .del ids :: rest => runNoRup (t.filter fun e => !ids.contains e.1) rest

def checkNoRup (f : Cnf) (p : List Step) : Bool := runNoRup (index 1 f) p

def verifyNoRup (hash : List ℤ → ℤ) (st : Statement) (c : Certificate) : Bool :=
  (mroot hash (flattenCnf c.cnf) == st.root) && checkNoRup c.cnf c.proof

def phpStmt : Statement := ⟨mroot hash0 (flattenCnf php3)⟩
def satStmt : Statement := ⟨mroot hash0 (flattenCnf satCnf)⟩

-- (a) ACCEPTED: the solver's refutation, by the checker, the verifier, and the shipped checker.
theorem php3_accepted : checkLrat php3 php3Proof = true := by decide
theorem php3_verified : verify hash0 phpStmt ⟨php3, php3Proof⟩ = true := by decide
#guard checkLrat php3 php3Proof
#guard verify hash0 phpStmt ⟨php3, php3Proof⟩
#guard checkStd php3 php3Proof

/-- ⚑ **Non-vacuity**: PHP(3,2) is unsatisfiable, as a term, through `checkLrat_sound`. -/
theorem php3_unsat : Unsat php3 := checkLrat_sound _ _ php3_accepted

-- (b) one hint removed: REFUSED (both checkers).
theorem php3_dropHint_refused : checkLrat php3 php3DropHint = false := by decide
#guard !checkLrat php3 php3DropHint && !checkStd php3 php3DropHint

-- (c) the no-RUP comparator ACCEPTS the bogus addition that `checkLrat` REFUSES.
theorem bogus_accepted_by_noRup : checkNoRup satCnf bogusAdd = true := by decide
theorem bogus_refused : checkLrat satCnf bogusAdd = false := by decide
#guard checkNoRup satCnf bogusAdd && !checkLrat satCnf bogusAdd && !checkStd satCnf bogusAdd

-- (d) a SATISFIABLE CNF with a forged empty clause: refused, and the no-RUP comparator accepts it,
-- also at the verifier level with a correct root.
theorem forged_accepted_by_noRup : verifyNoRup hash0 satStmt ⟨satCnf, forgedEmpty⟩ = true := by
  decide
theorem forged_refused : verify hash0 satStmt ⟨satCnf, forgedEmpty⟩ = false := by decide
#guard !checkLrat satCnf forgedEmpty && !checkStd satCnf forgedEmpty
/-- The forged certificate's CNF really is satisfiable (`x₁ := true`), so its acceptance by
`verifyNoRup` is a false `Unsat` claim, not a lucky one. -/
theorem satCnf_sat : Satisfies (fun _ => true) satCnf := by
  intro c hc
  simp only [satCnf, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> exact ⟨1, by simp, by decide⟩

-- (e) a wrong root: the PHP certificate at the satisfiable CNF's root is refused.
theorem wrong_root_refused : verify hash0 satStmt ⟨php3, php3Proof⟩ = false := by decide
#guard !verify hash0 satStmt ⟨php3, php3Proof⟩

-- (f) The malformed PHP replay is refused; it violates both freshness and later hint lookup.
theorem reusedId_refused : checkLrat php3 php3ReusedId = false := by decide
#guard rupCheck (index 1 php3) [-2] [7, 8, 2, 3, 6]

/-- Freshness-omitting comparator: all RUP obligations and replay behavior are unchanged. -/
def runNoFresh : Table → List Step → Bool
  | _, [] => false
  | t, .add id c hints :: rest =>
    rupCheck t c hints && (c.isEmpty || runNoFresh ((id, c) :: t) rest)
  | t, .del ids :: rest => runNoFresh (t.filter fun e => !ids.contains e.1) rest

def checkNoFresh (f : Cnf) (p : List Step) : Bool := runNoFresh (index 1 f) p

/-- The reused id is the ONLY failed obligation: both hints are live and produce a conflict. -/
theorem reusedId_separation :
    checkNoFresh [[1], [-1]] [.add 1 [] [1, 2]] = true ∧
    checkLrat [[1], [-1]] [.add 1 [] [1, 2]] = false := by decide

/-- Removing the final conflict hint passes the no-RUP comparator but fails real replay. -/
theorem dropHint_separation :
    checkNoRup php3 php3DropHint = true ∧ checkLrat php3 php3DropHint = false := by decide

/-- Early conflict makes the unused, nonexistent hint irrelevant to RUP, but not `checkNoRup`. -/
theorem noRup_not_superset :
    checkLrat [[]] [.add 2 [] [1, 999]] = true ∧
    checkNoRup [[]] [.add 2 [] [1, 999]] = false := by decide

/-! ### Counts, pinned.

`hintLookups` = clause-table lookups summed over steps; `maxHints` = the longest chain; widths;
`literalReads` = `Σ` over hints of the hinted clause's width (the negated-literal membership tests
of the RUP check), computed by replaying the table. -/

def stepHints : Step → Nat
  | .add _ _ h => h.length
  | .del _ => 0

def stepWidth : Step → Nat
  | .add _ c _ => c.length
  | .del _ => 0

def literalReads : Table → List Step → Nat
  | _, [] => 0
  | t, .add id c hints :: rest =>
    (hints.map fun h => ((lookup t h).getD []).length).sum + literalReads ((id, c) :: t) rest
  | t, .del ids :: rest => literalReads (t.filter fun e => !ids.contains e.1) rest

#guard php3.length == 9
#guard php3Proof.length == 7
#guard (php3Proof.map stepHints).sum == 18
#guard (php3Proof.map stepHints).foldl max 0 == 5
#guard (php3.map List.length).foldl max 0 == 2
#guard (php3Proof.map stepWidth).foldl max 0 == 1
#guard literalReads (index 1 php3) php3Proof == 29

/-- Reproducible operation counts for the entire honest replay (including all hinted widths). -/
theorem php3_counts :
    php3.length = 9 ∧ php3Proof.length = 7 ∧
    (php3Proof.map stepHints).sum = 18 ∧ (php3Proof.map stepHints).foldl max 0 = 5 ∧
    (php3.map List.length).foldl max 0 = 2 ∧ (php3Proof.map stepWidth).foldl max 0 = 1 ∧
    literalReads (index 1 php3) php3Proof = 29 := by decide

end Reference

/-! ## §7 — axiom tripwires. -/

#assert_all_clean [litVal_neg_true, litVal_neg_of_false, lookup_mem, propagate_sound, rup_sound,
  mem_index, run_sound, checkLrat_sound, toStd_eval_of_satisfies, checkStd_sound,
  flattenCnf_injective, verify_sound, refutes_intended_or_collides,
  Reference.php3_accepted, Reference.php3_verified, Reference.php3_unsat,
  Reference.php3_dropHint_refused, Reference.bogus_accepted_by_noRup, Reference.bogus_refused,
  Reference.forged_accepted_by_noRup, Reference.forged_refused, Reference.satCnf_sat,
  Reference.wrong_root_refused, Reference.reusedId_refused, Reference.reusedId_separation,
  Reference.dropHint_separation, Reference.noRup_not_superset, Reference.php3_counts]

/-! Exact axiom sets for the soundness boundary and the new separation/count terms. -/
/-- info: 'Dregg2.Sat.LratCert.checkLrat_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkLrat_sound
/-- info: 'Dregg2.Sat.LratCert.verify_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms verify_sound
/-- info: 'Dregg2.Sat.LratCert.refutes_intended_or_collides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms refutes_intended_or_collides
/-- info: 'Dregg2.Sat.LratCert.Reference.reusedId_separation' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Reference.reusedId_separation
/-- info: 'Dregg2.Sat.LratCert.Reference.dropHint_separation' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Reference.dropHint_separation
/-- info: 'Dregg2.Sat.LratCert.Reference.noRup_not_superset' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Reference.noRup_not_superset
/-- info: 'Dregg2.Sat.LratCert.Reference.php3_counts' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Reference.php3_counts

end Dregg2.Sat.LratCert
