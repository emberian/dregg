/-
# Dregg2.Crypto.Deriv.BisimCert — derivative-bisimulation certificates for regex inclusion and
equivalence over the infinite `Value` alphabet (L2).

Lane E of `docs/automata/SUBSTRATE-DECISION.md` §7; the "regex equivalence" row of
`docs/automata/SEMANTIC-CEILING.md` §2 and its §5 item 4. 2026-11-06.

## The object

A **statement** is `(r, s, ⊆)` or `(r, s, ≡)` over `PredRE` (the tree's regex over `Pred` leaves,
`Core.lean`). A **certificate** is a list of regex pairs. `bisimOk cls ps r s` checks:
  1. `(r, s)` is in `ps` up to ACI similarity (`memSim`, through the tree's `simDecide` = recursive
     `nrm` then the one-sided `reEq`; only its soundness direction `simDecide_sound` is used);
  2. at every pair, `null p → null q` (`null p = null q` for `bisimEqOk`);
  3. every pair is closed: for every class representative `c ∈ cls`, `(der c p, der c q)` is again
     in `ps` up to `≅`.
`bisimCheck ps r s` computes the classes itself (`classesOf`: the tree's `atomCands` over the
deduplicated pin set of the pairs' leaves, `SymbolicMinterms.lean` §6), so it takes no trusted input
beyond the pair list, and refuses outside the decidable-leaf fragment.

## What is proved (kernel-clean, §6)

  * `closed_under_symbols`: given `Covers (pairLeaves ps) cls` (every inhabited minterm of the
    pairs' leaves has a representative), closure under the representatives is closure under EVERY
    symbol, by the tree's `der_factors_over`. This is the lemma that makes a finite check speak
    about an infinite alphabet.
  * `bisim_core`: the bisimulation argument by induction on the word, generic in the relation
    between nullabilities.
  * `bisim_sound : Covers (pairLeaves ps) cls → bisimOk cls ps r s = true → ∀ w, Matches w r →
    Matches w s`, and `bisimEq_sound` (`↔`).
  * `classesOf_covers` (from the tree's `coverOfAtoms`), hence the hypothesis-free
    `bisimCheck_sound` and `bisimEqCheck_sound`.
  * Non-vacuity as terms: `nodb_subset_anyStar` (the tree's policy regex `noDoubleBraceRE ⊆
    star any`), `a_subset_ab`, `nodb_equiv_assoc` (the policy and its reassociation are equivalent).

## Falsifiers (§5; kernel-decided by `decide +kernel`, mirrored by `#guard`s)

  (a) accepted: `noDoubleBraceRE ⊆ star any`; `a ⊆ a | b` on the alphabet `t = 0` / `t = 1`;
      `noDoubleBraceRE ≡` its reassociation;
  (b) refused: the policy certificate with its root pair dropped, and with an interior derivative
      pair dropped; the `a ⊆ a | b` certificate with a derivative pair dropped;
  (c) refused: the policy's inclusion certificate as an EQUIVALENCE certificate, and the reverse
      inclusion `star any ⊆ noDoubleBraceRE`;
  (d) `bisimNoNullable` (same closure, same computed classes, nullability forgotten) ACCEPTS the
      false inclusions `any ⊆ ε` and `a | b ⊆ a` that `bisimCheck` refuses; `any_not_subset_eps`
      proves the first false at the word `[record []]`.

## Counts (pinned) and cost

`|pairs| · |classes|` derivative-pair lookups, independent of any word (SEMANTIC-CEILING §2):
policy ⊆ `star any`: 11 pairs × 2 classes = 22; `a ⊆ a | b`: 4 × 3 = 12; policy ≡ reassociation:
11 × 2 = 22; `any ⊆ ε`: 3 × 1 = 3. Per lookup the checker computes two derivatives and searches the
pair list up to `≅` (here a linear scan of `simDecide` calls; an arithmetization would key the pair
table by a hash of the normal form, one lookup per derivative pair). No circuit is built.

## The emitter, and what is NOT claimed

`SymbolicEquivalence.predRE_equivalence_decidable` is a `Decidable` instance through emptiness of
the symmetric difference (kernel-evaluable only at a tiny bound, its header says) and
`EquivalenceFixpoint` runs a worklist over `symDiff` states; neither exposes a bisimulation. So this
file adds `emitPairs`, an UNTRUSTED fuel-bounded worklist exploration that prints the pair list
(normalized by `nrm`); every certificate above is its output, checked by `bisimCheck`. NOT claimed:
that `emitPairs` terminates within its fuel or finds a certificate whenever the inclusion holds
(completeness rests on `der_finite` plus `simDecide`'s completeness, which holds only for
`RigidFull` left arguments); any leaf outside `IsSymbolic`'s vocabulary (scalar atoms, cross-field
equality, reactive `(old, new)` atoms: `classesOf` returns `none` and the checker refuses); any
commitment to the regexes (the statement names them in clear; a committed-policy form would bind
them by `mroot` as `Sat/LratCert.lean` does). Prior art, not a first: Nipkow and Traytel's verified
regex equivalence by derivatives (Isabelle), Crepe (arXiv 2504.01198), Brzozowski's derivatives up
to ACI similarity (the tree's `Similarity.lean`, after the ITP'25 finiteness development).

## Axiom hygiene
`#assert_all_clean` on every theorem; no `sorry`, no `native_decide`. NEW file; imports read-only.
-/
import Dregg2.Crypto.Deriv.SymbolicMinterms
import Dregg2.Crypto.Deriv.AciComplete
import Dregg2.Tactics

namespace Dregg2.Crypto.Deriv

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra
open PredRE (der null derives leaf Matches correctness Sim sim_null sim_der sim_derives nrm
  nrm_eq_sim reEq reEq_sound simDecide)

set_option autoImplicit false

namespace BisimCert

/-! ## §1 — Certificates and the checker. -/

/-- A candidate bisimulation: a list of regex pairs. -/
abbrev Pairs := List (PredRE × PredRE)

/-- Every leaf predicate occurring in the pairs: the minterm vocabulary the classes must cover. -/
def pairLeaves (ps : Pairs) : List Pred := ps.flatMap fun pq => leavesOf pq.1 ++ leavesOf pq.2

/-- `(p, q)` is in `ps` up to ACI similarity (the tree's `simDecide`: recursive `nrm`, then the
one-sided `reEq`). -/
def memSim (ps : Pairs) (p q : PredRE) : Bool :=
  ps.any fun pq => simDecide p pq.1 && simDecide q pq.2

/-- Closure of one pair under the derivative by every class representative. -/
def closedAt (cls : List Value) (ps : Pairs) (pq : PredRE × PredRE) : Bool :=
  cls.all fun c => memSim ps (der c pq.1) (der c pq.2)

/-- **The inclusion checker.** `(r, s)` is in the pairs, every pair is closed under every class,
and at every pair `null p → null q`. -/
def bisimOk (cls : List Value) (ps : Pairs) (r s : PredRE) : Bool :=
  memSim ps r s && ps.all fun pq => (!null pq.1 || null pq.2) && closedAt cls ps pq

/-- **The equivalence checker**: as `bisimOk` with `null p = null q` at every pair. -/
def bisimEqOk (cls : List Value) (ps : Pairs) (r s : PredRE) : Bool :=
  memSim ps r s && ps.all fun pq => (null pq.1 == null pq.2) && closedAt cls ps pq

/-! ## §2 — Soundness. -/

theorem simDecide_sound {R S : PredRE} (h : simDecide R S = true) : Sim R S :=
  nrm_eq_sim (reEq_sound h)

theorem memSim_spec {ps : Pairs} {p q : PredRE} (h : memSim ps p q = true) :
    ∃ pq ∈ ps, Sim p pq.1 ∧ Sim q pq.2 := by
  obtain ⟨pq, hm, hb⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true] at hb
  exact ⟨pq, hm, simDecide_sound hb.1, simDecide_sound hb.2⟩

/-- Every component of a pair reads a frame only through `pairLeaves ps`. -/
theorem symbolicOver_pair {ps : Pairs} {pq : PredRE × PredRE} (h : pq ∈ ps) :
    SymbolicOver (pairLeaves ps) pq.1 ∧ SymbolicOver (pairLeaves ps) pq.2 := by
  constructor <;> refine symbolicOver_of_leaves_mem fun φ hφ => ?_ <;>
    exact List.mem_flatMap.mpr ⟨pq, h, List.mem_append.mpr (by simp [hφ])⟩

/-- `cls` covers every inhabited minterm of `L`. -/
def Covers (L : List Pred) (cls : List Value) : Prop :=
  ∀ a : Value, ∃ c ∈ cls, leafSig L c = leafSig L a

/-- ⚑ **`closed_under_symbols`** — closure under the class representatives is closure under EVERY
symbol of the infinite alphabet: a symbol and its class representative have the same derivative
(`der_factors_over`), up to which the representative's derivative pair is in the list. -/
theorem closed_under_symbols {cls : List Value} {ps : Pairs} (hcov : Covers (pairLeaves ps) cls)
    {pq : PredRE × PredRE} (hpq : pq ∈ ps) (hcl : closedAt cls ps pq = true) (a : Value) :
    ∃ pq' ∈ ps, Sim (der a pq.1) pq'.1 ∧ Sim (der a pq.2) pq'.2 := by
  obtain ⟨c, hc, hsig⟩ := hcov a
  have hsym := symbolicOver_pair hpq
  have h1 : der a pq.1 = der c pq.1 := der_factors_over hsig.symm hsym.1
  have h2 : der a pq.2 = der c pq.2 := der_factors_over hsig.symm hsym.2
  rw [h1, h2]
  exact memSim_spec (List.all_eq_true.mp hcl c hc)

/-- The bisimulation argument, generic in the relation the pairs' nullabilities satisfy. By
induction on the word: the empty word reads `null` (invariant under `≅`, `sim_null`), a symbol
moves both sides to a derivative pair that is again in the list up to `≅`. -/
theorem bisim_core (Rel : Bool → Bool → Prop) {cls : List Value} {ps : Pairs}
    (hcov : Covers (pairLeaves ps) cls)
    (hnull : ∀ pq ∈ ps, Rel (null pq.1) (null pq.2))
    (hcl : ∀ pq ∈ ps, closedAt cls ps pq = true) :
    ∀ (w : List Value) (p q : PredRE), (∃ pq ∈ ps, Sim p pq.1 ∧ Sim q pq.2) →
      Rel (derives w p) (derives w q)
  | [], p, q, ⟨pq, hm, hp, hq⟩ => by
    simp only [derives]; rw [sim_null hp, sim_null hq]; exact hnull pq hm
  | a :: w, p, q, ⟨pq, hm, hp, hq⟩ => by
    simp only [derives]
    obtain ⟨pq', hm', h1, h2⟩ := closed_under_symbols hcov hm (hcl pq hm) a
    exact bisim_core Rel hcov hnull hcl w _ _
      ⟨pq', hm', Sim.trans (sim_der hp a) h1, Sim.trans (sim_der hq a) h2⟩

/-- ⚑ **`bisim_sound`** — an accepted inclusion certificate (with covering classes) proves
`L(r) ⊆ L(s)` over the whole infinite alphabet. -/
theorem bisim_sound {cls : List Value} {ps : Pairs} {r s : PredRE}
    (hcov : Covers (pairLeaves ps) cls) (h : bisimOk cls ps r s = true) :
    ∀ w, Matches w r → Matches w s := by
  simp only [bisimOk, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨hroot, hall⟩ := h
  intro w hw
  rw [← correctness] at hw ⊢
  refine bisim_core (fun x y => x = true → y = true) hcov ?_ (fun pq hm => (hall pq hm).2) w r s
    (memSim_spec hroot) hw
  intro pq hm hx
  rcases (hall pq hm).1 with h | h
  · rw [hx] at h; exact absurd h (by decide)
  · exact h

/-- ⚑ **`bisimEq_sound`** — an accepted equivalence certificate proves `L(r) = L(s)`. -/
theorem bisimEq_sound {cls : List Value} {ps : Pairs} {r s : PredRE}
    (hcov : Covers (pairLeaves ps) cls) (h : bisimEqOk cls ps r s = true) :
    ∀ w, Matches w r ↔ Matches w s := by
  simp only [bisimEqOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨hroot, hall⟩ := h
  intro w
  rw [← correctness, ← correctness]
  have := bisim_core (fun x y => x = y) hcov (fun pq hm => (hall pq hm).1)
    (fun pq hm => (hall pq hm).2) w r s (memSim_spec hroot)
  rw [this]

/-! ## §3 — The classes, computed: the tree's minterm cover. -/

/-- The class representatives for a pair list: the tree's `atomCands` over the (deduplicated) pin
set of its leaves; `none` outside the decidable-leaf fragment (`IsSymbolic`'s vocabulary). -/
def classesOf (ps : Pairs) : Option (List Value) :=
  (atomsOfLeaves? (pairLeaves ps)).map fun A => atomCands A.dedup

theorem classesOf_covers {ps : Pairs} {cls : List Value} (h : classesOf ps = some cls) :
    Covers (pairLeaves ps) cls := by
  unfold classesOf at h
  cases hA : atomsOfLeaves? (pairLeaves ps) with
  | none => rw [hA] at h; cases h
  | some A =>
    rw [hA] at h; cases h
    intro a
    obtain ⟨c, hc, hsig⟩ := (coverOfAtoms A.dedup (pairLeaves ps) (fun φ hφ => by
      obtain ⟨Aφ, h1, h2⟩ := atomsOfLeaves?_spec hA φ hφ
      exact ⟨Aφ, h1, fun x hx => List.mem_dedup.mpr (h2 hx)⟩)).covers a
    exact ⟨c, hc, hsig⟩

/-- **The executable checker**: classes computed, not supplied. -/
def bisimCheck (ps : Pairs) (r s : PredRE) : Bool :=
  match classesOf ps with
  | some cls => bisimOk cls ps r s
  | none => false

def bisimEqCheck (ps : Pairs) (r s : PredRE) : Bool :=
  match classesOf ps with
  | some cls => bisimEqOk cls ps r s
  | none => false

/-- ⚑ **`bisimCheck_sound`** — hypothesis-free. -/
theorem bisimCheck_sound {ps : Pairs} {r s : PredRE} (h : bisimCheck ps r s = true) :
    ∀ w, Matches w r → Matches w s := by
  unfold bisimCheck at h
  split at h
  · rename_i cls hc; exact bisim_sound (classesOf_covers hc) h
  · cases h

theorem bisimEqCheck_sound {ps : Pairs} {r s : PredRE} (h : bisimEqCheck ps r s = true) :
    ∀ w, Matches w r ↔ Matches w s := by
  unfold bisimEqCheck at h
  split at h
  · rename_i cls hc; exact bisimEq_sound (classesOf_covers hc) h
  · cases h

/-! ## §4 — The emitter (untrusted): a worklist exploration that prints the pair list. -/

def explore (cls : List Value) : Nat → Pairs → Pairs → Pairs
  | 0, _, done => done
  | _ + 1, [], done => done
  | n + 1, (p, q) :: todo, done =>
    if memSim done p q then explore cls n todo done
    else explore cls n (todo ++ cls.map fun c => (nrm (der c p), nrm (der c q)))
      (done ++ [(nrm p, nrm q)])

def emitPairs (fuel : Nat) (r s : PredRE) : Pairs :=
  match classesOf [(r, s)] with
  | some cls => explore cls fuel [(r, s)] []
  | none => []

/-! ## §5 — Non-vacuity, falsifiers, counts. -/

namespace Reference

open Dregg2.Crypto.HandlebarsGuarded (noDoubleBraceRE braceP)

/-- `star any`: every word. -/
def anyStar : PredRE := .star PredRE.any
/-- Two single-symbol regexes on the tiny alphabet `t = 0` / `t = 1`. -/
def aRE : PredRE := .sym (.symEq "t" 0)
def bRE : PredRE := .sym (.symEq "t" 1)
/-- The reassociated policy regex (the shape of `HandlebarsGuardDecision.nodbAssoc`). -/
def nodbAssoc : PredRE :=
  .neg (.cat (.cat anyStar (.sym braceP)) (.cat (.sym braceP) anyStar))

/-- The emitted certificates. -/
def nodbPairs : Pairs := emitPairs 200 noDoubleBraceRE anyStar
def abPairs : Pairs := emitPairs 50 aRE (.alt aRE bRE)
def assocPairs : Pairs := emitPairs 200 noDoubleBraceRE nodbAssoc

-- (a) ACCEPTED: the policy regex is included in `star any`; `a ⊆ a | b`; the reassociated policy
-- is EQUIVALENT to the policy. Kernel-decided.
theorem nodb_accepted : bisimCheck nodbPairs noDoubleBraceRE anyStar = true := by decide +kernel
theorem ab_accepted : bisimCheck abPairs aRE (.alt aRE bRE) = true := by decide +kernel
theorem assoc_equiv_accepted : bisimEqCheck assocPairs noDoubleBraceRE nodbAssoc = true := by
  decide +kernel

/-- ⚑ **Non-vacuity**, as terms through the soundness theorems. -/
theorem nodb_subset_anyStar : ∀ w, Matches w noDoubleBraceRE → Matches w anyStar :=
  bisimCheck_sound nodb_accepted
theorem a_subset_ab : ∀ w, Matches w aRE → Matches w (.alt aRE bRE) :=
  bisimCheck_sound ab_accepted
theorem nodb_equiv_assoc : ∀ w, Matches w noDoubleBraceRE ↔ Matches w nodbAssoc :=
  bisimEqCheck_sound assoc_equiv_accepted

-- (b) dropping the ROOT pair is refused; dropping an interior DERIVATIVE pair is refused (closure).
theorem nodb_dropRoot_refused :
    bisimCheck (nodbPairs.eraseIdx 0) noDoubleBraceRE anyStar = false := by decide +kernel
theorem nodb_dropDerivative_refused :
    bisimCheck (nodbPairs.eraseIdx 3) noDoubleBraceRE anyStar = false := by decide +kernel
theorem ab_dropDerivative_refused :
    bisimCheck (abPairs.eraseIdx 1) aRE (.alt aRE bRE) = false := by decide +kernel

-- (c) the inclusion is not an equivalence: the same pair list fails the `↔` checker, and the reverse
-- inclusion `star any ⊆ noDoubleBraceRE` has no certificate from the emitter.
theorem nodb_not_equiv_refused :
    bisimEqCheck nodbPairs noDoubleBraceRE anyStar = false := by decide +kernel
theorem anyStar_sub_nodb_refused :
    bisimCheck (emitPairs 200 anyStar noDoubleBraceRE) anyStar noDoubleBraceRE = false := by
  decide +kernel

/-- (d) The WEAKER checker: the same closure and the same computed classes, with the nullability
check forgotten. -/
def bisimNoNullable (cls : List Value) (ps : Pairs) (r s : PredRE) : Bool :=
  memSim ps r s && ps.all fun pq => closedAt cls ps pq

def bisimNoNullableCheck (ps : Pairs) (r s : PredRE) : Bool :=
  match classesOf ps with
  | some cls => bisimNoNullable cls ps r s
  | none => false

/-- The false inclusion `any ⊆ ε`. -/
def anyEpsPairs : Pairs := emitPairs 50 PredRE.any .ε

theorem anyEps_accepted_by_noNullable : bisimNoNullableCheck anyEpsPairs PredRE.any .ε = true := by
  decide +kernel
theorem anyEps_refused : bisimCheck anyEpsPairs PredRE.any .ε = false := by decide +kernel

/-- The inclusion `any ⊆ ε` really is false: the one-letter word `[record []]`. -/
theorem any_not_subset_eps : ¬ ∀ w, Matches w PredRE.any → Matches w .ε := by
  intro h
  have := h [.record []] ((correctness _ _).mp (by decide))
  exact absurd ((correctness _ _).mpr this) (by decide)

-- The same split on a policy-sized instance: `a | b ⊆ a` is false (the word `[t = 1]`).
theorem ab_sub_a_refused :
    bisimCheck (emitPairs 50 (.alt aRE bRE) aRE) (.alt aRE bRE) aRE = false := by decide +kernel
theorem ab_sub_a_accepted_by_noNullable :
    bisimNoNullableCheck (emitPairs 50 (.alt aRE bRE) aRE) (.alt aRE bRE) aRE = true := by
  decide +kernel

-- Compiled mirrors of the kernel verdicts.
#guard bisimCheck nodbPairs noDoubleBraceRE anyStar
#guard bisimCheck abPairs aRE (.alt aRE bRE)
#guard bisimEqCheck assocPairs noDoubleBraceRE nodbAssoc
#guard !bisimCheck (nodbPairs.eraseIdx 0) noDoubleBraceRE anyStar
#guard !bisimCheck (nodbPairs.eraseIdx 3) noDoubleBraceRE anyStar
#guard bisimNoNullableCheck anyEpsPairs PredRE.any .ε && !bisimCheck anyEpsPairs PredRE.any .ε

/-! ### Counts, pinned: `|pairs| · |classes|` derivative-pair lookups per certificate. -/

def lookups (ps : Pairs) : Nat := ps.length * ((classesOf ps).map List.length).getD 0

#guard nodbPairs.length == 11
#guard (classesOf nodbPairs).map List.length == some 2
#guard lookups nodbPairs == 22
#guard abPairs.length == 4
#guard (classesOf abPairs).map List.length == some 3
#guard lookups abPairs == 12
#guard assocPairs.length == 11
#guard lookups assocPairs == 22
#guard anyEpsPairs.length == 3
#guard lookups anyEpsPairs == 3

end Reference

/-! ## §6 — axiom tripwires. -/

#assert_all_clean [simDecide_sound, memSim_spec, symbolicOver_pair, closed_under_symbols, bisim_core,
  bisim_sound, bisimEq_sound, classesOf_covers, bisimCheck_sound, bisimEqCheck_sound,
  Reference.nodb_accepted, Reference.ab_accepted, Reference.assoc_equiv_accepted,
  Reference.nodb_subset_anyStar, Reference.a_subset_ab, Reference.nodb_equiv_assoc,
  Reference.nodb_dropRoot_refused, Reference.nodb_dropDerivative_refused,
  Reference.ab_dropDerivative_refused, Reference.nodb_not_equiv_refused,
  Reference.anyStar_sub_nodb_refused, Reference.anyEps_accepted_by_noNullable,
  Reference.anyEps_refused, Reference.any_not_subset_eps, Reference.ab_sub_a_refused,
  Reference.ab_sub_a_accepted_by_noNullable]

end BisimCert

end Dregg2.Crypto.Deriv
