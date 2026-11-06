/-
# Dregg2.Policy.Elab — the surface means what the engines compute.

Each construct of the policy language elaborates to an object that already exists in the tree:

| surface | object | theorem here |
|---|---|---|
| `pattern P = re` | `Crypto.Deriv.PredRE` over byte frames `⟨"c" ↦ sym b⟩` | `elabRe_semantics` |
| `forbid pattern P in F` | `absenceOf (elabRe re)` = `neg (any* · R · any*)` | `absenceOf_semantics`, `absenceOf_derives` |
| `grammar G { … }` | mathlib `ContextFreeGrammar Nat` (`Crypto/Cfg.lean`'s object) | `elabGrammar_rules`, `dyck_derives` |
| `rule …` | `Datalog.StratifiedCert.SProgram`; positive rules also `FixpointCert.Program` | `elabProgram_pos`, `varIdx_inj` |
| `budget …` | `Aggregates.sumAt` / `FixpointCert.countQ` bound | `BudgetClaim.holds` (definitional) |

**The byte alphabet.** `Deriv.PredRE`'s alphabet is `Exec.Value`, not bytes, and
`PredicateLibrary` has no byte predicates. A byte `b` is the frame `byteFrame b = ⟨"c" ↦ sym b⟩`,
the convention `ZkOracle.frame` and `InjectionGuardCircuit.word` already use; a byte class is
`Pred.symMemberOf "c" (bytes)` (pin-representable, so the minterm cover and the decision procedures
apply); `.` is `Pred.tt`. The semantic theorem quantifies over byte words `w : List Nat` mapped
through `byteFrame`; on non-byte frames the elaborated regex means whatever `Matches` says, and
nothing here is claimed about it.

**`ReSem`** is the textbook semantics of the surface regex (Kleene star as "a concatenation of a
list of matching words"), written independently of `PredRE` so that `elabRe_semantics` is not a
restatement of `Matches`.
-/
import Mathlib.Computability.ContextFreeGrammar
import Dregg2.Crypto.Deriv.Correctness
import Dregg2.Datalog.StratifiedCert
import Dregg2.Datalog.Aggregates
import Dregg2.Policy.Syntax
import Dregg2.Tactics

namespace Dregg2.Policy

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra (Pred)
open Dregg2.Crypto.Deriv
open Dregg2.Crypto.Deriv.PredRE

set_option autoImplicit false

/-! ## §1 The textbook semantics of the surface regex. -/

/-- **`ReSem r w`** — the byte word `w` matches `r`. -/
def ReSem : Re → List Nat → Prop
  | .lit bs, w => w = bs
  | .set ng rs, w => ∃ c, w = [c] ∧ inRanges rs c = !ng
  | .esc e, w => ∃ c, w = [c] ∧ inRanges e.ranges c = true
  | .any, w => ∃ c, w = [c]
  | .alt l r, w => ReSem l w ∨ ReSem r w
  | .inter l r, w => ReSem l w ∧ ReSem r w
  | .cat l r, w => ∃ u v, w = u ++ v ∧ ReSem l u ∧ ReSem r v
  | .neg r, w => ¬ ReSem r w
  | .star r, w => ∃ ws : List (List Nat), w = ws.flatten ∧ ∀ u ∈ ws, ReSem r u
  | .plus r, w => ∃ ws : List (List Nat), ws ≠ [] ∧ w = ws.flatten ∧ ∀ u ∈ ws, ReSem r u
  | .opt r, w => w = [] ∨ ReSem r w
  | .rep r m n, w => ∃ ws : List (List Nat), m ≤ ws.length ∧ ws.length ≤ n ∧ w = ws.flatten ∧
      ∀ u ∈ ws, ReSem r u

/-! ## §2 The elaborator. -/

/-- A byte as an alphabet symbol (`ZkOracle.frame`'s convention). -/
def byteFrame (b : Nat) : Value := .record [("c", .sym b)]

/-- The bytes of inclusive ranges, enumerated. -/
def rangeBytes (rs : List (Nat × Nat)) : List Nat :=
  rs.flatMap (fun p => List.range' p.1 (p.2 + 1 - p.1))

def bytesIn (rs : List (Nat × Nat)) : Pred := .symMemberOf "c" (rangeBytes rs)

/-- `r` repeated at most `k` times. -/
def upTo (r : PredRE) : Nat → PredRE
  | 0 => .ε
  | k + 1 => .alt .ε (.cat r (upTo r k))

/-- **`elabRe`** — a surface regex as a derivative-engine regex. -/
def elabRe : Re → PredRE
  | .lit bs => bs.foldr (fun b acc => .cat (.sym (.symEq "c" b)) acc) .ε
  | .set ng rs => .sym (if ng then .not (bytesIn rs) else bytesIn rs)
  | .esc e => .sym (bytesIn e.ranges)
  | .any => .sym .tt
  | .alt l r => .alt (elabRe l) (elabRe r)
  | .inter l r => .inter (elabRe l) (elabRe r)
  | .cat l r => .cat (elabRe l) (elabRe r)
  | .neg r => .neg (elabRe r)
  | .star r => .star (elabRe r)
  | .plus r => .cat (elabRe r) (.star (elabRe r))
  | .opt r => .alt .ε (elabRe r)
  | .rep r m n => if m ≤ n then .cat (repeatCat (elabRe r) m) (upTo (elabRe r) (n - m)) else bot

/-- **`absenceOf R`** — "no factor of the word matches `R`": the padded complement. -/
def absenceOf (R : PredRE) : PredRE := .neg (.cat (.star any) (.cat R (.star any)))

/-! ## §3 Matching on byte words. -/

section Matching

theorem m_sym (w : List Value) (φ : Pred) : Matches w (.sym φ) ↔ ∃ a, w = [a] ∧ leaf φ a = true := by
  rw [Matches]
theorem m_eps (w : List Value) : Matches w .ε ↔ w = [] := by rw [Matches]
theorem m_alt (w : List Value) (l r : PredRE) : Matches w (.alt l r) ↔ Matches w l ∨ Matches w r := by
  rw [Matches]
theorem m_inter (w : List Value) (l r : PredRE) :
    Matches w (.inter l r) ↔ Matches w l ∧ Matches w r := by rw [Matches]
theorem m_neg (w : List Value) (r : PredRE) : Matches w (.neg r) ↔ ¬ Matches w r := by rw [Matches]
theorem m_star (w : List Value) (r : PredRE) : Matches w (.star r) ↔ ∃ m, Matches w (repeatCat r m) := by
  rw [Matches]
theorem m_cat (w : List Value) (l r : PredRE) :
    Matches w (.cat l r) ↔ ∃ w₁ w₂, w₁ ++ w₂ = w ∧ Matches w₁ l ∧ Matches w₂ r := by rw [Matches]

theorem leaf_member (b : Nat) (s : List Nat) : leaf (.symMemberOf "c" s) (byteFrame b) = s.contains b := by
  simp [leaf, Pred.eval, Value.symField, Value.field, byteFrame]

theorem leaf_symEq (b c : Nat) : leaf (.symEq "c" c) (byteFrame b) = (b == c) := by
  simp [leaf, Pred.eval, Value.symField, Value.field, byteFrame]

theorem leaf_not (φ : Pred) (a : Value) : leaf (.not φ) a = !(leaf φ a) := by simp [leaf, Pred.eval]

theorem leaf_tt (a : Value) : leaf .tt a = true := by simp [leaf, Pred.eval]

theorem mb_sym (w : List Nat) (φ : Pred) :
    Matches (w.map byteFrame) (.sym φ) ↔ ∃ c, w = [c] ∧ leaf φ (byteFrame c) = true := by
  rw [m_sym]
  constructor
  · rintro ⟨a, ha, hl⟩
    obtain ⟨c, rfl, rfl⟩ := List.map_eq_singleton_iff.mp ha
    exact ⟨c, rfl, hl⟩
  · rintro ⟨c, rfl, hl⟩; exact ⟨_, rfl, hl⟩

theorem mb_cat (w : List Nat) (l r : PredRE) :
    Matches (w.map byteFrame) (.cat l r) ↔
      ∃ u v, w = u ++ v ∧ Matches (u.map byteFrame) l ∧ Matches (v.map byteFrame) r := by
  rw [m_cat]
  constructor
  · rintro ⟨w₁, w₂, he, h1, h2⟩
    obtain ⟨u, v, rfl, rfl, rfl⟩ := List.map_eq_append_iff.mp he.symm
    exact ⟨u, v, rfl, h1, h2⟩
  · rintro ⟨u, v, rfl, h1, h2⟩; exact ⟨_, _, by simp, h1, h2⟩

theorem mb_eps (w : List Nat) : Matches (w.map byteFrame) .ε ↔ w = [] := by
  rw [m_eps]; simp

/-- `repeatCat` on byte words: exactly `m` matching pieces. -/
theorem mb_repeat (R : PredRE) (P : List Nat → Prop) (hR : ∀ u, Matches (u.map byteFrame) R ↔ P u) :
    ∀ (m : Nat) (w : List Nat), Matches (w.map byteFrame) (repeatCat R m) ↔
      ∃ ws : List (List Nat), ws.length = m ∧ w = ws.flatten ∧ ∀ u ∈ ws, P u := by
  intro m
  induction m with
  | zero =>
    intro w
    simp only [repeatCat, mb_eps]
    constructor
    · rintro rfl; exact ⟨[], rfl, rfl, by simp⟩
    · rintro ⟨ws, hl, rfl, -⟩; rw [List.length_eq_zero_iff.mp hl]; rfl
  | succ m ih =>
    intro w
    simp only [repeatCat, mb_cat, hR, ih]
    constructor
    · rintro ⟨u, v, rfl, hu, ws, hl, rfl, hws⟩
      refine ⟨u :: ws, by simp [hl], by simp, ?_⟩
      intro x hx; simp only [List.mem_cons] at hx; rcases hx with rfl | hx
      · exact hu
      · exact hws x hx
    · rintro ⟨ws, hl, rfl, hws⟩
      cases ws with
      | nil => simp at hl
      | cons u ws =>
        exact ⟨u, ws.flatten, by simp, hws u List.mem_cons_self, ws, by simpa using hl, rfl,
          fun x hx => hws x (List.mem_cons_of_mem _ hx)⟩

/-- `upTo` on byte words: at most `k` matching pieces. -/
theorem mb_upTo (R : PredRE) (P : List Nat → Prop) (hR : ∀ u, Matches (u.map byteFrame) R ↔ P u) :
    ∀ (k : Nat) (w : List Nat), Matches (w.map byteFrame) (upTo R k) ↔
      ∃ ws : List (List Nat), ws.length ≤ k ∧ w = ws.flatten ∧ ∀ u ∈ ws, P u := by
  intro k
  induction k with
  | zero =>
    intro w
    simp only [upTo, mb_eps]
    constructor
    · rintro rfl; exact ⟨[], le_refl _, rfl, by simp⟩
    · rintro ⟨ws, hl, rfl, -⟩; rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)]; rfl
  | succ k ih =>
    intro w
    simp only [upTo, m_alt, mb_eps, mb_cat, hR, ih]
    constructor
    · rintro (rfl | ⟨u, v, rfl, hu, ws, hl, rfl, hws⟩)
      · exact ⟨[], by simp, rfl, by simp⟩
      · refine ⟨u :: ws, by simp; omega, by simp, ?_⟩
        intro x hx; simp only [List.mem_cons] at hx; rcases hx with rfl | hx
        · exact hu
        · exact hws x hx
    · rintro ⟨ws, hl, rfl, hws⟩
      cases ws with
      | nil => left; rfl
      | cons u ws =>
        right
        exact ⟨u, ws.flatten, by simp, hws u List.mem_cons_self, ws, by simp at hl; omega, rfl,
          fun x hx => hws x (List.mem_cons_of_mem _ hx)⟩

theorem mb_star (R : PredRE) (P : List Nat → Prop) (hR : ∀ u, Matches (u.map byteFrame) R ↔ P u)
    (w : List Nat) : Matches (w.map byteFrame) (.star R) ↔
      ∃ ws : List (List Nat), w = ws.flatten ∧ ∀ u ∈ ws, P u := by
  rw [m_star]
  simp only [mb_repeat R P hR]
  constructor
  · rintro ⟨m, ws, -, h1, h2⟩; exact ⟨ws, h1, h2⟩
  · rintro ⟨ws, h1, h2⟩; exact ⟨ws.length, ws, rfl, h1, h2⟩

theorem contains_rangeBytes (rs : List (Nat × Nat)) (c : Nat) :
    (rangeBytes rs).contains c = inRanges rs c := by
  rw [Bool.eq_iff_iff]
  simp only [rangeBytes, List.contains_iff_mem, List.mem_flatMap, List.mem_range'_1, inRanges,
    List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨p, hp, h1, h2⟩; exact ⟨p, hp, h1, by omega⟩
  · rintro ⟨p, hp, h1, h2⟩; exact ⟨p, hp, h1, by omega⟩

end Matching

/-! ## §4 ⚑ The elaboration theorem. -/

theorem elabRe_lit (bs : List Nat) (w : List Nat) :
    Matches (w.map byteFrame) (elabRe (.lit bs)) ↔ w = bs := by
  induction bs generalizing w with
  | nil => simp only [elabRe, List.foldr_nil, mb_eps]
  | cons b bs ih =>
    simp only [elabRe, List.foldr_cons] at ih ⊢
    rw [mb_cat]
    simp only [mb_sym, leaf_symEq, beq_iff_eq, ih]
    constructor
    · rintro ⟨u, v, rfl, ⟨c, rfl, rfl⟩, rfl⟩; rfl
    · rintro rfl; exact ⟨[b], bs, rfl, ⟨b, rfl, rfl⟩, rfl⟩

/-- ⚑⚑ **`elabRe_semantics`** — on every byte word, the elaborated `PredRE` matches (in the
derivative engine's denotation `Matches`) exactly when the surface regex matches in the textbook
semantics `ReSem`. With `Deriv.correctness`, the derivative MATCHER `derives` decides `ReSem`
(`elabRe_derives`). -/
theorem elabRe_semantics : ∀ (r : Re) (w : List Nat), Matches (w.map byteFrame) (elabRe r) ↔ ReSem r w := by
  intro r
  induction r with
  | lit bs => intro w; rw [elabRe_lit]; rfl
  | set ng rs =>
    intro w
    simp only [elabRe, mb_sym, ReSem]
    cases ng
    · simp only [Bool.false_eq_true, if_false, bytesIn, leaf_member, contains_rangeBytes, Bool.not_false]
    · simp only [if_true, bytesIn, leaf_not, leaf_member, contains_rangeBytes, Bool.not_true,
        Bool.not_eq_true']
  | esc e =>
    intro w
    simp only [elabRe, mb_sym, ReSem, bytesIn, leaf_member, contains_rangeBytes]
  | any => intro w; simp only [elabRe, mb_sym, ReSem, leaf_tt, and_true]
  | alt l r ihl ihr => intro w; simp only [elabRe, m_alt, ihl, ihr, ReSem]
  | inter l r ihl ihr => intro w; simp only [elabRe, m_inter, ihl, ihr, ReSem]
  | cat l r ihl ihr => intro w; simp only [elabRe, mb_cat, ihl, ihr, ReSem]
  | neg r ih => intro w; simp only [elabRe, m_neg, ih, ReSem]
  | star r ih => intro w; simp only [elabRe, ReSem]; exact mb_star _ _ ih w
  | plus r ih =>
    intro w
    simp only [elabRe, mb_cat, ih, mb_star _ _ ih, ReSem]
    constructor
    · rintro ⟨u, v, rfl, hu, ws, rfl, hws⟩
      refine ⟨u :: ws, by simp, by simp, ?_⟩
      intro x hx; simp only [List.mem_cons] at hx; rcases hx with rfl | hx
      · exact hu
      · exact hws x hx
    · rintro ⟨ws, hne, rfl, hws⟩
      cases ws with
      | nil => exact absurd rfl hne
      | cons u ws => exact ⟨u, ws.flatten, by simp, hws u List.mem_cons_self, ws, rfl,
          fun x hx => hws x (List.mem_cons_of_mem _ hx)⟩
  | opt r ih => intro w; simp only [elabRe, m_alt, mb_eps, ih, ReSem]
  | rep r m n ih =>
    intro w
    simp only [elabRe, ReSem]
    split
    · rename_i hmn
      rw [mb_cat]
      simp only [mb_repeat _ _ ih, mb_upTo _ _ ih]
      constructor
      · rintro ⟨u, v, rfl, ⟨ws1, hl1, rfl, h1⟩, ⟨ws2, hl2, rfl, h2⟩⟩
        refine ⟨ws1 ++ ws2, by simp; omega, by simp; omega, by simp, ?_⟩
        intro x hx; rcases List.mem_append.mp hx with hx | hx
        · exact h1 x hx
        · exact h2 x hx
      · rintro ⟨ws, hl1, hl2, rfl, hws⟩
        refine ⟨(ws.take m).flatten, (ws.drop m).flatten, by
          rw [← List.flatten_append, List.take_append_drop], ⟨ws.take m, by simp; omega, rfl,
            fun x hx => hws x (List.mem_of_mem_take hx)⟩,
          ⟨ws.drop m, by simp; omega, rfl, fun x hx => hws x (List.mem_of_mem_drop hx)⟩⟩
    · rename_i hmn
      constructor
      · intro h; exact absurd h (matches_bot _)
      · rintro ⟨ws, h1, h2, -⟩; omega

/-- **`elabRe_derives`** — the derivative matcher decides the surface semantics. -/
theorem elabRe_derives (r : Re) (w : List Nat) :
    derives (w.map byteFrame) (elabRe r) = true ↔ ReSem r w := by
  rw [correctness, elabRe_semantics]

theorem any_star_all (w : List Value) : Matches w (.star any) := by
  rw [m_star]
  refine ⟨w.length, ?_⟩
  induction w with
  | nil => simp [repeatCat, m_eps]
  | cons a as ih =>
    simp only [List.length_cons, repeatCat]
    rw [m_cat]
    exact ⟨[a], as, rfl, by rw [m_sym]; exact ⟨a, rfl, leaf_tt a⟩, ih⟩

/-- ⚑ **`absenceOf_semantics`** — `forbid pattern P` means: no factor of the byte word matches `P`. -/
theorem absenceOf_semantics (r : Re) (w : List Nat) :
    Matches (w.map byteFrame) (absenceOf (elabRe r)) ↔ ¬ ∃ x y z, w = x ++ y ++ z ∧ ReSem r y := by
  simp only [absenceOf, m_neg]
  apply not_congr
  rw [mb_cat]
  constructor
  · rintro ⟨x, v, rfl, -, hv⟩
    rw [mb_cat] at hv
    obtain ⟨y, z, rfl, hy, -⟩ := hv
    exact ⟨x, y, z, by simp, (elabRe_semantics r y).mp hy⟩
  · rintro ⟨x, y, z, rfl, hy⟩
    refine ⟨x, y ++ z, by simp, any_star_all _, ?_⟩
    rw [mb_cat]
    exact ⟨y, z, rfl, (elabRe_semantics r y).mpr hy, any_star_all _⟩

/-- The one-line connection to `derives_neg`: the absence verdict is the negated factor search. -/
theorem absenceOf_derives (R : PredRE) (w : List Value) :
    derives w (absenceOf R) = !(derives w (.cat (.star any) (.cat R (.star any)))) :=
  derives_neg w _

/-! ## §5 Grammars → mathlib `ContextFreeGrammar`. -/

def elabGSym : GSym → List (Symbol Nat String)
  | .nt n => [.nonterminal n]
  | .t bs => bs.map .terminal

def elabAlt (a : List GSym) : List (Symbol Nat String) := a.flatMap elabGSym

/-- The rule list of a grammar body. -/
def grammarRules (ps : List Prod) : List (ContextFreeRule Nat String) :=
  ps.flatMap (fun p => p.alts.map (fun a => ⟨p.lhs, elabAlt a⟩))

/-- **`elabGrammar`** — terminals are bytes, nonterminals are names, the start symbol is the first
production's left-hand side (the grammar's own name when the body is empty). -/
def elabGrammar (name : String) (ps : List Prod) : ContextFreeGrammar Nat where
  NT := String
  initial := (ps.head?.map Prod.lhs).getD name
  rules := (grammarRules ps).toFinset

theorem elabGrammar_rules (name : String) (ps : List Prod) (r : ContextFreeRule Nat String) :
    r ∈ (elabGrammar name ps).rules ↔ ∃ p ∈ ps, ∃ a ∈ p.alts, r = ⟨p.lhs, elabAlt a⟩ := by
  show r ∈ (grammarRules ps).toFinset ↔ _
  rw [List.mem_toFinset]
  simp only [grammarRules, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨p, hp, a, ha, rfl⟩; exact ⟨p, hp, a, ha, rfl⟩
  · rintro ⟨p, hp, a, ha, rfl⟩; exact ⟨p, hp, a, ha, rfl⟩

/-- The single-nesting bracket grammar `S -> "[" S "]" | ε` (the `Cfg.Reference.dyck` shape). -/
def dyckProds : List Prod := [⟨"S", [[.t [91], .nt "S", .t [93]], []]⟩]

/-- Non-vacuity: `"[]"` is in the elaborated grammar's language (a derivation, kernel-checked). -/
theorem dyck_derives : [91, 93] ∈ (elabGrammar "dyck" dyckProds).language := by
  have r1 : (⟨"S", [.terminal 91, .nonterminal "S", .terminal 93]⟩ : ContextFreeRule Nat String) ∈
      (elabGrammar "dyck" dyckProds).rules := by
    rw [elabGrammar_rules]; exact ⟨_, List.mem_singleton_self _, _, List.mem_cons_self, rfl⟩
  have r2 : (⟨"S", []⟩ : ContextFreeRule Nat String) ∈ (elabGrammar "dyck" dyckProds).rules := by
    rw [elabGrammar_rules]; exact ⟨_, List.mem_singleton_self _, [], by simp [dyckProds], rfl⟩
  show (elabGrammar "dyck" dyckProds).Derives [.nonterminal "S"] [.terminal 91, .terminal 93]
  have w1 := ContextFreeRule.rewrites_of_exists_parts
    (⟨"S", [.terminal 91, .nonterminal "S", .terminal 93]⟩ : ContextFreeRule Nat String) [] []
  have w2 := ContextFreeRule.rewrites_of_exists_parts
    (⟨"S", []⟩ : ContextFreeRule Nat String) [.terminal 91] [.terminal 93]
  simp only [List.nil_append, List.append_nil, List.cons_append] at w1 w2
  have s1 : (elabGrammar "dyck" dyckProds).Produces [.nonterminal "S"]
      [.terminal 91, .nonterminal "S", .terminal 93] := ⟨_, r1, w1⟩
  have s2 : (elabGrammar "dyck" dyckProds).Produces [.terminal 91, .nonterminal "S", .terminal 93]
      [.terminal 91, .terminal 93] := ⟨_, r2, w2⟩
  exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single s1) s2

/-! ## §6 Rules → `StratifiedCert.SProgram` (and `FixpointCert.Program` for the positive fragment). -/

/-- Predicate names in order of first appearance (heads and bodies, rule by rule). -/
def predNames (rs : List Rule) : List String :=
  (rs.flatMap (fun r => r.head.pred :: r.body.map (·.atom.pred))).eraseDups

/-- A rule's variables in order of first appearance. -/
def ruleVarNames (r : Rule) : List String :=
  ((r.head :: r.body.map (·.atom)).flatMap (fun a => a.args.filterMap (fun x => match x with
    | .var v => some v | .int _ => none))).eraseDups

def varIdx (vs : List String) (v : String) : Nat := vs.idxOf v

/-- Distinct variables of a rule get distinct indices. -/
theorem varIdx_inj {vs : List String} {a b : String} (ha : a ∈ vs) (h : varIdx vs a = varIdx vs b) :
    a = b := by
  unfold varIdx at h
  have hlt : vs.idxOf a < vs.length := List.idxOf_lt_length_iff.mpr ha
  have hb : b ∈ vs := by
    by_contra hb
    rw [List.idxOf_eq_length hb] at h; omega
  have := List.getElem_idxOf hlt
  have hb' := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hb)
  simp only [h] at this
  rw [← this, hb']

def elabTerm (vs : List String) : Arg → Datalog.FixpointCert.Term
  | .var v => .var (varIdx vs v)
  | .int z => .const z

def elabAtom (ps vs : List String) (a : Atom) : Datalog.FixpointCert.Atom :=
  ⟨ps.idxOf a.pred, a.args.map (elabTerm vs)⟩

def elabLit (ps vs : List String) (l : Lit) : Datalog.StratifiedCert.Lit :=
  if l.neg then .neg (elabAtom ps vs l.atom) else .pos (elabAtom ps vs l.atom)

def elabSRule (ps : List String) (r : Rule) : Datalog.StratifiedCert.SRule :=
  let vs := ruleVarNames r
  ⟨elabAtom ps vs r.head, r.body.map (elabLit ps vs)⟩

/-- **`elabProgram`** — rules as a stratified program, with the predicate numbering. -/
def elabProgram (rs : List Rule) : Datalog.StratifiedCert.SProgram × List String :=
  let ps := predNames rs
  (rs.map (elabSRule ps), ps)

/-- **`elabRules`** — the positive fragment as a `FixpointCert.Program`; a negated literal is an
error naming its rule (negation goes through `elabProgram`, i.e. `StratifiedCert.SRule`). -/
def elabRules (rs : List Rule) : Except String Datalog.FixpointCert.Program :=
  if rs.all (fun r => r.body.all (fun l => !l.neg)) then
    .ok ((elabProgram rs).1.map Datalog.StratifiedCert.SRule.toRule)
  else .error "negated literal: use elabProgram (StratifiedCert.SRule)"

/-- On positive rules the two elaborations agree: the stratified rule forgets to the positive one,
and every body literal is `pos`. -/
theorem elabProgram_pos (ps : List String) (r : Rule) (hpos : r.body.all (fun l => !l.neg) = true) :
    ∀ l ∈ (elabSRule ps r).body, ∃ a, l = .pos a := by
  intro l hl
  simp only [elabSRule, List.mem_map] at hl
  obtain ⟨l', hl', rfl⟩ := hl
  have := (List.all_eq_true.mp hpos) l' hl'
  simp only [Bool.not_eq_true'] at this
  exact ⟨elabAtom ps (ruleVarNames r) l'.atom, by simp [elabLit, this]⟩

/-- A stratification by predicate rank: `rank head ≥ rank (positive body)`,
`rank head > rank (negated body)`, iterated to a fixpoint; `none` when there is a cycle through
negation (the rank would exceed the number of predicates). -/
def predRanks (P : Datalog.StratifiedCert.SProgram) (npreds : Nat) : Option (List Nat) :=
  let step (rk : List Nat) : List Nat :=
    P.foldl (fun rk r =>
      let need := r.body.foldl (fun m l => match l with
        | .pos a => max m (rk.getD a.pred 0)
        | .neg a => max m (rk.getD a.pred 0 + 1)) 0
      rk.set r.head.pred (max (rk.getD r.head.pred 0) need)) rk
  let rk := (List.range (npreds + 1)).foldl (fun rk _ => step rk) (List.replicate npreds 0)
  if step rk == rk && rk.all (· ≤ npreds) then some rk else none

/-- Rule indices grouped by the rank of their head, lowest first (lane A's `Strata`). -/
def strataOf (P : Datalog.StratifiedCert.SProgram) (npreds : Nat) : Option Datalog.StratifiedCert.Strata :=
  (predRanks P npreds).map fun rk =>
    let top := rk.foldl max 0
    ((List.range (top + 1)).map fun k =>
      (List.range P.length).filter fun i => (P[i]?.map (fun r => rk.getD r.head.pred 0)) == some k)
    |>.filter (· ≠ [])

/-! ## §7 Budgets and policy claims. -/

/-- An elaborated budget: an aggregate over a predicate's facts, bounded above. -/
structure BudgetClaim where
  agg : Agg
  pred : Nat
  bound : Nat
  deriving Repr

/-- What a budget claims about a database of facts (`Aggregates.sumAt`, `FixpointCert.countQ`). -/
def BudgetClaim.holds (b : BudgetClaim) (db : List Datalog.FixpointCert.Fact) : Prop :=
  match b.agg with
  | .sum _ i => Datalog.Aggregates.sumAt db b.pred i ≤ b.bound
  | .count _ => Datalog.FixpointCert.countQ db b.pred ≤ b.bound

def elabBudget (ps : List String) (agg : Agg) (bound : Nat) : BudgetClaim :=
  let p := match agg with | .sum p _ => p | .count p => p
  ⟨agg, ps.idxOf p, bound⟩

/-- An elaborated claim of a `policy` block. -/
inductive ElabClaim where
  | absence (field : String) (R : PredRE)
  | whole (field : String) (R : PredRE)
  | countZero (pred : Nat)
  | countPos (pred : Nat)
  | budget (b : BudgetClaim)

/-- What a policy claims of a record (its fields, as byte words) and a derived database. -/
def ElabClaim.holds (fields : String → List Nat) (db : List Datalog.FixpointCert.Fact) : ElabClaim → Prop
  | .absence f R => derives ((fields f).map byteFrame) R = true
  | .whole f R => derives ((fields f).map byteFrame) R = true
  | .countZero p => Datalog.FixpointCert.countQ db p = 0
  | .countPos p => 0 < Datalog.FixpointCert.countQ db p
  | .budget b => b.holds db

/-- Resolve a policy block's names against the file. -/
def elabClaims (p : Policy) (cs : List Claim) : Except String (List ElabClaim) :=
  let rules := p.decls.filterMap (fun d => match d with | .rule r => some r | _ => none)
  let ps := predNames rules
  let findPat (n : String) : Except String Re :=
    match p.decls.findSome? (fun d => match d with
      | .pattern m r => if m = n then some r else none | _ => none) with
    | some r => .ok r
    | none => .error s!"unknown pattern `{n}`"
  let findPred (n : String) : Except String Nat :=
    if n ∈ ps then .ok (ps.idxOf n) else .error s!"unknown predicate `{n}`"
  cs.mapM fun c => match c with
    | .forbidPattern n f => do let r ← findPat n; pure (.absence f (absenceOf (elabRe r)))
    | .requirePattern n f => do let r ← findPat n; pure (.whole f (elabRe r))
    | .forbidRule n => do pure (.countZero (← findPred n))
    | .requireRule n => do pure (.countPos (← findPred n))
    | .requireBudget n =>
      match p.decls.findSome? (fun d => match d with
        | .budget m a b => if m = n then some (a, b) else none | _ => none) with
      | some (a, b) => pure (.budget (elabBudget ps a b))
      | none => .error s!"unknown budget `{n}`"

/-! ## §8 Falsifiers (compiled evaluation) — the elaborated regexes admit and reject real bytes. -/

def bytesOf (s : String) : List Nat := s.toUTF8.toList.map (·.toNat)

-- `"sk-" \w{2,3}` admits `sk-ab`, rejects `sk-a` (too short) and `sk-a!` (`!` is not `\w`).
#guard derives ((bytesOf "sk-ab").map byteFrame) (elabRe (.cat (.lit (bytesOf "sk-")) (.rep (.esc .word) 2 3)))
#guard !derives ((bytesOf "sk-a").map byteFrame) (elabRe (.cat (.lit (bytesOf "sk-")) (.rep (.esc .word) 2 3)))
#guard !derives ((bytesOf "sk-a!").map byteFrame) (elabRe (.cat (.lit (bytesOf "sk-")) (.rep (.esc .word) 2 3)))
-- absence of `{{`: admits `a { b`, rejects `x {{ y`.
#guard derives ((bytesOf "a { b").map byteFrame) (absenceOf (elabRe (.lit (bytesOf "{{"))))
#guard !derives ((bytesOf "x {{ y").map byteFrame) (absenceOf (elabRe (.lit (bytesOf "{{"))))
-- a negated class is a byte complement: `[^a]` admits `b`, rejects `a` and the empty word.
#guard derives ((bytesOf "b").map byteFrame) (elabRe (.set true [(97, 97)]))
#guard !derives ((bytesOf "a").map byteFrame) (elabRe (.set true [(97, 97)]))
#guard !derives [] (elabRe (.set true [(97, 97)]))
-- `{3,2}` is empty.
#guard !derives ((bytesOf "aa").map byteFrame) (elabRe (.rep (.lit [97]) 3 2))

-- Stratification: `active(K) :- issued(K), !revoked(K).` is stratified (revoked below active);
-- `p :- !p` is not.
#guard (strataOf (elabProgram [⟨⟨"active", [.var "K"]⟩, [⟨false, ⟨"issued", [.var "K"]⟩⟩,
    ⟨true, ⟨"revoked", [.var "K"]⟩⟩]⟩]).1 3).isSome
#guard (strataOf (elabProgram [⟨⟨"p", []⟩, [⟨true, ⟨"p", []⟩⟩]⟩]).1 1).isNone
#guard (match strataOf (elabProgram [⟨⟨"active", [.var "K"]⟩, [⟨false, ⟨"issued", [.var "K"]⟩⟩,
    ⟨true, ⟨"revoked", [.var "K"]⟩⟩]⟩]).1 3 with
  | some st => Datalog.StratifiedCert.stratifiedB (elabProgram [⟨⟨"active", [.var "K"]⟩,
      [⟨false, ⟨"issued", [.var "K"]⟩⟩, ⟨true, ⟨"revoked", [.var "K"]⟩⟩]⟩]).1 st
  | none => false)
-- Positive rules elaborate to `FixpointCert.Rule`; a negated literal is refused there.
#guard (elabRules [⟨⟨"path", [.var "X", .var "Y"]⟩, [⟨false, ⟨"edge", [.var "X", .var "Y"]⟩⟩]⟩]).toOption ==
  some [⟨⟨0, [.var 0, .var 1]⟩, [⟨1, [.var 0, .var 1]⟩]⟩]
#guard (elabRules [⟨⟨"p", []⟩, [⟨true, ⟨"q", []⟩⟩]⟩]).toOption.isNone

#assert_all_clean [elabRe_semantics, elabRe_derives, elabRe_lit, mb_repeat, mb_upTo, mb_star,
  absenceOf_semantics, absenceOf_derives, any_star_all, elabGrammar_rules, dyck_derives, varIdx_inj,
  elabProgram_pos, contains_rangeBytes]

end Dregg2.Policy
