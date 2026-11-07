/-
# Dregg2.Crypto.Deriv.Thompson — Stage 4, the LEGACY Thompson-subset path: BOTH halves CLOSED.
# Subset/determinization correctness via mathlib; Thompson-construction correctness via an explicit
# Lean Thompson ε-NFA + structural-induction proof. Matching faithfulness is now end-to-end.

`Powerset.lean` closed faithfulness for the DEPLOYED *derivative* determinizer (`derivative.rs::Re::
compile`), whose `step` IS the Brzozowski derivative, so its table agrees with `derives` BY
CONSTRUCTION. Its closing note named the one piece still open: the LEGACY complement-free path
`compiler.rs::pattern_to_nfa().determinize()` — a Thompson ε-NFA construction followed by the
ε-closure subset (powerset) construction — instantiates the same faithfulness contract only via the
"residual-language = Brzozowski-derivative" bridge, i.e.

  Thompson-construction correctness   ∘   subset-construction correctness.

This module CLOSES the right factor — subset-construction correctness — end-to-end, and ISOLATES the
left factor as a single, precisely-stated obligation `ThompsonRecognizes`.

## What is closed (the subset/determinization half)

`compiler.rs::Nfa::determinize` (`dfa/src/compiler.rs:296`) is the textbook ε-closure powerset
construction: DFA states are ε-closed sets of NFA states, `step S b = εclosure (⋃_{s∈S} δ(s,b))`,
`start = εclosure {nfaStart}`, `accept S = (nfaAccept ∈ S)`, with the flat table laid out as
`transitions[state*256+byte]`. That construction is **already verified in mathlib**, in two proven
edges we IMPORT (not re-prove):

  * `εNFA.toNFA_correct` — ε-elimination: `M.toNFA.accepts = M.accepts` (the ε-closure is sound);
  * `NFA.toDFA_correct`  — the subset construction: `N.toDFA.accepts = N.accepts`.

`compiler.rs`'s `determinize` IS `M.toNFA.toDFA` (ε-closure folded into the powerset step). We model
the deployed flat-table fold `Dfa::matches` as our `TableDfa` (exactly as `TableDfa.lean` does for the
derivative path) via `ofDFA`, prove the fold agrees with mathlib's `DFA.eval`, and chain:

  `determinizedTable M . accepts w  ↔  w ∈ M.accepts`     (`determinizedTable_accepts`)

So given ONLY that the Thompson ε-NFA recognizes the right language, the deployed determinized table
is faithful to the denotational spec `Matches` — `legacy_determinized_faithful`, via the keystone
`derives ↔ Matches` (`Deriv.correctness`).

## What is closed (the Thompson-construction half — NOW DISCHARGED)

`ThompsonRecognizes M R := ∀ w, w ∈ M.accepts ↔ derives w R = true` is exactly Thompson-construction
correctness: that `pattern_to_nfa p`'s ε-NFA accepts exactly the language of `p`'s `PredRE`. Mathlib
provides NO regex→ε-NFA Thompson construction (it connects regexes to languages via Brzozowski
derivatives, NOT via Thompson), so the construction AND its correctness are built here from the
`εNFA.IsPath` primitives:

  * `thompson : PredRE → εNFA Value (TState R)` — the explicit Thompson ε-NFA mirroring
    `compiler.rs::pattern_to_nfa` (`empty`/`single_byte`/`concat`/`union`/`star`), `Set`-valued
    transitions (the ε-join edges as `Prop` conditions — no `DecidableEq` needed);
  * a generic composition toolkit (`isPath_embed`, `isPath_sink`, `isPath_from_inr`, `region_escape`);
  * the per-constructor language equalities (`accepts_eps`/`_sym`/`_alt`/`_cat`/`_star`), assembled by
    `accepts_correct : IsThompson R → (w ∈ (thompson R).accepts ↔ Matches w R)`.

The historically "months-scale" case — `star`'s ε-loop — is `region_escape` (peel the first sub-run
`s0⇝f0`, sound because `f0`'s only star-edges are ε-exits, `tStep_accept_empty`) plus strong induction
on the path length (`star_decomp`). The result: `thompson_recognizes` closes `ThompsonRecognizes` for
the full Thompson fragment, and `legacy_determinized_faithful_thompson` makes the deployed legacy path
faithful to `Matches` END-TO-END, no longer modulo an assumed factor.

`inter`/`neg` are EXCLUDED from `IsThompson` deliberately: the deployed `compiler.rs::pattern_to_nfa`
(`:692`, "Complement has no Thompson-NFA constructor") routes them through the derivative determinizer
(`Powerset.lean`), NOT Thompson — so the fragment proved here is exactly the one Thompson realizes.

The canonical single-symbol automaton `symENfa φ` (the 2-state `s --φ--> a` machine) and its
`symENfa_recognizes` proof are retained below as a self-contained worked witness.

The in-circuit `Dfa.lean` cascade is untouched; the determinized-state space here is `Set σ` (the
canonical subset-construction state), related to the deployed integer state IDs by a bijection exactly
as `Powerset.lean`'s `decode` relates residuals to integer IDs — and `tableDfa_faithful'` is opaque to
the state representation, so the relabeling is immaterial.

`#assert_axioms`-clean, `sorry`-free.
-/
import Mathlib.Computability.EpsilonNFA
import Dregg2.Crypto.Deriv.TableDfa
import Dregg2.Crypto.Deriv.Correctness

namespace Dregg2.Crypto.Deriv

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra (Pred)
open Set

namespace PredRE

/-! ## Bridging a (mathlib) `DFA` to our flat-table `TableDfa` — the deployed `Dfa::matches` fold. -/

/-- **`ofDFA D`** — view a mathlib `DFA Value S` as our `TableDfa S Value` (the deployed
`compiler.rs::Dfa`'s flat `step`/`start`/`accept`). The transition FUNCTION, start, and accept set
carry over directly; `TableDfa.runState` is `DFA.evalFrom` (both `List.foldl step`). -/
def ofDFA {S : Type} (D : DFA Value S) : TableDfa S Value where
  step := D.step
  start := D.start
  accept := fun s => s ∈ D.accept

/-- The flat-table fold IS mathlib's `DFA.evalFrom` (both fold `step` along the word). -/
theorem ofDFA_runState {S : Type} (D : DFA Value S) (q : S) (w : List Value) :
    (ofDFA D).runState q w = D.evalFrom q w := by
  induction w generalizing q with
  | nil => rfl
  | cons a as ih => exact ih (D.step q a)

/-- `ofDFA`'s acceptance is mathlib's `DFA.accepts`. So our deployed-table model recognizes exactly
the language the mathlib `DFA` does. -/
theorem ofDFA_accepts {S : Type} (D : DFA Value S) (w : List Value) :
    (ofDFA D).accepts w ↔ w ∈ D.accepts := by
  unfold TableDfa.accepts
  rw [ofDFA_runState]
  exact Iff.rfl

/-! ## The deployed determinized table — `compiler.rs::Nfa::determinize` as `M.toNFA.toDFA`. -/

/-- **`determinizedTable M`** — the flat table the LEGACY path emits for the Thompson ε-NFA `M`:
the ε-closure powerset construction `compiler.rs::Nfa::determinize`, modelled as the verified mathlib
pipeline `M.toNFA.toDFA` (ε-elimination then subset construction) viewed as a `TableDfa`. States are
ε-closed sets of NFA states (`Set σ`) — the canonical subset-construction state; the deployed integer
state IDs are a bijective relabeling, immaterial to `tableDfa_faithful'`. -/
def determinizedTable {σ : Type} (M : εNFA Value σ) : TableDfa (Set σ) Value :=
  ofDFA M.toNFA.toDFA

/-- **`determinizedTable_accepts`** — the SUBSET-CONSTRUCTION half, CLOSED: the determinized table
recognizes EXACTLY the Thompson ε-NFA's language. This is `compiler.rs::Nfa::determinize`'s
correctness, discharged by mathlib's verified `εNFA.toNFA_correct` (ε-elimination) and
`NFA.toDFA_correct` (subset construction) — no re-proof, the textbook theorems. -/
theorem determinizedTable_accepts {σ : Type} (M : εNFA Value σ) (w : List Value) :
    (determinizedTable M).accepts w ↔ w ∈ M.accepts := by
  rw [determinizedTable, ofDFA_accepts]
  rw [show M.toNFA.toDFA.accepts = M.accepts by rw [NFA.toDFA_correct, εNFA.toNFA_correct]]

/-! ## The keystone, generic over the state representation, and the legacy close. -/

/-- **`tableDfa_faithful'`** — the `TableDfa.tableDfa_faithful` keystone, stated generically over the
state space `State` (the deployed legacy table's states are `Set σ`, not `PredRE`): any table whose
`accepts` agrees with `derives` everywhere decides EXACTLY `Matches R`. Construction- AND
representation-opaque; chains `Deriv.correctness`. -/
theorem tableDfa_faithful' {State : Type} (td : TableDfa State Value) (R : PredRE)
    (hagree : ∀ w, td.accepts w ↔ derives w R = true) (w : List Value) :
    td.accepts w ↔ Matches w R := by
  rw [hagree w, correctness]

/-- **`ThompsonRecognizes M R`** — the Thompson-construction obligation: the Thompson ε-NFA `M`
(`compiler.rs::pattern_to_nfa p`) recognizes exactly the language of `R = p`'s `PredRE`. This IS
Thompson-construction correctness (design §3.2 step 3) — the inductive `accepts (thompson R) =
Matches R` over the concat/star/union sub-automata, which mathlib does NOT provide.

It is **CLOSED** below for the full Thompson fragment (`ε`/`sym`/`alt`/`cat`/`star`) by
`thompson_recognizes`, via an explicit Lean Thompson construction `thompson : PredRE → εNFA` that
mirrors `pattern_to_nfa` and a kernel-clean structural-induction proof `accepts_correct`. -/
def ThompsonRecognizes {σ : Type} (M : εNFA Value σ) (R : PredRE) : Prop :=
  ∀ w, w ∈ M.accepts ↔ derives w R = true

/-- **`legacy_determinized_faithful`** — the LEGACY-path close, MODULO the Thompson factor: IF the
Thompson ε-NFA `M` recognizes `R`'s language (`ThompsonRecognizes`), THEN the deployed determinized
table is faithful to the denotational spec `Matches R`. The subset-construction factor is fully
discharged (`determinizedTable_accepts`, via mathlib); only `ThompsonRecognizes` is assumed.

So the legacy complement-free path is covered by the faithfulness keystone EXACTLY up to the
named-and-isolated Thompson-construction obligation. -/
theorem legacy_determinized_faithful {σ : Type} (M : εNFA Value σ) (R : PredRE)
    (hM : ThompsonRecognizes M R) (w : List Value) :
    (determinizedTable M).accepts w ↔ Matches w R :=
  tableDfa_faithful' (determinizedTable M) R
    (fun w => (determinizedTable_accepts M w).trans (hM w)) w

/-! ## Non-vacuity — the canonical single-symbol Thompson automaton satisfies the obligation.

`compiler.rs::Nfa::single_byte`/`byte_range` build a 2-state machine `start --byte--> accept`. Its
`PredRE`-leaf analog is `symENfa φ`: states `Bool` (`false` = start, `true` = accept), one transition
`false --(a : leaf φ a)--> true`, no ε-edges. We prove `ThompsonRecognizes (symENfa φ) (.sym φ)` in
full — so the closed subset half provably carries a GENUINE Thompson automaton to `Matches`-faithful,
and the `ThompsonRecognizes` contract is inhabited, not vacuous. -/

/-- The canonical single-symbol Thompson ε-NFA: `false --(leaf φ)--> true`, no ε. -/
def symENfa (φ : Pred) : εNFA Value Bool where
  step s o := match s, o with
    | false, some a => if leaf φ a then {true} else (∅ : Set Bool)
    | _, _ => (∅ : Set Bool)
  start := {false}
  accept := {true}

@[simp] theorem symENfa_step_true (φ : Pred) (o : Option Value) :
    (symENfa φ).step true o = (∅ : Set Bool) := rfl
@[simp] theorem symENfa_step_false_none (φ : Pred) :
    (symENfa φ).step false none = (∅ : Set Bool) := rfl
@[simp] theorem symENfa_step_false_some (φ : Pred) (a : Value) :
    (symENfa φ).step false (some a) = (if leaf φ a then {true} else (∅ : Set Bool)) := rfl

/-- No transition leaves `true` — any path FROM `true` is the empty path. -/
theorem symENfa_path_true {φ : Pred} {u : Bool} {x : List (Option Value)}
    (h : (symENfa φ).IsPath true u x) : u = true ∧ x = [] := by
  cases h with
  | nil => exact ⟨rfl, rfl⟩
  | cons t s u a x' hstep _ => exact absurd hstep (by simp)

/-- A path `false ⇝ true` is exactly a single symbol `a` satisfying the leaf. -/
theorem symENfa_path_false_true {φ : Pred} {x : List (Option Value)}
    (h : (symENfa φ).IsPath false true x) : ∃ a, x = [some a] ∧ leaf φ a = true := by
  cases h with
  | cons t s u a x' hstep hpath =>
    cases a with
    | none => exact absurd hstep (by simp)
    | some av =>
      by_cases hl : leaf φ av
      · rw [symENfa_step_false_some, if_pos hl, mem_singleton_iff] at hstep
        subst hstep
        obtain ⟨_, hx'⟩ := symENfa_path_true hpath
        subst hx'
        exact ⟨av, rfl, hl⟩
      · rw [symENfa_step_false_some, if_neg hl] at hstep
        exact absurd hstep (by simp)

/-- `symENfa φ` recognizes exactly singletons `[a]` with `leaf φ a`. -/
theorem symENfa_accepts (φ : Pred) (w : List Value) :
    w ∈ (symENfa φ).accepts ↔ ∃ a, w = [a] ∧ leaf φ a = true := by
  rw [εNFA.mem_accepts_iff_exists_path]
  constructor
  · rintro ⟨s₁, s₂, x', hs₁, hs₂, hred, hpath⟩
    rw [show (symENfa φ).start = ({false} : Set Bool) from rfl, mem_singleton_iff] at hs₁
    rw [show (symENfa φ).accept = ({true} : Set Bool) from rfl, mem_singleton_iff] at hs₂
    subst hs₁; subst hs₂
    obtain ⟨av, hx', hl⟩ := symENfa_path_false_true hpath
    subst hx'
    refine ⟨av, ?_, hl⟩
    simpa using hred.symm
  · rintro ⟨a, rfl, hl⟩
    refine ⟨false, true, [some a], rfl, rfl, by simp, ?_⟩
    rw [εNFA.isPath_singleton, symENfa_step_false_some, if_pos hl]
    exact mem_singleton _

/-- **`symENfa_recognizes`** — the obligation, DISCHARGED for the canonical single-symbol Thompson
automaton: `symENfa φ` recognizes exactly `(.sym φ)`'s language. So `ThompsonRecognizes` is inhabited
by a real Thompson construction. -/
theorem symENfa_recognizes (φ : Pred) : ThompsonRecognizes (symENfa φ) (.sym φ) := by
  intro w
  rw [symENfa_accepts, correctness, Matches]

/-! ### The closed subset half carries the canonical Thompson automaton to `Matches`-faithful. -/

section Witnesses

private def frameK7 : Value := .record [("k", .sym 7)]
private def isK7 : Pred := .symEq "k" 7

-- The determinized table of the single-symbol Thompson automaton is faithful to `Matches`…
example (w : List Value) :
    (determinizedTable (symENfa isK7)).accepts w ↔ Matches w (.sym isK7) :=
  legacy_determinized_faithful (symENfa isK7) (.sym isK7) (symENfa_recognizes isK7) w

-- …it ACCEPTS a real matching word (the determinized subset table, Set-states and all)…
example : (determinizedTable (symENfa isK7)).accepts [frameK7] := by
  rw [legacy_determinized_faithful (symENfa isK7) (.sym isK7) (symENfa_recognizes isK7), Matches]
  exact ⟨frameK7, rfl, by decide⟩

-- …and REJECTS the empty word (≠ a singleton) — both polarities, non-vacuous.
example : ¬ (determinizedTable (symENfa isK7)).accepts [] := by
  rw [legacy_determinized_faithful (symENfa isK7) (.sym isK7) (symENfa_recognizes isK7), Matches]
  rintro ⟨a, h, _⟩
  exact absurd h (by simp)

end Witnesses


/-! ## CLOSING the Thompson factor — an explicit Thompson construction over `PredRE`.

The section below mirrors `compiler.rs::pattern_to_nfa` AS A LEAN ε-NFA `thompson : PredRE → εNFA`
and discharges `ThompsonRecognizes` for the full Thompson fragment by structural induction. Mathlib
provides NO regex→ε-NFA Thompson construction, so the construction and its correctness are built
here from the `εNFA.IsPath` primitives: a small generic composition toolkit (`isPath_embed`,
`isPath_sink`, `isPath_from_inr`, `region_escape`) then the per-constructor language equalities. The
historically "months-scale" case — `star`'s ε-loop — is the `region_escape` + path-length strong
induction in `star_decomp`. -/

/-! ## The Thompson ε-NFA over `PredRE` — state types. -/

/-- State space of `thompson R`, mirroring `compiler.rs::pattern_to_nfa`. Each sub-expression has a
distinguished start/accept; leaves use `Bool` (`false`=start, `true`=accept); `inter`/`neg` are NOT in
the Thompson fragment (they go through the derivative determinizer) — dummy `Bool` with no edges. -/
def TState : PredRE → Type
  | .ε        => Bool
  | .sym _    => Bool
  | .alt l r  => Sum Bool (Sum (TState l) (TState r))
  | .cat l r  => Sum (TState l) (TState r)
  | .star r   => Sum Bool (TState r)
  | .inter _ _ => Bool
  | .neg _    => Bool

/-- The distinguished start state of `thompson R`. -/
def tStart : (R : PredRE) → TState R
  | .ε        => false
  | .sym _    => false
  | .alt _ _  => Sum.inl false
  | .cat l _  => Sum.inl (tStart l)
  | .star _   => Sum.inl false
  | .inter _ _ => false
  | .neg _    => false

/-- The distinguished accept state of `thompson R`. -/
def tAccept : (R : PredRE) → TState R
  | .ε        => true
  | .sym _    => true
  | .alt _ _  => Sum.inl true
  | .cat _ r  => Sum.inr (tAccept r)
  | .star _   => Sum.inl true
  | .inter _ _ => true
  | .neg _    => true

/-- The transition relation of `thompson R`. `Set`-valued (so the ε-join edges are stated as `Prop`
conditions — no `DecidableEq (TState R)` needed). -/
def tStep : (R : PredRE) → TState R → Option Value → Set (TState R)
  | .ε,       s, o => {t | s = false ∧ o = none ∧ t = true}
  | .sym φ,   s, o => {t | s = false ∧ t = true ∧ ∃ a, o = some a ∧ leaf φ a = true}
  | .alt l r, s, o =>
      match s with
      | Sum.inl false =>           -- new start: ε to both sub-starts
          {t | o = none ∧ (t = Sum.inr (Sum.inl (tStart l)) ∨ t = Sum.inr (Sum.inr (tStart r)))}
      | Sum.inl true => ∅          -- new accept: sink
      | Sum.inr (Sum.inl x) =>     -- left sub
          (fun u => Sum.inr (Sum.inl u)) '' (tStep l x o)
            ∪ {t | x = tAccept l ∧ o = none ∧ t = Sum.inl true}
      | Sum.inr (Sum.inr y) =>     -- right sub
          (fun u => Sum.inr (Sum.inr u)) '' (tStep r y o)
            ∪ {t | y = tAccept r ∧ o = none ∧ t = Sum.inl true}
  | .cat l r, s, o =>
      match s with
      | Sum.inl x => (fun u => Sum.inl u) '' (tStep l x o)
            ∪ {t | x = tAccept l ∧ o = none ∧ t = Sum.inr (tStart r)}
      | Sum.inr y => (fun u => Sum.inr u) '' (tStep r y o)
  | .star r,  s, o =>
      match s with
      | Sum.inl false => {t | o = none ∧ (t = Sum.inr (tStart r) ∨ t = Sum.inl true)}
      | Sum.inl true => ∅
      | Sum.inr y => (fun u => Sum.inr u) '' (tStep r y o)
            ∪ {t | y = tAccept r ∧ o = none ∧ (t = Sum.inr (tStart r) ∨ t = Sum.inl true)}
  | .inter _ _, _, _ => ∅
  | .neg _,     _, _ => ∅

/-- The Thompson ε-NFA itself: singleton start/accept. -/
def thompson (R : PredRE) : εNFA Value (TState R) where
  step := tStep R
  start := {tStart R}
  accept := {tAccept R}

/-- The accept state is a SINK in every sub-machine: no sub-transitions leave `tAccept R`. The crux
fact that makes the `star` ε-loop tractable (the only way out of a sub-accept is the star's ε-edges). -/
theorem tStep_accept_empty : ∀ (R : PredRE) (o : Option Value), tStep R (tAccept R) o = ∅
  | .ε, o => by ext t; simp [tStep, tAccept]
  | .sym _, o => by ext t; simp [tStep, tAccept]
  | .alt _ _, o => rfl
  | .cat _ r, o => by
      show ((fun u => Sum.inr u) '' (tStep r (tAccept r) o)) = ∅
      rw [tStep_accept_empty r o, image_empty]
  | .star _, o => rfl
  | .inter _ _, o => rfl
  | .neg _, o => rfl

/-! ## Characterizing acceptance via a single start→accept path. -/

/-- `thompson R` accepts `w` iff there is a path from `tStart R` to `tAccept R` labelled `w`. -/
theorem thompson_accepts_iff (R : PredRE) (w : List Value) :
    w ∈ (thompson R).accepts ↔
      ∃ x', x'.reduceOption = w ∧ (thompson R).IsPath (tStart R) (tAccept R) x' := by
  rw [εNFA.mem_accepts_iff_exists_path]
  constructor
  · rintro ⟨s₁, s₂, x', hs₁, hs₂, hr, hp⟩
    rw [show (thompson R).start = ({tStart R} : Set _) from rfl, mem_singleton_iff] at hs₁
    rw [show (thompson R).accept = ({tAccept R} : Set _) from rfl, mem_singleton_iff] at hs₂
    subst hs₁; subst hs₂; exact ⟨x', hr, hp⟩
  · rintro ⟨x', hr, hp⟩
    exact ⟨tStart R, tAccept R, x', rfl, rfl, hr, hp⟩

/-! ## Generic ε-NFA path lemmas (composition toolkit). -/

/-- **Embed**: a path in `N` lifts along ANY state injection `ι` whose `ι`-image of `N`'s steps is
contained in `M`'s steps. (The backward/constructive direction of every combinator.) -/
theorem isPath_embed {σ τ : Type} {M : εNFA Value σ} {N : εNFA Value τ} (ι : τ → σ)
    (h : ∀ x o, ι '' (N.step x o) ⊆ M.step (ι x) o)
    {a b : τ} {p} (hp : N.IsPath a b p) : M.IsPath (ι a) (ι b) p := by
  induction hp with
  | nil s => exact .nil _
  | cons t s u o x hstep _ ih => exact .cons _ _ _ _ _ (h _ _ (Set.mem_image_of_mem ι hstep)) ih

/-- **Sink**: a state with no outgoing transitions only admits the empty path. -/
theorem isPath_sink {σ : Type} {M : εNFA Value σ} {s : σ} (hs : ∀ o, M.step s o = ∅)
    {u p} (hp : M.IsPath s u p) : u = s ∧ p = [] := by
  cases hp with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ _ _ _ _ hstep _ => rw [hs] at hstep; exact absurd hstep (by simp)

/-- **Right confinement**: in a sum machine whose `inr`-steps stay in the `inr` region (image of
`N`'s steps), any path from an `inr` state stays in `inr` and is an `N`-path. -/
theorem isPath_from_inr {σ₁ σ₂ : Type} {M : εNFA Value (σ₁ ⊕ σ₂)} {N : εNFA Value σ₂}
    (h : ∀ y o, M.step (Sum.inr y) o ⊆ (fun u => Sum.inr u) '' (N.step y o)) :
    ∀ (p : List (Option Value)) (a : σ₂) (u : σ₁ ⊕ σ₂),
      M.IsPath (Sum.inr a) u p → ∃ b, u = Sum.inr b ∧ N.IsPath a b p := by
  intro p
  induction p with
  | nil => intro a u hp; rw [εNFA.isPath_nil] at hp; exact ⟨a, hp.symm, .nil a⟩
  | cons o rest ih =>
      intro a u hp
      cases hp with
      | cons t _ _ _ _ hstep hpath =>
          obtain ⟨t', ht', rfl⟩ := h a o hstep
          obtain ⟨b, rfl, hN⟩ := ih t' u hpath
          exact ⟨b, rfl, .cons _ _ _ _ _ ht' hN⟩

/-- **Region escape**: in a machine with a sub-region embedded by `ι` whose only edges leaving the
region's representative `N`-steps are ε-edges out of the sub-accept `f0` into `Ex`, a path from
`ι a` either stays an `N`-path, or splits as `(N-path a⇝f0) · none · (tail from an exit state)`. -/
theorem region_escape {σ τ : Type} {M : εNFA Value σ} {N : εNFA Value τ}
    (ι : τ → σ) (f0 : τ) (Ex : Set σ)
    (hsplit : ∀ y o t, t ∈ M.step (ι y) o →
        t ∈ ι '' (N.step y o) ∨ (y = f0 ∧ o = none ∧ t ∈ Ex)) :
    ∀ (p : List (Option Value)) (a : τ) (u : σ),
      M.IsPath (ι a) u p →
        (∃ b, u = ι b ∧ N.IsPath a b p) ∨
        (∃ p₁ p₂ z, p = p₁ ++ none :: p₂ ∧ N.IsPath a f0 p₁ ∧ z ∈ Ex ∧ M.IsPath z u p₂) := by
  intro p
  induction p with
  | nil => intro a u hp; rw [εNFA.isPath_nil] at hp; exact Or.inl ⟨a, hp.symm, .nil a⟩
  | cons o rest ih =>
      intro a u hp
      cases hp with
      | cons t _ _ _ _ hstep hpath =>
          rcases hsplit a o t hstep with ⟨t', ht', rfl⟩ | ⟨rfl, rfl, hEx⟩
          · rcases ih t' u hpath with ⟨b, rfl, hN⟩ | ⟨p₁, p₂, z, hp', hN1, hz, hM2⟩
            · exact Or.inl ⟨b, rfl, .cons _ _ _ _ _ ht' hN⟩
            · exact Or.inr ⟨o :: p₁, p₂, z, by rw [hp', List.cons_append],
                .cons _ _ _ _ _ ht' hN1, hz, hM2⟩
          · exact Or.inr ⟨[], rest, t, rfl, .nil a, hEx, hpath⟩

/-! ## The leaf cases — `ε` and `sym`. -/

theorem accepts_eps (w : List Value) : w ∈ (thompson .ε).accepts ↔ Matches w .ε := by
  rw [thompson_accepts_iff, Matches]
  constructor
  · rintro ⟨x', rfl, hp⟩
    cases hp with
    | cons t _ _ o rest hstep hpath =>
        simp only [thompson, tStep, mem_setOf_eq] at hstep
        obtain ⟨-, rfl, rfl⟩ := hstep
        obtain ⟨-, rfl⟩ := isPath_sink (M := thompson .ε) (s := true)
          (fun o => tStep_accept_empty .ε o) hpath
        rfl
  · rintro rfl
    exact ⟨[none], rfl, .cons _ _ _ _ _ ⟨rfl, rfl, rfl⟩ (.nil true)⟩

theorem accepts_sym (φ : Pred) (w : List Value) :
    w ∈ (thompson (.sym φ)).accepts ↔ Matches w (.sym φ) := by
  rw [thompson_accepts_iff, Matches]
  constructor
  · rintro ⟨x', rfl, hp⟩
    cases hp with
    | cons t _ _ o rest hstep hpath =>
        simp only [thompson, tStep, mem_setOf_eq] at hstep
        obtain ⟨-, rfl, a, rfl, hl⟩ := hstep
        obtain ⟨-, rfl⟩ := isPath_sink (M := thompson (.sym φ)) (s := true)
          (fun o => tStep_accept_empty (.sym φ) o) hpath
        exact ⟨a, rfl, hl⟩
  · rintro ⟨a, rfl, hl⟩
    exact ⟨[some a], rfl, .cons _ _ _ _ _ ⟨rfl, rfl, a, rfl, hl⟩ (.nil true)⟩

/-! ## Alternation. -/

theorem accepts_alt (l r : PredRE)
    (ihl : ∀ w, w ∈ (thompson l).accepts ↔ Matches w l)
    (ihr : ∀ w, w ∈ (thompson r).accepts ↔ Matches w r)
    (w : List Value) : w ∈ (thompson (.alt l r)).accepts ↔ Matches w (.alt l r) := by
  set M := thompson (.alt l r) with hM
  have hsplitL : ∀ y o t, t ∈ M.step (Sum.inr (Sum.inl y)) o →
      t ∈ (fun u => Sum.inr (Sum.inl u)) '' ((thompson l).step y o) ∨
        (y = tAccept l ∧ o = none ∧ t ∈ ({Sum.inl true} : Set (TState (.alt l r)))) := by
    intro y o t ht
    rcases ht with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.1, h.2.1, h.2.2⟩
  have hsplitR : ∀ y o t, t ∈ M.step (Sum.inr (Sum.inr y)) o →
      t ∈ (fun u => Sum.inr (Sum.inr u)) '' ((thompson r).step y o) ∨
        (y = tAccept r ∧ o = none ∧ t ∈ ({Sum.inl true} : Set (TState (.alt l r)))) := by
    intro y o t ht
    rcases ht with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.1, h.2.1, h.2.2⟩
  rw [thompson_accepts_iff, Matches]
  constructor
  · rintro ⟨x', rfl, hp⟩
    cases hp with
    | cons t _ _ o rest hstep hpath =>
        simp only [thompson, tStep] at hstep
        obtain ⟨rfl, hcase⟩ := hstep
        rw [List.reduceOption_cons_of_none]
        rcases hcase with rfl | rfl
        · rcases region_escape (fun u => Sum.inr (Sum.inl u)) (tAccept l)
              ({Sum.inl true} : Set (TState (.alt l r))) hsplitL rest (tStart l) (Sum.inl true) hpath with
            ⟨b, hb, _⟩ | ⟨p₁, p₂, z, hsplitp, hN1, hz, hM2⟩
          · exact absurd hb (by simp)
          · obtain rfl : z = Sum.inl true := hz
            obtain ⟨-, rfl⟩ := isPath_sink (M := M) (s := Sum.inl true) (by intro o; rfl) hM2
            subst hsplitp
            left
            rw [← ihl, thompson_accepts_iff]
            refine ⟨p₁, ?_, hN1⟩
            simp [List.reduceOption_append, List.reduceOption_cons_of_none]
        · rcases region_escape (fun u => Sum.inr (Sum.inr u)) (tAccept r)
              ({Sum.inl true} : Set (TState (.alt l r))) hsplitR rest (tStart r) (Sum.inl true) hpath with
            ⟨b, hb, _⟩ | ⟨p₁, p₂, z, hsplitp, hN1, hz, hM2⟩
          · exact absurd hb (by simp)
          · obtain rfl : z = Sum.inl true := hz
            obtain ⟨-, rfl⟩ := isPath_sink (M := M) (s := Sum.inl true) (by intro o; rfl) hM2
            subst hsplitp
            right
            rw [← ihr, thompson_accepts_iff]
            refine ⟨p₁, ?_, hN1⟩
            simp [List.reduceOption_append, List.reduceOption_cons_of_none]
  · rintro (hl | hr)
    · rw [← ihl, thompson_accepts_iff] at hl
      obtain ⟨p₁, hr1, hpath1⟩ := hl
      refine ⟨[none] ++ (p₁ ++ [none]), ?_, ?_⟩
      · simp [List.reduceOption_append, List.reduceOption_cons_of_none, hr1]
      · refine (εNFA.isPath_append _).mpr ?_
        refine ⟨Sum.inr (Sum.inl (tStart l)), by refine (εNFA.isPath_singleton _).mpr ?_; exact ⟨rfl, Or.inl rfl⟩, ?_⟩
        refine (εNFA.isPath_append _).mpr ?_
        refine ⟨Sum.inr (Sum.inl (tAccept l)),
          isPath_embed (fun u => Sum.inr (Sum.inl u)) (fun x o => Set.subset_union_left) hpath1, ?_⟩
        refine (εNFA.isPath_singleton _).mpr ?_
        exact Or.inr ⟨rfl, rfl, rfl⟩
    · rw [← ihr, thompson_accepts_iff] at hr
      obtain ⟨p₁, hr1, hpath1⟩ := hr
      refine ⟨[none] ++ (p₁ ++ [none]), ?_, ?_⟩
      · simp [List.reduceOption_append, List.reduceOption_cons_of_none, hr1]
      · refine (εNFA.isPath_append _).mpr ?_
        refine ⟨Sum.inr (Sum.inr (tStart r)), by refine (εNFA.isPath_singleton _).mpr ?_; exact ⟨rfl, Or.inr rfl⟩, ?_⟩
        refine (εNFA.isPath_append _).mpr ?_
        refine ⟨Sum.inr (Sum.inr (tAccept r)),
          isPath_embed (fun u => Sum.inr (Sum.inr u)) (fun x o => Set.subset_union_left) hpath1, ?_⟩
        refine (εNFA.isPath_singleton _).mpr ?_
        exact Or.inr ⟨rfl, rfl, rfl⟩

/-! ## Concatenation. -/

theorem accepts_cat (l r : PredRE)
    (ihl : ∀ w, w ∈ (thompson l).accepts ↔ Matches w l)
    (ihr : ∀ w, w ∈ (thompson r).accepts ↔ Matches w r)
    (w : List Value) : w ∈ (thompson (.cat l r)).accepts ↔ Matches w (.cat l r) := by
  set M := thompson (.cat l r) with hM
  have hsplitC : ∀ y o t, t ∈ M.step (Sum.inl y) o →
      t ∈ (fun u => Sum.inl u) '' ((thompson l).step y o) ∨
        (y = tAccept l ∧ o = none ∧ t ∈ ({Sum.inr (tStart r)} : Set (TState (.cat l r)))) := by
    intro y o t ht
    rcases ht with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.1, h.2.1, h.2.2⟩
  have hinr : ∀ y o, M.step (Sum.inr y) o ⊆ (fun u => Sum.inr u) '' ((thompson r).step y o) :=
    fun y o a ha => ha
  rw [thompson_accepts_iff, Matches]
  constructor
  · rintro ⟨x', rfl, hp⟩
    rcases region_escape (fun u => Sum.inl u) (tAccept l)
        ({Sum.inr (tStart r)} : Set (TState (.cat l r))) hsplitC x' (tStart l)
        (Sum.inr (tAccept r)) hp with
      ⟨b, hb, _⟩ | ⟨p₁, p₂, z, hsplitp, hN1, hz, hM2⟩
    · exact absurd hb (by simp)
    · obtain rfl : z = Sum.inr (tStart r) := hz
      obtain ⟨b, hb, hNr⟩ := isPath_from_inr hinr p₂ (tStart r) (Sum.inr (tAccept r)) hM2
      rw [Sum.inr.injEq] at hb; subst hb
      subst hsplitp
      refine ⟨List.reduceOption p₁, List.reduceOption p₂, ?_, ?_, ?_⟩
      · rw [List.reduceOption_append, List.reduceOption_cons_of_none]
      · exact (ihl _).mp ((thompson_accepts_iff l _).mpr ⟨p₁, rfl, hN1⟩)
      · exact (ihr _).mp ((thompson_accepts_iff r _).mpr ⟨p₂, rfl, hNr⟩)
  · rintro ⟨w₁, w₂, rfl, hl, hr⟩
    rw [← ihl, thompson_accepts_iff] at hl
    rw [← ihr, thompson_accepts_iff] at hr
    obtain ⟨p₁, hr1, hpath1⟩ := hl
    obtain ⟨p₂, hr2, hpath2⟩ := hr
    refine ⟨p₁ ++ none :: p₂, ?_, ?_⟩
    · rw [List.reduceOption_append, List.reduceOption_cons_of_none, hr1, hr2]
    · refine (εNFA.isPath_append _).mpr ?_
      refine ⟨Sum.inl (tAccept l),
        isPath_embed (fun u => Sum.inl u) (fun x o => Set.subset_union_left) hpath1, ?_⟩
      refine εNFA.IsPath.cons _ _ _ _ _ (show Sum.inr (tStart r) ∈ M.step (Sum.inl (tAccept l)) none
          from Or.inr ⟨rfl, rfl, rfl⟩) ?_
      exact isPath_embed (fun u => Sum.inr u) (fun x o a ha => ha) hpath2

/-! ## Kleene star.

The star automaton has a new start `NS = inl false` and accept `NA = inl true`, the sub at
`inr ·`, with ε-edges `NS→s0`, `NS→NA`, `f0→s0` (loop), `f0→NA` (exit). Three pieces close it:
the pure `Matches`/`repeatCat` ↔ list-of-pieces bridge, the constructive path builder, and the
forward ε-loop decomposition (the historically "months-scale" case), discharged via `region_escape`
+ strong induction on the path length. -/

/-- The denotational bridge: a `star`-match is exactly a flattening of finitely many `r`-matches.
Pure `PredRE`/`Matches` lemma (no automata) — `repeatCat`'s power encoding ↔ a list of pieces. -/
theorem star_flatten_iff (r : PredRE) (w : List Value) :
    (∃ ws : List (List Value), w = ws.flatten ∧ ∀ wi ∈ ws, Matches wi r) ↔
    ∃ m, Matches w (repeatCat r m) := by
  constructor
  · rintro ⟨ws, rfl, hall⟩
    induction ws with
    | nil => exact ⟨0, by simp only [List.flatten_nil, repeatCat]; rw [Matches]⟩
    | cons wi rest ih =>
        obtain ⟨m, hm⟩ := ih (fun x hx => hall x (List.mem_cons_of_mem _ hx))
        refine ⟨m + 1, ?_⟩
        simp only [repeatCat]; rw [Matches]
        exact ⟨wi, rest.flatten, by rw [List.flatten_cons], hall wi (by simp), hm⟩
  · rintro ⟨m, hm⟩
    induction m generalizing w with
    | zero =>
        simp only [repeatCat] at hm; rw [Matches] at hm
        exact ⟨[], by rw [hm, List.flatten_nil], by simp⟩
    | succ n ih =>
        simp only [repeatCat] at hm; rw [Matches] at hm
        obtain ⟨w₁, w₂, hsplit, h1, h2⟩ := hm
        obtain ⟨ws', hwf, hall'⟩ := ih w₂ h2
        exact ⟨w₁ :: ws', by rw [List.flatten_cons, ← hwf, hsplit], by
          intro wi hwi; rw [List.mem_cons] at hwi; rcases hwi with rfl | h
          · exact h1
          · exact hall' wi h⟩

/-- **Constructive (backward)**: a list of `r`-acceptances threads into one `s0 ⇝ f0` path of the
star machine, the sub-runs joined by the `f0→s0` ε-loop. -/
theorem star_thread (r : PredRE) : ∀ (ws : List (List Value)), ws ≠ [] →
    (∀ wi ∈ ws, wi ∈ (thompson r).accepts) →
    ∃ q, q.reduceOption = ws.flatten ∧
      (thompson (.star r)).IsPath (Sum.inr (tStart r)) (Sum.inr (tAccept r)) q
  | [], h, _ => absurd rfl h
  | [wi], _, hall => by
      obtain ⟨p, hp1, hpath⟩ := (thompson_accepts_iff r wi).mp (hall wi (by simp))
      refine ⟨p, by simp [hp1], isPath_embed (fun u => Sum.inr u)
        (fun x o => Set.subset_union_left) hpath⟩
  | wi :: w2 :: rest, _, hall => by
      obtain ⟨p, hp1, hpath⟩ := (thompson_accepts_iff r wi).mp (hall wi (by simp))
      obtain ⟨q', hq1, hqpath⟩ :=
        star_thread r (w2 :: rest) (by simp) (fun x hx => hall x (List.mem_cons_of_mem _ hx))
      refine ⟨p ++ none :: q', ?_, ?_⟩
      · simp [List.reduceOption_append, List.reduceOption_cons_of_none, hp1, hq1, List.flatten_cons]
      · refine (εNFA.isPath_append _).mpr ?_
        refine ⟨Sum.inr (tAccept r),
          isPath_embed (fun u => Sum.inr u) (fun x o => Set.subset_union_left) hpath, ?_⟩
        refine εNFA.IsPath.cons _ _ _ _ _
          (show Sum.inr (tStart r) ∈ (thompson (.star r)).step (Sum.inr (tAccept r)) none
            from Or.inr ⟨rfl, rfl, Or.inl rfl⟩) ?_
        exact hqpath

/-- **Forward ε-loop decomposition** (the crux): any `s0 ⇝ NA` path of the star machine splits into
finitely many `r`-acceptances. `region_escape` peels the FIRST sub-run (`s0 ⇝ f0`, no exit before
`f0` because `f0`'s only star-edges are ε-exits), then strong induction on the residual path. -/
theorem star_decomp (r : PredRE) (q : List (Option Value))
    (hp : (thompson (.star r)).IsPath (Sum.inr (tStart r)) (Sum.inl true) q) :
    ∃ ws, q.reduceOption = ws.flatten ∧ ws ≠ [] ∧ ∀ wi ∈ ws, wi ∈ (thompson r).accepts := by
  have hsplitS : ∀ y o t, t ∈ (thompson (.star r)).step (Sum.inr y) o →
      t ∈ (fun u => Sum.inr u) '' ((thompson r).step y o) ∨
        (y = tAccept r ∧ o = none ∧
          t ∈ ({t | t = Sum.inr (tStart r) ∨ t = Sum.inl true} : Set (TState (.star r)))) := by
    intro y o t ht
    rcases ht with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.1, h.2.1, h.2.2⟩
  rcases region_escape (fun u => Sum.inr u) (tAccept r)
      ({t | t = Sum.inr (tStart r) ∨ t = Sum.inl true} : Set (TState (.star r)))
      hsplitS q (tStart r) (Sum.inl true) hp with
    ⟨b, hb, _⟩ | ⟨p₁, p₂, z, hsplitp, hN1, hz, hM2⟩
  · exact absurd hb (by simp)
  · have hv1 : List.reduceOption p₁ ∈ (thompson r).accepts :=
      (thompson_accepts_iff r _).mpr ⟨p₁, rfl, hN1⟩
    rcases hz with rfl | rfl
    · obtain ⟨ws', hflat, _, hall⟩ := star_decomp r p₂ hM2
      refine ⟨List.reduceOption p₁ :: ws', ?_, by simp, ?_⟩
      · rw [hsplitp]
        simp [List.reduceOption_append, List.reduceOption_cons_of_none, hflat, List.flatten_cons]
      · intro wi hwi; rw [List.mem_cons] at hwi; rcases hwi with rfl | hwi
        · exact hv1
        · exact hall wi hwi
    · obtain ⟨-, rfl⟩ := isPath_sink (M := thompson (.star r)) (s := Sum.inl true)
        (by intro o; rfl) hM2
      refine ⟨[List.reduceOption p₁], ?_, by simp, ?_⟩
      · rw [hsplitp]
        simp [List.reduceOption_append, List.reduceOption_cons_of_none]
      · intro wi hwi; rw [List.mem_singleton] at hwi; subst hwi; exact hv1
  termination_by q.length
  decreasing_by
    rw [hsplitp]; simp [List.length_append, List.length_cons]; omega

theorem accepts_star (r : PredRE)
    (ihr : ∀ w, w ∈ (thompson r).accepts ↔ Matches w r)
    (w : List Value) : w ∈ (thompson (.star r)).accepts ↔ Matches w (.star r) := by
  rw [thompson_accepts_iff]
  constructor
  · rintro ⟨x', rfl, hp⟩
    cases hp with
    | cons t _ _ o rest hstep hpath =>
        simp only [thompson, tStep] at hstep
        obtain ⟨rfl, hcase⟩ := hstep
        rw [List.reduceOption_cons_of_none]
        rcases hcase with rfl | rfl
        · obtain ⟨ws, hflat, _, hall⟩ := star_decomp r rest hpath
          rw [Matches, hflat]
          exact (star_flatten_iff r ws.flatten).mp ⟨ws, rfl, fun wi hwi => (ihr wi).mp (hall wi hwi)⟩
        · obtain ⟨-, rfl⟩ := isPath_sink (M := thompson (.star r)) (s := Sum.inl true)
            (by intro o; rfl) hpath
          rw [List.reduceOption_nil, Matches]
          exact ⟨0, by simp only [repeatCat]; rw [Matches]⟩
  · intro hm
    rw [Matches] at hm
    obtain ⟨ws, hwf, hall⟩ := (star_flatten_iff r w).mpr hm
    rcases ws with _ | ⟨wi, rest⟩
    · subst hwf; exact ⟨[none], rfl, .cons _ _ _ _ _ ⟨rfl, Or.inr rfl⟩ (.nil _)⟩
    · obtain ⟨q, hq1, hqpath⟩ := star_thread r (wi :: rest) (by simp)
        (fun x hx => (ihr x).mpr (hall x hx))
      refine ⟨[none] ++ (q ++ [none]), ?_, ?_⟩
      · simp [List.reduceOption_append, List.reduceOption_cons_of_none, hq1, hwf]
      · refine (εNFA.isPath_append _).mpr ?_
        refine ⟨Sum.inr (tStart r), by refine (εNFA.isPath_singleton _).mpr ?_; exact ⟨rfl, Or.inl rfl⟩, ?_⟩
        refine (εNFA.isPath_append _).mpr ?_
        refine ⟨Sum.inr (tAccept r), hqpath, ?_⟩
        refine (εNFA.isPath_singleton _).mpr ?_
        exact Or.inr ⟨rfl, rfl, Or.inr rfl⟩

/-! ## The Thompson fragment and the closed obligation. -/

/-- `IsThompson R` — `R` is built only from the constructors the deployed `pattern_to_nfa` realizes
via the Thompson construction (`ε`, `sym`, `alt`, `cat`, `star`). `inter`/`neg` are EXCLUDED: the
deployed compiler routes them through the derivative determinizer (`compiler.rs:692` — "Complement
has no Thompson-NFA constructor"), NOT Thompson. -/
def IsThompson : PredRE → Prop
  | .ε        => True
  | .sym _    => True
  | .alt l r  => IsThompson l ∧ IsThompson r
  | .cat l r  => IsThompson l ∧ IsThompson r
  | .star r   => IsThompson r
  | .inter _ _ => False
  | .neg _    => False

/-- **`accepts_correct`** — the Thompson construction `thompson R` recognizes EXACTLY the
denotational language `Matches · R`, for every `R` in the Thompson fragment. Structural induction on
`R`, each constructor discharged by its `accepts_<ctor>` composition lemma. -/
theorem accepts_correct : ∀ (R : PredRE), IsThompson R →
    ∀ w, w ∈ (thompson R).accepts ↔ Matches w R
  | .ε, _, w => accepts_eps w
  | .sym φ, _, w => accepts_sym φ w
  | .alt l r, h, w => accepts_alt l r (accepts_correct l h.1) (accepts_correct r h.2) w
  | .cat l r, h, w => accepts_cat l r (accepts_correct l h.1) (accepts_correct r h.2) w
  | .star r, h, w => accepts_star r (accepts_correct r h) w
  | .inter _ _, h, _ => h.elim
  | .neg _, h, _ => h.elim

/-- **`thompson_recognizes`** — `ThompsonRecognizes` CLOSED for the full Thompson fragment: the
explicit Thompson ε-NFA `thompson R` recognizes exactly `derives · R`. Chains `accepts_correct`
(language faithfulness of the construction) with the keystone `correctness` (`derives ↔ Matches`).
So matching-faithfulness is end-to-end for the legacy path, no longer modulo an assumed factor. -/
theorem thompson_recognizes (R : PredRE) (h : IsThompson R) :
    ThompsonRecognizes (thompson R) R := by
  intro w
  rw [accepts_correct R h w]; exact (correctness w R).symm

/-- **`legacy_determinized_faithful_thompson`** — the LEGACY complement-free path, now faithful
END-TO-END (not modulo any assumption): the deployed determinized table of the Thompson ε-NFA for any
Thompson-fragment `R` decides EXACTLY the denotational spec `Matches · R`. The Thompson factor is
`thompson_recognizes`, the subset-construction factor is `determinizedTable_accepts` (mathlib). -/
theorem legacy_determinized_faithful_thompson (R : PredRE) (h : IsThompson R) (w : List Value) :
    (determinizedTable (thompson R)).accepts w ↔ Matches w R :=
  legacy_determinized_faithful (thompson R) R (thompson_recognizes R h) w

end PredRE

end Dregg2.Crypto.Deriv

/-! ## Axiom hygiene. -/

#assert_all_clean [
  Dregg2.Crypto.Deriv.PredRE.ofDFA_accepts,
  Dregg2.Crypto.Deriv.PredRE.determinizedTable_accepts,
  Dregg2.Crypto.Deriv.PredRE.tableDfa_faithful',
  Dregg2.Crypto.Deriv.PredRE.legacy_determinized_faithful,
  Dregg2.Crypto.Deriv.PredRE.symENfa_accepts,
  Dregg2.Crypto.Deriv.PredRE.symENfa_recognizes,
  Dregg2.Crypto.Deriv.PredRE.accepts_correct,
  Dregg2.Crypto.Deriv.PredRE.thompson_recognizes,
  Dregg2.Crypto.Deriv.PredRE.legacy_determinized_faithful_thompson
]
