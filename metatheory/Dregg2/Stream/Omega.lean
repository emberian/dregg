/-
# Dregg2.Stream.Omega: the ω-semantics of `Stream.Core`'s automata, and the verdict theorems

The objects are `Core`'s (`DOmega`, `scan`, `VCert`, `verdictOf`); this file gives them their infinite
meaning and proves what a finite prefix may say about it.

* **ω-words and runs.** `OWord Sym := ℕ → Sym`; `DOmega.run A σ n` is the state after `n` symbols;
  `Accepts A .buchi σ` is "the run is in `F` infinitely often", `Accepts A .coBuchi σ` its negation.
* **The receipt counter IS the acceptance condition's finite approximant.** `run_eq_exec` and
  `scan_prefix` tie `Core.scan` to the infinite run; `buchi_iff_count_unbounded`: a Büchi automaton
  accepts `σ` iff the count of marked positions in `(0, n]` is unbounded in `n`;
  `coBuchi_iff_count_bounded` dually. `lastMark_spec`: no marked state after `lastMark`, and
  `lastMark_marked`: a positive `lastMark` is itself marked. So `n − lastMark` is exactly the length of
  the current unmarked stretch (for the demo policy: an upper bound on the age of the oldest open
  prompt, and after a trip, the time since the trip).
* **Verdicts.** `VCert.Valid`: `dead` and `good` are closed under every transition, and (Büchi) `dead`
  avoids `F` and `good` is inside `F` (co-Büchi: the reverse). `verdict_viol_sound`: a `viol` verdict on
  a prefix means every infinite extension is rejected (the prefix is a bad prefix);
  `verdict_sat_sound` dually; `verdict_monotone`: a definite verdict never changes on extension, so a
  `viol` never becomes `sat` (or `unknown`).
* **Safety ∩ liveness.** `prodSafety S L`: a safety monitor (absorbing bad set) times a Büchi
  automaton; `prod_accepts_iff`: the product accepts iff no prefix trips the monitor AND `L` accepts
  (Alpern–Schneider's decomposition, for this construction); `prodVCert_valid`: its tripped states
  are a valid dead set.
* **The flag-DFA mutant** is refuted in `Stream.ClaudePolicy` on the demo automaton (a marked state is
  not acceptance; reaching `F` once is not Büchi acceptance).

Axioms: `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem.
-/
import Dregg2.Stream.Core
import Dregg2.Lightclient.MMR

namespace Dregg2.Stream

variable {Q Sym : Type}

/-- An infinite word. -/
abbrev OWord (Sym : Type) := ℕ → Sym

/-- `σ` extends the finite word `u`. -/
def Extends (σ : OWord Sym) (u : List Sym) : Prop := ∀ i (h : i < u.length), σ i = u[i]

/-- The length-`n` prefix of `σ`. -/
def prefixOf (σ : OWord Sym) (n : ℕ) : List Sym := (List.range n).map σ

/-- `p` holds infinitely often. -/
def InfOften (p : ℕ → Prop) : Prop := ∀ N, ∃ n, N ≤ n ∧ p n

namespace DOmega

/-- The state after `n` symbols of `σ`, from `q`. -/
def runFrom (A : DOmega Q Sym) (q : Q) (σ : OWord Sym) : ℕ → Q
  | 0 => q
  | n + 1 => A.step (A.runFrom q σ n) (σ n)

def run (A : DOmega Q Sym) (σ : OWord Sym) : ℕ → Q := A.runFrom A.start σ

/-- **The acceptance condition, stated.** Büchi: marked infinitely often. Co-Büchi: not. -/
def Accepts (A : DOmega Q Sym) : Cond → OWord Sym → Prop
  | .buchi, σ => InfOften fun n => A.mark (A.run σ n) = true
  | .coBuchi, σ => ¬ InfOften fun n => A.mark (A.run σ n) = true

/-- The number of marked positions in `(0, n]` of the run: what the receipt counter claims. -/
def marks (A : DOmega Q Sym) (σ : OWord Sym) : ℕ → ℕ
  | 0 => 0
  | n + 1 => A.marks σ n + if A.mark (A.run σ (n + 1)) then 1 else 0

end DOmega

/-! ## Prefixes -/

theorem prefixOf_succ (σ : OWord Sym) (n : ℕ) : prefixOf σ (n + 1) = prefixOf σ n ++ [σ n] := by
  simp [prefixOf, List.range_succ]

@[simp] theorem prefixOf_length (σ : OWord Sym) (n : ℕ) : (prefixOf σ n).length = n := by
  simp [prefixOf]

theorem extends_prefixOf {σ : OWord Sym} {u : List Sym} (h : Extends σ u) :
    prefixOf σ u.length = u := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [prefixOf, h i h2]

theorem extends_prefixOf_self (σ : OWord Sym) (n : ℕ) : Extends σ (prefixOf σ n) := by
  intro i h
  simp [prefixOf]

/-- `σ` extends `u ++ v` only if it extends `u`. -/
theorem extends_of_append {σ : OWord Sym} {u v : List Sym} (h : Extends σ (u ++ v)) : Extends σ u := by
  intro i hi
  rw [h i (by simp; omega), List.getElem_append_left hi]

namespace DOmega

variable (A : DOmega Q Sym)

/-- The infinite run's `n`-th state is the finite run over the `n`-prefix. -/
theorem runFrom_eq_exec (q : Q) (σ : OWord Sym) (n : ℕ) :
    A.runFrom q σ n = A.exec q (prefixOf σ n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [runFrom, ih, exec, prefixOf_succ, List.foldl_append]

theorem run_eq_exec {σ : OWord Sym} {u : List Sym} (h : Extends σ u) :
    A.run σ u.length = A.exec A.start u := by
  rw [run, runFrom_eq_exec, extends_prefixOf h]

theorem exec_append (q : Q) (u v : List Sym) : A.exec q (u ++ v) = A.exec (A.exec q u) v := by
  simp [exec, List.foldl_append]

theorem scan_append (s : MState Q) (u v : List Sym) : A.scan s (u ++ v) = A.scan (A.scan s u) v := by
  simp [scan, List.foldl_append]

theorem scan_q (s : MState Q) (w : List Sym) : (A.scan s w).q = A.exec s.q w := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih => simp only [scan, exec, List.foldl_cons] at ih ⊢; rw [ih]; rfl

theorem scan_pos (s : MState Q) (w : List Sym) : (A.scan s w).pos = s.pos + w.length := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih =>
    simp only [scan, List.foldl_cons] at ih ⊢; rw [ih]; simp [scanStep]; omega

/-- **The monitor over the prefix computes the infinite run's state, position and marked count.** -/
theorem scan_prefix (σ : OWord Sym) (n : ℕ) :
    A.scan A.init (prefixOf σ n) = ⟨A.run σ n, n, A.marks σ n, (A.scan A.init (prefixOf σ n)).lastMark⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [prefixOf_succ, scan_append, ih]
    simp [scan, scanStep, run, runFrom, marks]

/-- Every finite word the follower has seen yields the run of every extension. -/
theorem scan_extends {σ : OWord Sym} {u : List Sym} (h : Extends σ u) :
    (A.scan A.init u).q = A.run σ u.length ∧ (A.scan A.init u).pos = u.length ∧
      (A.scan A.init u).count = A.marks σ u.length := by
  have := A.scan_prefix σ u.length
  rw [extends_prefixOf h] at this
  rw [this]; exact ⟨rfl, rfl, rfl⟩

/-- **`lastMark` is honest**: from the start, no position in `(lastMark, pos]` is marked. -/
theorem lastMark_spec (σ : OWord Sym) (n : ℕ) :
    ∀ i, (A.scan A.init (prefixOf σ n)).lastMark < i → i ≤ n → A.mark (A.run σ i) = false := by
  induction n with
  | zero => intro i h1 h2; simp [scan, init] at h1; omega
  | succ n ih =>
    intro i h1 h2
    rw [prefixOf_succ, scan_append] at h1
    have hs := A.scan_prefix σ n
    rw [hs] at h1
    simp only [scan, List.foldl_cons, List.foldl_nil, scanStep] at h1
    by_cases hm : A.mark (A.step (A.run σ n) (σ n)) = true
    · rw [if_pos hm] at h1; omega
    · rw [if_neg hm] at h1
      rcases Nat.lt_or_ge i (n + 1) with hi | hi
      · exact ih i (by rw [hs]; exact h1) (by omega)
      · have : i = n + 1 := by omega
        subst this
        simpa [run, runFrom] using hm

/-- **A positive `lastMark` is a marked position.** (With `lastMark_spec`: `lastMark` is the last marked
position in `(0, n]`, and `0` means none.) -/
theorem lastMark_marked (σ : OWord Sym) (n : ℕ) :
    0 < (A.scan A.init (prefixOf σ n)).lastMark →
      A.mark (A.run σ (A.scan A.init (prefixOf σ n)).lastMark) = true := by
  induction n with
  | zero => intro h; simp [scan, init, prefixOf] at h
  | succ n ih =>
    intro h
    have hs := A.scan_prefix σ n
    rw [prefixOf_succ, scan_append] at h ⊢
    rw [hs] at h ih ⊢
    simp only [scan, List.foldl_cons, List.foldl_nil, scanStep] at h ⊢
    by_cases hm : A.mark (A.step (A.run σ n) (σ n)) = true
    · rw [if_pos hm] at h ⊢; simpa [run, runFrom] using hm
    · rw [if_neg hm] at h ⊢; exact ih h

theorem marks_mono (σ : OWord Sym) {a b : ℕ} (h : a ≤ b) : A.marks σ a ≤ A.marks σ b := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (by simp [marks])

/-- **Büchi acceptance IS the receipts' counter being unbounded.** -/
theorem buchi_iff_count_unbounded (σ : OWord Sym) :
    A.Accepts .buchi σ ↔ ∀ k, ∃ n, k ≤ A.marks σ n := by
  constructor
  · intro h k
    induction k with
    | zero => exact ⟨0, le_refl _⟩
    | succ k ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨m, hm, hmark⟩ := h (n + 1)
      obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      refine ⟨j + 1, ?_⟩
      have h1 : A.marks σ n ≤ A.marks σ j := A.marks_mono σ (by omega)
      have h2 : A.marks σ (j + 1) = A.marks σ j + 1 := by simp [marks, hmark]
      omega
  · intro h N
    by_contra hno
    push Not at hno
    have hconst : ∀ n, A.marks σ n ≤ A.marks σ N := by
      intro n
      induction n with
      | zero => exact Nat.zero_le _
      | succ n ih =>
        rcases Nat.lt_or_ge n N with hn | hn
        · exact A.marks_mono σ (by omega)
        · have hf : A.mark (A.run σ (n + 1)) = false := by
            have := hno (n + 1) (by omega); simpa using this
          simp [marks, hf]; exact ih
    obtain ⟨n, hn⟩ := h (A.marks σ N + 1)
    have := hconst n
    omega

/-- **Co-Büchi acceptance IS the receipts' counter being bounded.** -/
theorem coBuchi_iff_count_bounded (σ : OWord Sym) :
    A.Accepts .coBuchi σ ↔ ∃ k, ∀ n, A.marks σ n ≤ k := by
  have h := A.buchi_iff_count_unbounded σ
  simp only [Accepts] at h ⊢
  rw [h]
  push Not
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, fun n => by have := hk n; omega⟩
  · rintro ⟨k, hk⟩; exact ⟨k + 1, fun n => by have := hk n; omega⟩

end DOmega

/-! ## Verdicts -/

namespace VCert

/-- **Validity of a verdict certificate.** Both sets are closed under every transition; for Büchi,
`dead` avoids `F` and `good` lies inside `F`; for co-Büchi the reverse. -/
def Valid (c : VCert Q) (A : DOmega Q Sym) (cond : Cond) : Prop :=
  (∀ q a, c.dead q = true → c.dead (A.step q a) = true) ∧
  (∀ q a, c.good q = true → c.good (A.step q a) = true) ∧
  match cond with
  | .buchi => (∀ q, c.dead q = true → A.mark q = false) ∧ (∀ q, c.good q = true → A.mark q = true)
  | .coBuchi => (∀ q, c.dead q = true → A.mark q = true) ∧ (∀ q, c.good q = true → A.mark q = false)

end VCert

/-- A finite word every infinite extension of which is rejected / accepted. -/
def BadPrefix (P : OWord Sym → Prop) (u : List Sym) : Prop := ∀ σ, Extends σ u → ¬ P σ
def GoodPrefix (P : OWord Sym → Prop) (u : List Sym) : Prop := ∀ σ, Extends σ u → P σ

section verdicts

variable {A : DOmega Q Sym} {c : VCert Q} {cond : Cond}

theorem closed_runFrom {S : Q → Bool} (hS : ∀ q a, S q = true → S (A.step q a) = true)
    (σ : OWord Sym) (m : ℕ) (hm : S (A.run σ m) = true) : ∀ n, m ≤ n → S (A.run σ n) = true := by
  intro n hn
  induction hn with
  | refl => exact hm
  | step _ ih => exact hS _ _ ih

theorem exec_closed {S : Q → Bool} (hS : ∀ q a, S q = true → S (A.step q a) = true)
    (q : Q) (hq : S q = true) (w : List Sym) : S (A.exec q w) = true := by
  induction w generalizing q with
  | nil => exact hq
  | cons a w ih => exact ih _ (hS q a hq)

/-- From a state in a closed set that avoids / lies in `F` from position `m` on, the run's acceptance
is decided. -/
theorem dead_rejects (hv : c.Valid A cond) (σ : OWord Sym) (m : ℕ) (hm : c.dead (A.run σ m) = true) :
    ¬ A.Accepts cond σ := by
  have hall := closed_runFrom hv.1 σ m hm
  cases cond with
  | buchi =>
    intro h
    obtain ⟨n, hn, hmark⟩ := h m
    have := hv.2.2.1 _ (hall n hn)
    simp [this] at hmark
  | coBuchi =>
    intro h
    apply h
    intro N
    exact ⟨max N m, le_max_left _ _, hv.2.2.1 _ (hall _ (le_max_right _ _))⟩

theorem good_accepts (hv : c.Valid A cond) (σ : OWord Sym) (m : ℕ) (hm : c.good (A.run σ m) = true) :
    A.Accepts cond σ := by
  have hall := closed_runFrom hv.2.1 σ m hm
  cases cond with
  | buchi =>
    intro N
    exact ⟨max N m, le_max_left _ _, hv.2.2.2 _ (hall _ (le_max_right _ _))⟩
  | coBuchi =>
    rintro h
    obtain ⟨n, hn, hmark⟩ := h m
    have := hv.2.2.2 _ (hall n hn)
    simp [this] at hmark

/-- **`verdict_viol_sound`**: a `viol` verdict on the prefix `u` makes `u` a bad prefix of the
automaton's ω-language. -/
theorem verdict_viol_sound (hv : c.Valid A cond) {u : List Sym}
    (h : verdictOf c (A.exec A.start u) = .viol) : BadPrefix (A.Accepts cond) u := by
  intro σ hσ
  apply dead_rejects hv σ u.length
  rw [A.run_eq_exec hσ]
  unfold verdictOf at h
  split at h
  · assumption
  · split at h <;> cases h

/-- **`verdict_sat_sound`**: a `sat` verdict on `u` makes `u` a good prefix. -/
theorem verdict_sat_sound (hv : c.Valid A cond) {u : List Sym}
    (h : verdictOf c (A.exec A.start u) = .sat) : GoodPrefix (A.Accepts cond) u := by
  intro σ hσ
  apply good_accepts hv σ u.length
  rw [A.run_eq_exec hσ]
  unfold verdictOf at h
  split at h
  · cases h
  · split at h
    · assumption
    · cases h

/-- **`verdict_monotone`**: a definite verdict is final. Whatever is appended, `viol` stays `viol` and
`sat` stays `sat`; in particular a `viol` never becomes `sat`. -/
theorem verdict_monotone (hv : c.Valid A cond) (q : Q) (v : List Sym)
    (h : verdictOf c q ≠ .unknown) : verdictOf c (A.exec q v) = verdictOf c q := by
  have hdg : ∀ q, c.dead q = true → c.good q = true → False := by
    intro q hd hg
    cases cond with
    | buchi => have := hv.2.2.1 q hd; have := hv.2.2.2 q hg; simp_all
    | coBuchi => have := hv.2.2.1 q hd; have := hv.2.2.2 q hg; simp_all
  unfold verdictOf at h ⊢
  by_cases hd : c.dead q = true
  · rw [if_pos (exec_closed hv.1 q hd v), if_pos hd]
  · rw [if_neg hd] at h ⊢
    by_cases hg : c.good q = true
    · have hg' := exec_closed hv.2.1 q hg v
      have hd' : c.dead (A.exec q v) = false := by
        cases hx : c.dead (A.exec q v)
        · rfl
        · exact (hdg _ hx hg').elim
      simp [hd', hg', hg]
    · simp [hg] at h

/-- The receipt form: `viol` after a prefix is `viol` after every longer prefix. -/
theorem verdict_viol_final (hv : c.Valid A cond) (u v : List Sym)
    (h : verdictOf c (A.exec A.start u) = .viol) :
    verdictOf c (A.exec A.start (u ++ v)) = .viol := by
  rw [A.exec_append, verdict_monotone hv _ v (by rw [h]; decide), h]

end verdicts

/-! ## Safety ∩ liveness -/

def SafetyMon.run (M : SafetyMon S Sym) (σ : OWord Sym) : ℕ → S
  | 0 => M.start
  | n + 1 => M.step (M.run σ n) (σ n)

/-- The safety language: no prefix reaches `bad`. -/
def SafetyMon.Safe (M : SafetyMon S Sym) (σ : OWord Sym) : Prop := ∀ n, M.bad (M.run σ n) = false

def SafetyMon.Absorbing (M : SafetyMon S Sym) : Prop := ∀ s a, M.bad s = true → M.bad (M.step s a) = true

theorem prod_run {S L : Type} (M : SafetyMon S Sym) (A : DOmega L Sym) (σ : OWord Sym) (n : ℕ) :
    (prodSafety M A).run σ n = (M.run σ n, A.run σ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (prodSafety M A).step ((prodSafety M A).runFrom (prodSafety M A).start σ n) (σ n) = _
    rw [show (prodSafety M A).runFrom (prodSafety M A).start σ n = (prodSafety M A).run σ n from rfl, ih]
    rfl

/-- **`prod_accepts_iff`**: the product's Büchi language is the safety language intersected with the
liveness automaton's Büchi language. -/
theorem prod_accepts_iff {S L : Type} (M : SafetyMon S Sym) (A : DOmega L Sym) (habs : M.Absorbing)
    (σ : OWord Sym) :
    (prodSafety M A).Accepts .buchi σ ↔ M.Safe σ ∧ A.Accepts .buchi σ := by
  have hm : ∀ n, (prodSafety M A).mark ((prodSafety M A).run σ n) =
      (!M.bad (M.run σ n) && A.mark (A.run σ n)) := by
    intro n; rw [prod_run]; rfl
  simp only [DOmega.Accepts, InfOften, hm, Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · intro h
    refine ⟨?_, fun N => ?_⟩
    · intro m
      by_contra hb
      have hb : M.bad (M.run σ m) = true := by simpa using hb
      have hall : ∀ n, m ≤ n → M.bad (M.run σ n) = true := by
        intro n hn
        induction hn with
        | refl => exact hb
        | step _ ih => exact habs _ _ ih
      obtain ⟨n, hn, h1, _⟩ := h m
      simp [hall n hn] at h1
    · obtain ⟨n, hn, _, h2⟩ := h N
      exact ⟨n, hn, h2⟩
  · rintro ⟨hs, hl⟩ N
    obtain ⟨n, hn, h2⟩ := hl N
    exact ⟨n, hn, hs n, h2⟩

theorem prodVCert_valid {S L : Type} (M : SafetyMon S Sym) (A : DOmega L Sym) (habs : M.Absorbing) :
    (prodVCert (L := L) M).Valid (prodSafety M A) .buchi := by
  refine ⟨fun q a h => habs _ _ h, fun _ _ h => by simp [prodVCert] at h, ?_⟩
  show (∀ q, (prodVCert (L := L) M).dead q = true → (prodSafety M A).mark q = false) ∧
    (∀ q, (prodVCert (L := L) M).good q = true → (prodSafety M A).mark q = true)
  refine ⟨fun q h => ?_, fun q h => by simp [prodVCert] at h⟩
  simp only [prodVCert] at h
  simp [prodSafety, h]

#assert_axioms DOmega.runFrom_eq_exec
#assert_axioms DOmega.run_eq_exec
#assert_axioms DOmega.scan_prefix
#assert_axioms DOmega.scan_extends
#assert_axioms DOmega.lastMark_spec
#assert_axioms DOmega.lastMark_marked
#assert_axioms DOmega.buchi_iff_count_unbounded
#assert_axioms DOmega.coBuchi_iff_count_bounded
#assert_axioms dead_rejects
#assert_axioms good_accepts
#assert_axioms verdict_viol_sound
#assert_axioms verdict_sat_sound
#assert_axioms verdict_monotone
#assert_axioms verdict_viol_final
#assert_axioms prod_accepts_iff
#assert_axioms prodVCert_valid

end Dregg2.Stream
