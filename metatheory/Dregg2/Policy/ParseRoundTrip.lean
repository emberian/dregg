/-
# Dregg2.Policy.ParseRoundTrip — the parser inverts the token printer.

The token-level half of `parse_print_roundtrip`: for every well-formed AST `x`, and every list of
positioned tokens `ps` whose token sequence is `x`'s printed tokens, the parser applied to
`ps ++ rest` returns `x` and exactly `rest`, provided `rest` begins with a token that cannot
continue `x` (the follow condition). Positions are arbitrary: they never affect a successful parse.

The regex induction is the only non-routine part. For each `r` it proves three things at once
(`ReOK r`): the parse at every precedence level `k ≤ 5` of `r.toksAt k` (with the level's follow
condition `stopB k`), and the parse at the postfix level of `r` followed by ANY run of postfix
operators (`ParsesOps`), which is what makes the left-recursive postfix loop inductive.
-/
import Dregg2.Policy.Parser
import Dregg2.Tactics

namespace Dregg2.Policy

set_option autoImplicit false

/-! ## Follow conditions. -/

def isPostfixTok : Tok → Bool
  | .punct .star | .punct .plus | .punct .quest | .punct .lbrace => true
  | _ => false

/-- `stopB k t`: a token `t` after a level-`k` regex ends it (no level `j ≥ k` continues on `t`). -/
def stopB (k : Nat) (t : Tok) : Bool :=
  (decide (0 < k) || t != tBar) && (decide (1 < k) || t != tAmp) &&
  (decide (2 < k) || !startsUnary t) && (decide (4 < k) || !isPostfixTok t)

theorem stopB_succ {k : Nat} {t : Tok} (h : stopB k t = true) : stopB (k + 1) t = true := by
  simp only [stopB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rcases h1 with h | h
    · left; omega
    · right; exact h
  · rcases h2 with h | h
    · left; omega
    · right; exact h
  · rcases h3 with h | h
    · left; omega
    · right; exact h
  · rcases h4 with h | h
    · left; omega
    · right; exact h

theorem stopB_mono {k j : Nat} {t : Tok} (hkj : k ≤ j) (h : stopB k t = true) : stopB j t = true := by
  induction hkj with
  | refl => exact h
  | step _ ih => exact stopB_succ ih

/-! ## Postfix operator runs. -/

inductive POp where
  | star | plus | opt
  | rep (m n : Nat)

def POp.apply : POp → Re → Re
  | .star, r => .star r
  | .plus, r => .plus r
  | .opt, r => .opt r
  | .rep m n, r => .rep r m n

def POp.toks : POp → List Tok
  | .star => [tStar]
  | .plus => [tPlus]
  | .opt => [tQuest]
  | .rep m n => [tLB, .int m, tComma, .int n, tRB]

def applyOps (r : Re) : List POp → Re
  | [] => r
  | o :: os => applyOps (o.apply r) os

def opsToks : List POp → List Tok
  | [] => []
  | o :: os => o.toks ++ opsToks os

/-- The postfix loop reads a run of printed operators. -/
theorem postfixLoop_ops : ∀ (ops : List POp) (acc : Re) (ps rest : List PTok),
    ps.map PTok.tok = opsToks ops → isPostfixTok (headTok rest) = false →
    postfixLoop acc (ps ++ rest) = .ok (applyOps acc ops, rest) := by
  intro ops
  induction ops with
  | nil =>
    intro acc ps rest hps hr
    simp only [opsToks, List.map_eq_nil_iff] at hps
    subst hps
    cases rest with
    | nil => rfl
    | cons t ts =>
      simp only [headTok] at hr
      obtain ⟨tok, pos⟩ := t
      simp only at hr
      simp only [List.nil_append, applyOps]
      cases tok with
      | punct p => cases p <;> simp_all [postfixLoop, isPostfixTok]
      | _ => simp [postfixLoop]
  | cons o os ih =>
    intro acc ps rest hps hr
    simp only [opsToks, List.map_eq_append_iff] at hps
    obtain ⟨p1, p2, rfl, h1, h2⟩ := hps
    cases o with
    | star =>
      obtain ⟨t, rfl, ht⟩ : ∃ t, p1 = [t] ∧ t.tok = tStar := by
        simp only [POp.toks, List.map_eq_singleton_iff] at h1; exact h1
      simp only [List.cons_append, List.nil_append]
      rw [postfixLoop.eq_def]; simp only [ht, applyOps, POp.apply]
      exact ih _ p2 rest h2 hr
    | plus =>
      obtain ⟨t, rfl, ht⟩ : ∃ t, p1 = [t] ∧ t.tok = tPlus := by
        simp only [POp.toks, List.map_eq_singleton_iff] at h1; exact h1
      simp only [List.cons_append, List.nil_append]
      rw [postfixLoop.eq_def]; simp only [ht, applyOps, POp.apply]
      exact ih _ p2 rest h2 hr
    | opt =>
      obtain ⟨t, rfl, ht⟩ : ∃ t, p1 = [t] ∧ t.tok = tQuest := by
        simp only [POp.toks, List.map_eq_singleton_iff] at h1; exact h1
      simp only [List.cons_append, List.nil_append]
      rw [postfixLoop.eq_def]; simp only [ht, applyOps, POp.apply]
      exact ih _ p2 rest h2 hr
    | rep m n =>
      simp only [POp.toks, List.map_eq_cons_iff, List.map_eq_nil_iff] at h1
      obtain ⟨a, l1, rfl, ha, b, l2, rfl, hb, c, l3, rfl, hc, d, l4, rfl, hd, e, l5, rfl, he, rfl⟩ := h1
      simp only [List.cons_append, List.nil_append]
      rw [postfixLoop]
      simp only [ha, hb, hc, hd, he, if_true, applyOps, POp.apply]
      exact ih _ p2 rest h2 hr

/-! ## One-step unfolding lemmas for `parseRe`. -/

section Steps
variable {n : Nat} {ts ts' rest rest1 : List PTok} {t t' : PTok} {l r : Re}

theorem alt_step (h1 : parseRe n 1 ts = .ok (l, t :: ts')) (ht : t.tok = tBar)
    (h2 : parseRe n 0 ts' = .ok (r, rest)) : parseRe (n+1) 0 ts = .ok (.alt l r, rest) := by
  simp only [parseRe, h1, ht, h2, bind, Except.bind, pure, Except.pure, if_true]

theorem lvl0_pass (h1 : parseRe n 1 ts = .ok (l, rest)) (hr : headTok rest ≠ tBar) :
    parseRe (n+1) 0 ts = .ok (l, rest) := by
  simp only [parseRe, h1, bind, Except.bind, pure, Except.pure]
  cases rest with
  | nil => rfl
  | cons t ts' => simp only [headTok] at hr; simp [hr]

theorem inter_step (h1 : parseRe n 2 ts = .ok (l, t :: ts')) (ht : t.tok = tAmp)
    (h2 : parseRe n 1 ts' = .ok (r, rest)) : parseRe (n+1) 1 ts = .ok (.inter l r, rest) := by
  simp only [parseRe, h1, ht, h2, bind, Except.bind, pure, Except.pure, if_true]

theorem lvl1_pass (h1 : parseRe n 2 ts = .ok (l, rest)) (hr : headTok rest ≠ tAmp) :
    parseRe (n+1) 1 ts = .ok (l, rest) := by
  simp only [parseRe, h1, bind, Except.bind, pure, Except.pure]
  cases rest with
  | nil => rfl
  | cons t ts' => simp only [headTok] at hr; simp [hr]

theorem cat_step (h1 : parseRe n 3 ts = .ok (l, rest1)) (hs : startsUnary (headTok rest1) = true)
    (h2 : parseRe n 2 rest1 = .ok (r, rest)) : parseRe (n+1) 2 ts = .ok (.cat l r, rest) := by
  simp only [parseRe, h1, hs, h2, bind, Except.bind, pure, Except.pure, if_true]

theorem lvl2_pass (h1 : parseRe n 3 ts = .ok (l, rest)) (hs : startsUnary (headTok rest) = false) :
    parseRe (n+1) 2 ts = .ok (l, rest) := by
  simp only [parseRe, h1, hs, bind, Except.bind, pure, Except.pure]
  rfl

theorem neg_step (ht : t.tok = tTilde) (h1 : parseRe n 3 ts = .ok (r, rest)) :
    parseRe (n+1) 3 (t :: ts) = .ok (.neg r, rest) := by
  simp only [parseRe, ht, h1, bind, Except.bind, pure, Except.pure, if_true]

theorem lvl3_pass (hs : headTok ts ≠ tTilde) : parseRe (n+1) 3 ts = parseRe n 4 ts := by
  cases ts with
  | nil => rfl
  | cons t ts' => simp only [headTok] at hs; simp [parseRe, hs]

theorem lvl4_eq : parseRe (n+1) 4 ts = (parseRe n 5 ts).bind (fun p => postfixLoop p.1 p.2) := by
  simp only [parseRe, bind]

theorem paren_step (ht : t.tok = tLP) (h1 : parseRe n 0 ts = .ok (r, t' :: rest)) (ht' : t'.tok = tRP) :
    parseRe (n+1) 5 (t :: ts) = .ok (r, rest) := by
  simp only [parseRe, ht, h1, bind, Except.bind, pure, Except.pure, expectP, ht', if_true]

end Steps

/-! ## Shape facts about printed regexes. -/

theorem wrap_eq_of_le {k : Nat} {r : Re} {ts : List Tok} (h : k ≤ r.prec) : wrap k r ts = ts := by
  simp [wrap, h]

theorem wrap_eq_of_lt {k : Nat} {r : Re} {ts : List Tok} (h : r.prec < k) :
    wrap k r ts = tLP :: (ts ++ [tRP]) := by
  simp [wrap, Nat.not_le.mpr h]

theorem prec_le_five (r : Re) : r.prec ≤ 5 := by
  cases r <;> simp [Re.prec]

/-- Every printed regex begins with a token that starts a unary expression. -/
theorem toks_head (r : Re) : ∃ t tl, r.toks = t :: tl ∧ startsUnary t = true ∧
    (4 ≤ r.prec → t ≠ tTilde) := by
  induction r with
  | lit bs => exact ⟨_, _, rfl, rfl, by simp⟩
  | set n rs => exact ⟨_, _, rfl, rfl, by simp⟩
  | esc e => exact ⟨_, _, rfl, rfl, by simp⟩
  | any => exact ⟨_, _, rfl, rfl, by simp⟩
  | alt l r ihl _ =>
    by_cases h : 1 ≤ l.prec
    · obtain ⟨t, tl, he, hs, hn⟩ := ihl
      refine ⟨t, tl ++ (tBar :: wrap 0 r r.toks), ?_, hs, ?_⟩
      · simp [Re.toks, wrap_eq_of_le h, he]
      · intro h4; simp [Re.prec] at h4
    · exact ⟨tLP, _, by rw [Re.toks, wrap_eq_of_lt (Nat.lt_of_not_le h)]; rfl, rfl, by simp⟩
  | inter l r ihl _ =>
    by_cases h : 2 ≤ l.prec
    · obtain ⟨t, tl, he, hs, hn⟩ := ihl
      refine ⟨t, tl ++ (tAmp :: wrap 1 r r.toks), ?_, hs, ?_⟩
      · simp [Re.toks, wrap_eq_of_le h, he]
      · intro h4; simp [Re.prec] at h4
    · exact ⟨tLP, _, by rw [Re.toks, wrap_eq_of_lt (Nat.lt_of_not_le h)]; rfl, rfl, by simp⟩
  | cat l r ihl _ =>
    by_cases h : 3 ≤ l.prec
    · obtain ⟨t, tl, he, hs, _⟩ := ihl
      refine ⟨t, tl ++ wrap 2 r r.toks, ?_, hs, ?_⟩
      · simp [Re.toks, wrap_eq_of_le h, he]
      · intro h4; simp [Re.prec] at h4
    · exact ⟨tLP, _, by rw [Re.toks, wrap_eq_of_lt (Nat.lt_of_not_le h)]; rfl, rfl, by simp⟩
  | neg r _ => exact ⟨tTilde, _, rfl, rfl, by simp [Re.prec]⟩
  | star r ih | plus r ih | opt r ih | rep r m n ih =>
    by_cases h : 4 ≤ r.prec
    · obtain ⟨t, tl, he, hs, hn⟩ := ih
      exact ⟨t, _, by rw [Re.toks, wrap_eq_of_le h, he]; rfl, hs, fun _ => hn h⟩
    · exact ⟨tLP, _, by rw [Re.toks, wrap_eq_of_lt (Nat.lt_of_not_le h)]; rfl, rfl, by simp⟩


theorem toksAt_of_le {k : Nat} {r : Re} (h : k ≤ r.prec) : r.toksAt k = r.toks := wrap_eq_of_le h

theorem toksAt_of_lt {k : Nat} {r : Re} (h : r.prec < k) : r.toksAt k = tLP :: (r.toks ++ [tRP]) :=
  wrap_eq_of_lt h

theorem len_of_map {ps : List PTok} {ts : List Tok} (h : ps.map PTok.tok = ts) :
    ps.length = ts.length := by
  rw [← h, List.length_map]

theorem toksAt_ne_nil (k : Nat) (r : Re) : r.toksAt k ≠ [] := by
  obtain ⟨t, tl, he, _⟩ := toks_head r
  rcases Nat.lt_or_ge r.prec k with h | h
  · rw [toksAt_of_lt h]; simp
  · rw [toksAt_of_le h, he]; simp

/-! ## Facts read off `stopB`. -/

theorem stop_bar {k : Nat} {t : Tok} (h : stopB k t = true) (hk : k = 0) : t ≠ tBar := by
  subst hk; intro e; subst e; simp [stopB] at h

theorem stop_amp {k : Nat} {t : Tok} (h : stopB k t = true) (hk : k ≤ 1) : t ≠ tAmp := by
  intro e; subst e; simp [stopB, startsUnary, isPostfixTok] at h; omega

theorem stop_unary {k : Nat} {t : Tok} (h : stopB k t = true) (hk : k ≤ 2) : startsUnary t = false := by
  simp only [stopB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨_, _⟩, h3⟩, _⟩ := h
  rcases h3 with h3 | h3
  · omega
  · exact h3

theorem stop_post {k : Nat} {t : Tok} (h : stopB k t = true) (hk : k ≤ 4) : isPostfixTok t = false := by
  simp only [stopB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨_, _⟩, _⟩, h4⟩ := h
  rcases h4 with h4 | h4
  · omega
  · exact h4

theorem stopB_five (t : Tok) : stopB 5 t = true := by simp [stopB]

/-! ## The level claims. -/

/-- The parse at level `k` of `r.toksAt k` before any `rest` that ends a level-`k` regex. -/
def ParsesAt (k : Nat) (r : Re) : Prop :=
  ∀ (ps rest : List PTok) (n : Nat), ps.map PTok.tok = r.toksAt k → stopB k (headTok rest) = true →
    3 * ps.length + (6 - k) ≤ n → parseRe n k (ps ++ rest) = .ok (r, rest)

/-- The parse at the postfix level of `r.toksAt 4` followed by any run of postfix operators. -/
def ParsesOps (r : Re) : Prop :=
  ∀ (ops : List POp) (ps rest : List PTok) (n : Nat), ps.map PTok.tok = r.toksAt 4 ++ opsToks ops →
    isPostfixTok (headTok rest) = false → 3 * (r.toksAt 4).length + 2 ≤ n →
    parseRe n 4 (ps ++ rest) = .ok (applyOps r ops, rest)

def ReOK (r : Re) : Prop := (∀ k, k ≤ 5 → ParsesAt k r) ∧ ParsesOps r

theorem headTok_append_cons (p : PTok) (ps rest : List PTok) :
    headTok ((p :: ps) ++ rest) = p.tok := rfl

/-- One level down: `k` from `k + 1` when both print the same tokens. -/
theorem step_down {k : Nat} {r : Re} (hk : k ≤ 3) (h : ParsesAt (k + 1) r)
    (heq : r.toksAt k = r.toksAt (k + 1))
    (hhead : k = 3 → ∀ t tl, r.toksAt (k + 1) = t :: tl → t ≠ tTilde) : ParsesAt k r := by
  intro ps rest n hps hstop hn
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have inner := h ps rest n' (heq ▸ hps) (stopB_succ hstop) (by omega)
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  · exact lvl0_pass inner (stop_bar hstop rfl)
  · exact lvl1_pass inner (stop_amp hstop (Nat.le_refl _))
  · exact lvl2_pass inner (stop_unary hstop (Nat.le_refl _))
  · rw [lvl3_pass]
    · exact inner
    · cases ps with
      | nil => exact absurd (by rw [heq] at hps; exact hps.symm) (toksAt_ne_nil _ _)
      | cons p ps' =>
        rw [headTok_append_cons]
        simp only [List.map_cons] at hps
        rw [heq] at hps
        exact hhead rfl p.tok _ hps.symm

/-- Down from an unwrapped level `j ≤ prec r` to any `k ≤ j`. -/
theorem climbU {r : Re} : ∀ (d k : Nat), k + d ≤ r.prec → k + d ≤ 4 → ParsesAt (k + d) r →
    (k ≤ 3 → 3 < k + d → ∀ t tl, r.toks = t :: tl → t ≠ tTilde) → ParsesAt k r := by
  intro d
  induction d with
  | zero => intro k _ _ h _; exact h
  | succ d ih =>
    intro k hp h4 h hhead
    have h1 : ParsesAt (k + 1) r := ih (k + 1) (by omega) (by omega)
      (by rw [show k + 1 + d = k + (d + 1) by omega]; exact h)
      (fun hk3 hlt t tl he => hhead (by omega) (by omega) t tl he)
    refine step_down (by omega) h1 ?_ ?_
    · rw [toksAt_of_le (by omega), toksAt_of_le (by omega)]
    · intro hk t tl he
      rw [toksAt_of_le (by omega)] at he
      exact hhead (by omega) (by omega) t tl he

/-- Down from level 4 to a wrapped level `k > prec r`. -/
theorem climbW {r : Re} : ∀ (d k : Nat), r.prec < k → k + d = 4 → ParsesAt 4 r → ParsesAt k r := by
  intro d
  induction d with
  | zero => intro k _ hk h; rw [show k = 4 by omega]; exact h
  | succ d ih =>
    intro k hp hk h
    have h1 : ParsesAt (k + 1) r := ih (k + 1) (by omega) (by omega) h
    refine step_down (by omega) h1 ?_ ?_
    · rw [toksAt_of_lt (by omega), toksAt_of_lt (by omega)]
    · intro _ t tl he
      rw [toksAt_of_lt (by omega)] at he
      simp at he; rw [← he.1]; simp

/-- An atom-level parse of a parenthesized regex. -/
theorem paren5 {r : Re} (h0 : ParsesAt 0 r) (hp : r.prec < 5) : ParsesAt 5 r := by
  intro ps rest n hps _ hn
  rw [toksAt_of_lt hp] at hps
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  match ps, hps with
  | p :: ps', hps =>
    simp only [List.map_cons, List.cons.injEq] at hps
    obtain ⟨hp1, hps'⟩ := hps
    rw [List.map_eq_append_iff] at hps'
    obtain ⟨q, q2, rfl, hq, hq2⟩ := hps'
    rw [List.map_eq_singleton_iff] at hq2
    obtain ⟨p', rfl, hp'⟩ := hq2
    have hlen := len_of_map hq
    simp only [List.length_cons, List.length_append] at hn
    have inner := h0 q (p' :: rest) n' (by rw [toksAt_of_le (Nat.zero_le _)]; exact hq)
      (by simp [headTok, hp', stopB, startsUnary, isPostfixTok]) (by omega)
    simp only [List.cons_append, List.append_assoc]
    exact paren_step hp1 inner hp'

/-- The postfix-run claim from the atom-level claim, when `r` prints the same at levels 4 and 5. -/
theorem ops_of_five {r : Re} (h5 : ParsesAt 5 r) (hp : r.prec ≠ 4) : ParsesOps r := by
  intro ops ps rest n hps hr hn
  have heq : r.toksAt 4 = r.toksAt 5 := by
    rcases Nat.lt_or_ge r.prec 4 with h | h
    · rw [toksAt_of_lt h, toksAt_of_lt (by omega)]
    · rw [toksAt_of_le h, toksAt_of_le (by have := prec_le_five r; omega)]
  rw [List.map_eq_append_iff] at hps
  obtain ⟨p1, p2, rfl, h1, h2⟩ := hps
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hlen := len_of_map h1
  have inner := h5 p1 (p2 ++ rest) n' (heq ▸ h1) (stopB_five _) (by rw [hlen, heq] at *; omega)
  rw [lvl4_eq, List.append_assoc, inner]
  exact postfixLoop_ops ops r p2 rest h2 hr

theorem four_of_ops {r : Re} (h : ParsesOps r) : ParsesAt 4 r := by
  intro ps rest n hps hstop hn
  have := h [] ps rest n (by simpa [opsToks] using hps) (stop_post hstop (Nat.le_refl _))
    (by rw [← len_of_map hps]; omega)
  simpa [applyOps] using this

/-! ## Assembling `ReOK` from the claim at a regex's own level. -/

theorem finish_composite {r : Re} (hc : r.prec ≤ 3) (hN : ParsesAt r.prec r) : ReOK r := by
  have hlow : ∀ k, k ≤ r.prec → ParsesAt k r := fun k hk =>
    climbU (r.prec - k) k (by omega) (by omega) (by rw [show k + (r.prec - k) = r.prec by omega]; exact hN)
      (fun _ h3 => absurd h3 (by omega))
  have h5 := paren5 (hlow 0 (Nat.zero_le _)) (by omega)
  have hO := ops_of_five h5 (by omega)
  have h4 := four_of_ops hO
  refine ⟨fun k hk => ?_, hO⟩
  rcases Nat.lt_or_ge r.prec k with h | h
  · rcases (by omega : k = 5 ∨ k ≤ 4) with rfl | hk4
    · exact h5
    · exact climbW (4 - k) k h (by omega) h4
  · exact hlow k h

theorem finish_four {r : Re} (hc : r.prec = 4) (hO : ParsesOps r) : ReOK r := by
  have h4 := four_of_ops hO
  obtain ⟨t, tl, he, _, hn⟩ := toks_head r
  have hlow : ∀ k, k ≤ 4 → ParsesAt k r := fun k hk =>
    climbU (4 - k) k (by omega) (by omega) (by rw [show k + (4 - k) = 4 by omega]; exact h4)
      (fun _ _ t' tl' he' => by rw [he] at he'; simp at he'; rw [← he'.1]; exact hn (by omega))
  have h5 := paren5 (hlow 0 (by omega)) (by omega)
  refine ⟨fun k hk => ?_, hO⟩
  rcases (by omega : k = 5 ∨ k ≤ 4) with rfl | hk4
  · exact h5
  · exact hlow k hk4

theorem finish_atom {r : Re} (hc : r.prec = 5) (h5 : ParsesAt 5 r) : ReOK r := by
  have hO := ops_of_five h5 (by omega)
  have h4 := four_of_ops hO
  obtain ⟨t, tl, he, _, hn⟩ := toks_head r
  have hlow : ∀ k, k ≤ 4 → ParsesAt k r := fun k hk =>
    climbU (4 - k) k (by omega) (by omega) (by rw [show k + (4 - k) = 4 by omega]; exact h4)
      (fun _ _ t' tl' he' => by rw [he] at he'; simp at he'; rw [← he'.1]; exact hn (by omega))
  refine ⟨fun k hk => ?_, hO⟩
  rcases (by omega : k = 5 ∨ k ≤ 4) with rfl | hk4
  · exact h5
  · exact hlow k hk4

theorem toksAt_head (k : Nat) (r : Re) : ∃ t tl, r.toksAt k = t :: tl ∧ startsUnary t = true := by
  obtain ⟨t, tl, he, hs, _⟩ := toks_head r
  rcases Nat.lt_or_ge r.prec k with h | h
  · exact ⟨tLP, _, toksAt_of_lt h, rfl⟩
  · exact ⟨t, tl, by rw [toksAt_of_le h, he], hs⟩

theorem stopB_of_unary {t : Tok} (h : startsUnary t = true) : stopB 3 t = true := by
  cases t with
  | punct p => cases p <;> simp_all [stopB, startsUnary, isPostfixTok]
  | _ => simp_all [stopB, startsUnary, isPostfixTok]

/-! ## The regex induction. -/

theorem atom5 {r : Re} {t : Tok} (htoks : r.toks = [t]) (hr : r.prec = 5)
    (hparse : ∀ (p : PTok) (rest : List PTok) (n : Nat), p.tok = t →
      parseRe (n + 1) 5 (p :: rest) = .ok (r, rest)) : ParsesAt 5 r := by
  intro ps rest n hps _ hn
  rw [toksAt_of_le (by omega), htoks, List.map_eq_singleton_iff] at hps
  obtain ⟨p, rfl, hp⟩ := hps
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  exact hparse p rest n' hp

theorem reOK : ∀ r : Re, ReOK r := by
  intro r
  induction r with
  | lit bs =>
    refine finish_atom rfl (atom5 (t := .str bs) rfl rfl ?_)
    intro p rest n hp; simp [parseRe, hp]
  | set ng rs =>
    refine finish_atom rfl (atom5 (t := .cls ng rs) rfl rfl ?_)
    intro p rest n hp; simp [parseRe, hp]
  | esc e =>
    refine finish_atom rfl (atom5 (t := .esc e) rfl rfl ?_)
    intro p rest n hp; simp [parseRe, hp]
  | any =>
    refine finish_atom rfl (atom5 (t := tDot) rfl rfl ?_)
    intro p rest n hp; simp [parseRe, hp]
  | alt l r ihl ihr =>
    refine finish_composite (by simp [Re.prec]) ?_
    intro ps rest n hps hstop hn
    simp only [Re.prec] at hps hstop hn ⊢
    rw [toksAt_of_le (by simp [Re.prec]), Re.toks, List.map_eq_append_iff] at hps
    obtain ⟨pl, pr', rfl, hl, hr'⟩ := hps
    rw [List.map_eq_cons_iff] at hr'
    obtain ⟨pb, pr, rfl, hb, hr⟩ := hr'
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have l1 := len_of_map hl; have l2 := len_of_map hr
    simp only [List.length_append, List.length_cons] at hn
    have h1 := ihl.1 1 (by omega) pl (pb :: (pr ++ rest)) n' hl
      (by simp [headTok, hb, stopB, startsUnary, isPostfixTok]) (by omega)
    have h2 := ihr.1 0 (by omega) pr rest n' hr hstop (by omega)
    simp only [List.append_assoc, List.cons_append]
    exact alt_step h1 hb h2
  | inter l r ihl ihr =>
    refine finish_composite (by simp [Re.prec]) ?_
    intro ps rest n hps hstop hn
    simp only [Re.prec] at hps hstop hn ⊢
    rw [toksAt_of_le (by simp [Re.prec]), Re.toks, List.map_eq_append_iff] at hps
    obtain ⟨pl, pr', rfl, hl, hr'⟩ := hps
    rw [List.map_eq_cons_iff] at hr'
    obtain ⟨pb, pr, rfl, hb, hr⟩ := hr'
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have l1 := len_of_map hl; have l2 := len_of_map hr
    simp only [List.length_append, List.length_cons] at hn
    have h1 := ihl.1 2 (by omega) pl (pb :: (pr ++ rest)) n' hl
      (by simp [headTok, hb, stopB, startsUnary, isPostfixTok]) (by omega)
    have h2 := ihr.1 1 (by omega) pr rest n' hr hstop (by omega)
    simp only [List.append_assoc, List.cons_append]
    exact inter_step h1 hb h2
  | cat l r ihl ihr =>
    refine finish_composite (by simp [Re.prec]) ?_
    intro ps rest n hps hstop hn
    simp only [Re.prec] at hps hstop hn ⊢
    rw [toksAt_of_le (by simp [Re.prec]), Re.toks, List.map_eq_append_iff] at hps
    obtain ⟨pl, pr, rfl, hl, hr⟩ := hps
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have l1 := len_of_map hl; have l2 := len_of_map hr
    have hl0 : 0 < pl.length := by
      obtain ⟨t, tl, he, _⟩ := toksAt_head 3 l; rw [l1]; unfold Re.toksAt at he; rw [he]; simp
    simp only [List.length_append] at hn
    obtain ⟨t, tl, he, hs⟩ := toksAt_head 2 r
    have hhead : headTok (pr ++ rest) = t := by
      unfold Re.toksAt at he
      rw [he] at hr
      cases pr with
      | nil => simp at hr
      | cons p pr' => simp only [List.map_cons, List.cons.injEq] at hr; simp [headTok, hr.1]
    have h1 := ihl.1 3 (by omega) pl (pr ++ rest) n' hl (by rw [hhead]; exact stopB_of_unary hs)
      (by omega)
    have h2 := ihr.1 2 (by omega) pr rest n' hr hstop (by omega)
    rw [List.append_assoc]
    exact cat_step h1 (by rw [hhead]; exact hs) h2
  | neg r ih =>
    refine finish_composite (by simp [Re.prec]) ?_
    intro ps rest n hps hstop hn
    simp only [Re.prec] at hps hstop hn ⊢
    rw [toksAt_of_le (by simp [Re.prec]), Re.toks, List.map_eq_cons_iff] at hps
    obtain ⟨pt, pr, rfl, ht, hr⟩ := hps
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have l2 := len_of_map hr
    simp only [List.length_cons] at hn
    have h1 := ih.1 3 (by omega) pr rest n' hr hstop (by omega)
    exact neg_step ht h1
  | star r ih | plus r ih | opt r ih | rep r m k ih =>
    refine finish_four (by simp [Re.prec]) ?_
    intro ops ps rest n hps hr hn
    first
    | have := ih.2 (.star :: ops) ps rest n
        (by rw [hps, toksAt_of_le (by simp [Re.prec]), Re.toks]; simp [opsToks, POp.toks, Re.toksAt])
        hr (by rw [toksAt_of_le (by simp [Re.prec]), Re.toks] at hn; simp at hn; unfold Re.toksAt; omega)
      exact this
    | have := ih.2 (.plus :: ops) ps rest n
        (by rw [hps, toksAt_of_le (by simp [Re.prec]), Re.toks]; simp [opsToks, POp.toks, Re.toksAt])
        hr (by rw [toksAt_of_le (by simp [Re.prec]), Re.toks] at hn; simp at hn; unfold Re.toksAt; omega)
      exact this
    | have := ih.2 (.opt :: ops) ps rest n
        (by rw [hps, toksAt_of_le (by simp [Re.prec]), Re.toks]; simp [opsToks, POp.toks, Re.toksAt])
        hr (by rw [toksAt_of_le (by simp [Re.prec]), Re.toks] at hn; simp at hn; unfold Re.toksAt; omega)
      exact this
    | have := ih.2 (.rep m k :: ops) ps rest n
        (by rw [hps, toksAt_of_le (by simp [Re.prec]), Re.toks]; simp [opsToks, POp.toks, Re.toksAt])
        hr (by rw [toksAt_of_le (by simp [Re.prec]), Re.toks] at hn; simp at hn; unfold Re.toksAt; omega)
      exact this

/-- ⚑ **The regex parser inverts the regex printer** (token level): for any regex `r`, any
positioned tokens spelling `r.toksAt 0`, and any `rest` that ends a regex. -/
theorem parseRe_toks (r : Re) (ps rest : List PTok) (n : Nat) (hps : ps.map PTok.tok = r.toksAt 0)
    (hstop : stopB 0 (headTok rest) = true) (hn : 3 * ps.length + 6 ≤ n) :
    parseRe n 0 (ps ++ rest) = .ok (r, rest) :=
  (reOK r).1 0 (Nat.zero_le _) ps rest n hps hstop hn

theorem parseReTop_toks (r : Re) (ps rest : List PTok) (hps : ps.map PTok.tok = r.toksAt 0)
    (hstop : stopB 0 (headTok rest) = true) : parseReTop (ps ++ rest) = .ok (r, rest) :=
  parseRe_toks r ps rest _ hps hstop (by simp only [List.length_append]; omega)

/-! ## Generic list combinators. -/

theorem flatMap_length_ge {α : Type} (f : α → List Tok) :
    ∀ (xs : List α), (∀ x ∈ xs, f x ≠ []) → xs.length ≤ (xs.flatMap f).length := by
  intro xs
  induction xs with
  | nil => intro _; simp
  | cons x xs ih =>
    intro h
    have h1 := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have h2 : 0 < (f x).length := List.length_pos_iff.mpr (h x List.mem_cons_self)
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

theorem map_split {ps : List PTok} {a b : List Tok} (h : ps.map PTok.tok = a ++ b) :
    ∃ p1 p2, ps = p1 ++ p2 ∧ p1.map PTok.tok = a ∧ p2.map PTok.tok = b :=
  List.map_eq_append_iff.mp h

theorem map_cons_split {ps : List PTok} {t : Tok} {b : List Tok} (h : ps.map PTok.tok = t :: b) :
    ∃ p q, ps = p :: q ∧ p.tok = t ∧ q.map PTok.tok = b :=
  List.map_eq_cons_iff.mp h

theorem map_nil_eq {ps : List PTok} (h : ps.map PTok.tok = []) : ps = [] := List.map_eq_nil_iff.mp h

theorem sepBy_length_ge {α : Type} (s : Tok) (f : α → List Tok) :
    ∀ (xs : List α), (∀ x ∈ xs, f x ≠ []) → xs.length ≤ (sepBy s f xs).length := by
  intro xs
  induction xs with
  | nil => intro _; simp
  | cons x xs ih =>
    intro h
    have h2 : 0 < (f x).length := List.length_pos_iff.mpr (h x List.mem_cons_self)
    cases xs with
    | nil => simp only [sepBy, List.length_cons, List.length_nil]; omega
    | cons y ys =>
      have h1 := ih (fun z hz => h z (List.mem_cons_of_mem _ hz))
      rw [sepBy_cons_cons]
      simp only [List.length_append, List.length_cons] at h1 ⊢
      omega

theorem sepEnd_toks {α : Type} (p : List PTok → Except ParseError (α × List PTok)) (sep term : Punct)
    (hst : sep ≠ term) (f : α → List Tok) :
    ∀ (xs : List α), xs ≠ [] →
    (∀ x ∈ xs, ∀ (ps rest : List PTok), ps.map PTok.tok = f x →
      (headTok rest = .punct sep ∨ headTok rest = .punct term) → p (ps ++ rest) = .ok (x, rest)) →
    ∀ (ps rest : List PTok) (n : Nat), ps.map PTok.tok = sepBy (.punct sep) f xs ++ [.punct term] →
      xs.length ≤ n → sepEnd p sep term n (ps ++ rest) = .ok (xs, rest) := by
  intro xs
  induction xs with
  | nil => intro h; exact absurd rfl h
  | cons x xs ih =>
    intro _ hp ps rest n hps hn
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp at hn; omega⟩
    cases xs with
    | nil =>
      obtain ⟨px, q, rfl, hx, hq⟩ := map_split hps
      obtain ⟨pt, q', rfl, ht, hq'⟩ := map_cons_split hq
      cases map_nil_eq hq'
      have h1 := hp x List.mem_cons_self px (pt :: rest) hx (Or.inr (by simp [headTok, ht]))
      have hne : ¬ (Tok.punct term = Tok.punct sep) := fun e => hst (Tok.punct.inj e).symm
      simp only [List.append_assoc, List.singleton_append, sepEnd, h1, bind, Except.bind, ht,
        pure, Except.pure, hne, if_false, if_true]
    | cons y ys =>
      rw [sepBy_cons_cons, List.append_assoc, List.cons_append] at hps
      obtain ⟨px, q, rfl, hx, hq⟩ := map_split hps
      obtain ⟨ps1, q2, rfl, hs, hq2⟩ := map_cons_split hq
      have h1 := hp x List.mem_cons_self px (ps1 :: (q2 ++ rest)) hx (Or.inl (by simp [headTok, hs]))
      have h2 := ih (by simp) (fun z hz => hp z (List.mem_cons_of_mem _ hz)) q2 rest n'
        hq2 (by simp at hn ⊢; omega)
      simp only [List.append_assoc, List.cons_append, sepEnd, h1, bind, Except.bind, hs, if_true,
        h2, pure, Except.pure]

theorem manyUntil_toks {α : Type} (p : List PTok → Except ParseError (α × List PTok))
    (stop : Tok → Bool) (f : α → List Tok) :
    ∀ (xs : List α),
    (∀ x ∈ xs, (∃ t tl, f x = t :: tl ∧ stop t = false) ∧
      ∀ (ps rest : List PTok), ps.map PTok.tok = f x → p (ps ++ rest) = .ok (x, rest)) →
    ∀ (ps rest : List PTok) (n : Nat), ps.map PTok.tok = xs.flatMap f →
      stop (headTok rest) = true → xs.length < n → manyUntil p stop n (ps ++ rest) = .ok (xs, rest) := by
  intro xs
  induction xs with
  | nil =>
    intro _ ps rest n hps hstop hn
    simp only [List.flatMap_nil, List.map_eq_nil_iff] at hps
    subst hps
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp [manyUntil, hstop]
  | cons x xs ih =>
    intro hp ps rest n hps hstop hn
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp at hn; omega⟩
    rw [List.flatMap_cons] at hps
    obtain ⟨px, pr, rfl, hx, hr⟩ := map_split hps
    obtain ⟨⟨t, tl, hft, hts⟩, hpx⟩ := hp x List.mem_cons_self
    have hhead : headTok (px ++ (pr ++ rest)) = t := by
      rw [hft] at hx
      cases px with
      | nil => simp at hx
      | cons a px' => simp only [List.map_cons, List.cons.injEq] at hx; simp [headTok, hx.1]
    have h1 := hpx px (pr ++ rest) hx
    have h2 := ih (fun z hz => hp z (List.mem_cons_of_mem _ hz)) pr rest n' hr hstop
      (by simp at hn; omega)
    simp only [List.append_assoc, manyUntil, hhead, hts, h1, h2, bind, Except.bind, pure,
      Except.pure]
    rfl

/-! ## Datalog. -/

theorem parseArg_tok (a : Arg) (ha : a.wf = true) (p : PTok) (hp : p.tok = a.tok) :
    parseArg p = .ok a := by
  cases a with
  | var v => simp only [Arg.wf] at ha; simp [parseArg, hp, Arg.tok, ha]
  | int z => simp [parseArg, hp, Arg.tok]

theorem argsTail_toks : ∀ (as : List Arg), (∀ a ∈ as, a.wf = true) →
    ∀ (ps rest : List PTok), ps.map PTok.tok = as.flatMap (fun a => [tComma, a.tok]) ++ [tRP] →
      argsTail (ps ++ rest) = .ok (as, rest) := by
  intro as
  induction as with
  | nil =>
    intro _ ps rest hps
    rw [List.flatMap_nil, List.nil_append] at hps
    obtain ⟨p, q, rfl, hp, hq⟩ := map_cons_split hps
    cases map_nil_eq hq
    unfold argsTail
    simp [hp]
  | cons a as ih =>
    intro hwf ps rest hps
    have hps' : ps.map PTok.tok = tComma :: a.tok :: (as.flatMap (fun a => [tComma, a.tok]) ++ [tRP]) := by
      rw [hps]; simp
    obtain ⟨pc, q, rfl, hc, hq⟩ := map_cons_split hps'
    obtain ⟨pa, q2, rfl, ha, hq2⟩ := map_cons_split hq
    have h1 := parseArg_tok a (hwf a List.mem_cons_self) pa ha
    have h2 := ih (fun b hb => hwf b (List.mem_cons_of_mem _ hb)) q2 rest hq2
    unfold argsTail
    simp [hc, h1, h2, bind, Except.bind, pure, Except.pure]

theorem sepBy_single {α : Type} (s : Tok) (g : α → Tok) :
    ∀ (x : α) (xs : List α), sepBy s (fun y => [g y]) (x :: xs) = g x :: xs.flatMap (fun y => [s, g y]) := by
  intro x xs
  induction xs generalizing x with
  | nil => rfl
  | cons y ys ih => rw [sepBy_cons_cons, ih]; rfl

theorem parseArgs_toks (as : List Arg) (hwf : ∀ a ∈ as, a.wf = true) (ps rest : List PTok)
    (hps : ps.map PTok.tok = tLP :: (commaSep (fun x => [Arg.tok x]) as ++ [tRP])) :
    parseArgs (ps ++ rest) = .ok (as, rest) := by
  obtain ⟨pl, q, rfl, hl, hq⟩ := map_cons_split hps
  cases as with
  | nil =>
    obtain ⟨pr, q', rfl, hr, hq'⟩ := map_cons_split hq
    cases map_nil_eq hq'
    simp [parseArgs, expectP, hl, hr, bind, Except.bind, pure, Except.pure]
  | cons a as =>
    rw [commaSep, sepBy_single, List.cons_append] at hq
    obtain ⟨pa, q2, rfl, ha, hq2⟩ := map_cons_split hq
    have h1 := parseArg_tok a (hwf a List.mem_cons_self) pa ha
    have h2 := argsTail_toks as (fun b hb => hwf b (List.mem_cons_of_mem _ hb)) q2 rest hq2
    have hne : ¬ (pa.tok = tRP) := by rw [ha]; cases a <;> simp [Arg.tok]
    simp [parseArgs, expectP, hl, hne, h1, h2, bind, Except.bind, pure, Except.pure]

theorem parseAtom_toks (a : Atom) (hwf : a.wf = true) (ps rest : List PTok)
    (hps : ps.map PTok.tok = a.toks) : parseAtom (ps ++ rest) = .ok (a, rest) := by
  simp only [Atom.wf, Bool.and_eq_true, List.all_eq_true] at hwf
  obtain ⟨pn, q, rfl, hn, hq⟩ := map_cons_split hps
  have h := parseArgs_toks a.args hwf.2 q rest hq
  simp [parseAtom, expectIdent, hn, h, bind, Except.bind, pure, Except.pure]

theorem parseLit_toks (l : Lit) (hwf : l.atom.wf = true) (ps rest : List PTok)
    (hps : ps.map PTok.tok = l.toks) : parseLit (ps ++ rest) = .ok (l, rest) := by
  obtain ⟨ng, a⟩ := l
  cases ng with
  | true =>
    simp only [Lit.toks, if_true, List.singleton_append] at hps
    obtain ⟨pb, q, rfl, hb, hq⟩ := map_cons_split hps
    have h := parseAtom_toks a hwf q rest hq
    simp [parseLit, hb, h, bind, Except.bind, pure, Except.pure]
  | false =>
    simp only [Lit.toks, Bool.false_eq_true, if_false, List.nil_append] at hps
    have h := parseAtom_toks a hwf ps rest hps
    obtain ⟨pn, q, rfl, hn, _⟩ := map_cons_split hps
    simp only [List.cons_append] at h ⊢
    simp [parseLit, hn, h, bind, Except.bind, pure, Except.pure]

theorem parseRule_toks (r : Rule) (hwf : r.wf = true) (ps rest : List PTok)
    (hps : ps.map PTok.tok = (r.toks).tail) : parseRule (ps ++ rest) = .ok (r, rest) := by
  obtain ⟨h, body⟩ := r
  simp only [Rule.wf, Bool.and_eq_true, List.all_eq_true] at hwf
  simp only [Rule.toks, List.tail_cons] at hps
  obtain ⟨ph, q, rfl, hh, hq⟩ := map_split hps
  cases body with
  | nil =>
    simp only [if_true, List.nil_append] at hq
    obtain ⟨pd, q', rfl, hd, hq'⟩ := map_cons_split hq
    cases map_nil_eq hq'
    have h1 := parseAtom_toks h hwf.1 ph (pd :: rest) hh
    simp [parseRule, List.append_assoc, h1, hd, bind, Except.bind, pure, Except.pure]
  | cons l ls =>
    simp only [reduceCtorEq, if_false, List.cons_append] at hq
    obtain ⟨pt, q2, rfl, ht, hq2⟩ := map_cons_split hq
    have h1 := parseAtom_toks h hwf.1 ph (pt :: (q2 ++ rest)) hh
    have hlen : (l :: ls).length ≤ (q2 ++ rest).length := by
      have h3 := len_of_map hq2
      have h4 := sepBy_length_ge tComma Lit.toks (l :: ls) (by
        intro x _; cases x with | mk ng a => cases ng <;> simp [Lit.toks, Atom.toks])
      simp only [commaSep, List.length_append, List.length_singleton] at h3 h4 ⊢
      omega
    have h2 := sepEnd_toks parseLit .comma .dot (by decide) Lit.toks (l :: ls) (by simp)
      (fun x hx ps' rest' hps' _ => parseLit_toks x (hwf.2 x hx) ps' rest' hps')
      q2 rest (q2 ++ rest).length hq2 hlen
    rw [List.length_append] at h2
    simp [parseRule, List.append_assoc, h1, ht, h2, bind, Except.bind, pure, Except.pure]

/-! ## Grammars. -/

theorem parseGSyms_toks : ∀ (ss : List GSym) (ps rest : List PTok), ps.map PTok.tok = ss.map GSym.tok →
    isGSymTok (headTok rest) = false → parseGSyms (ps ++ rest) = (ss, rest) := by
  intro ss
  induction ss with
  | nil =>
    intro ps rest hps hr
    cases map_nil_eq hps
    cases rest with
    | nil => rfl
    | cons t ts =>
      simp only [headTok] at hr
      obtain ⟨tok, pos⟩ := t
      simp only at hr
      cases tok <;> simp_all [parseGSyms, isGSymTok]
  | cons x xs ih =>
    intro ps rest hps hr
    obtain ⟨p, q, rfl, hp, hq⟩ := map_cons_split hps
    have h := ih q rest hq hr
    cases x with
    | nt n => simp only [GSym.tok] at hp; simp [parseGSyms, hp, h]
    | t bs => simp only [GSym.tok] at hp; simp [parseGSyms, hp, h]

theorem parseGAlt_toks (a : List GSym) (ps rest : List PTok) (hps : ps.map PTok.tok = altToks a)
    (hr : isGSymTok (headTok rest) = false) : parseGAlt (ps ++ rest) = .ok (a, rest) := by
  cases a with
  | nil =>
    obtain ⟨p, q, rfl, hp, hq⟩ := map_cons_split hps
    cases map_nil_eq hq
    simp [parseGAlt, hp]
  | cons x xs =>
    have hps' : ps.map PTok.tok = (x :: xs).map GSym.tok := hps
    have h := parseGSyms_toks (x :: xs) ps rest hps' hr
    obtain ⟨p, q, rfl, hp, hq⟩ := map_cons_split hps'
    have hne : ¬ (p.tok = .eps) := by rw [hp]; cases x <;> simp [GSym.tok]
    have hg : isGSymTok p.tok = true := by rw [hp]; cases x <;> simp [GSym.tok, isGSymTok]
    simp only [List.cons_append] at h ⊢
    simp [parseGAlt, hne, hg, h]

theorem altToks_ne_nil (a : List GSym) : altToks a ≠ [] := by
  cases a with
  | nil => simp [altToks]
  | cons x xs => simp [altToks]

theorem altToks_head (a : List GSym) : ∃ t tl, altToks a = t :: tl ∧ t ≠ tSemi := by
  cases a with
  | nil => exact ⟨.eps, [], rfl, by simp⟩
  | cons x xs => exact ⟨x.tok, xs.map GSym.tok, rfl, by cases x <;> simp [GSym.tok]⟩

theorem parseProd_toks (p : Prod) (ps rest : List PTok) (hps : ps.map PTok.tok = p.toks) :
    parseProd (ps ++ rest) = .ok (p, rest) := by
  obtain ⟨lhs, alts⟩ := p
  obtain ⟨pl, q, rfl, hl, hq⟩ := map_cons_split hps
  obtain ⟨pa, q2, rfl, ha, hq2⟩ := map_cons_split hq
  cases alts with
  | nil =>
    obtain ⟨ps', q3, rfl, hs, hq3⟩ := map_cons_split hq2
    cases map_nil_eq hq3
    simp [parseProd, expectIdent, expectP, hl, ha, hs, bind, Except.bind, pure, Except.pure]
  | cons a as =>
    have hlen : (a :: as).length ≤ (q2 ++ rest).length := by
      have h3 := len_of_map hq2
      have h4 := sepBy_length_ge tBar altToks (a :: as) (fun x _ => altToks_ne_nil x)
      simp only [barSep, List.length_append, List.length_singleton] at h3 h4 ⊢
      omega
    have h2 := sepEnd_toks parseGAlt .bar .semi (by decide) altToks (a :: as) (by simp)
      (fun x _ ps' rest' hps' hr' => parseGAlt_toks x ps' rest' hps' (by
        rcases hr' with h | h <;> rw [h] <;> rfl))
      q2 rest (q2 ++ rest).length hq2 hlen
    obtain ⟨t, tl, ht, htn⟩ : ∃ t tl, barSep (a :: as) ++ [tSemi] = t :: tl ∧ t ≠ tSemi := by
      obtain ⟨t, tl, he, hn⟩ := altToks_head a
      cases as with
      | nil => exact ⟨t, tl ++ [tSemi], by simp [barSep, sepBy, he], hn⟩
      | cons b bs => exact ⟨t, _, by rw [barSep, sepBy_cons_cons, he]; rfl, hn⟩
    rw [ht] at hq2
    obtain ⟨pt, q4, rfl, hpt, _⟩ := map_cons_split hq2
    have hns : ¬ (pt.tok = tSemi) := by rw [hpt]; exact htn
    simp only [List.cons_append] at h2 ⊢
    simp [parseProd, expectIdent, expectP, hl, ha, hns, h2, bind, Except.bind, pure, Except.pure,
      -List.length_append, -List.length_cons]

/-! ## Budgets, claims, declarations. -/

theorem parseAgg_toks (a : Agg) (ps rest : List PTok) (hps : ps.map PTok.tok = a.toks) :
    parseAgg (ps ++ rest) = .ok (a, rest) := by
  cases a with
  | sum p i =>
    simp only [Agg.toks, List.map_eq_cons_iff, List.map_eq_nil_iff] at hps
    obtain ⟨a1, _, rfl, h1, a2, _, rfl, h2, a3, _, rfl, h3, a4, _, rfl, h4, a5, _, rfl, h5,
      a6, _, rfl, h6, rfl⟩ := hps
    simp [parseAgg, expectP, expectIdent, expectNat, h1, h2, h3, h4, h5, h6, bind, Except.bind,
      pure, Except.pure]
  | count p =>
    simp only [Agg.toks, List.map_eq_cons_iff, List.map_eq_nil_iff] at hps
    obtain ⟨a1, _, rfl, h1, a2, _, rfl, h2, a3, _, rfl, h3, a4, _, rfl, h4, rfl⟩ := hps
    simp [parseAgg, expectP, expectIdent, h1, h2, h3, h4, bind, Except.bind, pure, Except.pure]

theorem parseClaim_toks (c : Claim) (ps rest : List PTok) (hps : ps.map PTok.tok = c.toks) :
    parseClaim (ps ++ rest) = .ok (c, rest) := by
  cases c <;>
  · simp only [Claim.toks, List.map_eq_cons_iff, List.map_eq_nil_iff] at hps
    first
    | obtain ⟨a1, _, rfl, h1, a2, _, rfl, h2, a3, _, rfl, h3, a4, _, rfl, h4, a5, _, rfl, h5,
        a6, _, rfl, h6, rfl⟩ := hps
      simp [parseClaim, expectP, expectIdent, expectKw, h1, h2, h3, h4, h5, h6, bind, Except.bind,
        pure, Except.pure]
    | obtain ⟨a1, _, rfl, h1, a2, _, rfl, h2, a3, _, rfl, h3, a4, _, rfl, h4, rfl⟩ := hps
      simp [parseClaim, expectP, expectIdent, h1, h2, h3, h4, bind, Except.bind, pure, Except.pure]

theorem parseDecl_toks (d : Decl) (hwf : d.wf = true) (ps rest : List PTok)
    (hps : ps.map PTok.tok = d.toks) : parseDecl (ps ++ rest) = .ok (d, rest) := by
  cases d with
  | pattern n r =>
    simp only [Decl.toks] at hps
    obtain ⟨p1, q1, rfl, h1, hq1⟩ := map_cons_split hps
    obtain ⟨p2, q2, rfl, h2, hq2⟩ := map_cons_split hq1
    obtain ⟨p3, q3, rfl, h3, hq3⟩ := map_cons_split hq2
    obtain ⟨pr, q4, rfl, hr, hq4⟩ := map_split hq3
    obtain ⟨p5, q5, rfl, h5, hq5⟩ := map_cons_split hq4
    cases map_nil_eq hq5
    have hre := parseReTop_toks r pr (p5 :: rest) hr (by simp [headTok, h5, stopB, startsUnary, isPostfixTok])
    simp only [List.cons_append, List.append_assoc] at hre ⊢
    simp [parseDecl, expectIdent, expectP, h1, h2, h3, h5, hre, bind, Except.bind, pure, Except.pure]
  | grammar n prods =>
    simp only [Decl.toks] at hps
    obtain ⟨p1, q1, rfl, h1, hq1⟩ := map_cons_split hps
    obtain ⟨p2, q2, rfl, h2, hq2⟩ := map_cons_split hq1
    obtain ⟨p3, q3, rfl, h3, hq3⟩ := map_cons_split hq2
    obtain ⟨pr, q4, rfl, hr, hq4⟩ := map_split hq3
    obtain ⟨p5, q5, rfl, h5, hq5⟩ := map_cons_split hq4
    cases map_nil_eq hq5
    have hlen : prods.length < (pr ++ p5 :: rest).length := by
      have h4 := flatMap_length_ge Prod.toks prods (fun x _ => by simp [Prod.toks])
      have h6 := len_of_map hr
      simp only [List.length_append, List.length_cons] at h4 h6 ⊢
      omega
    have hm := manyUntil_toks parseProd (· = .punct .rbrace) Prod.toks prods
      (fun x _ => ⟨⟨.ident x.lhs, _, rfl, by simp⟩, fun ps' rest' hps' => parseProd_toks x ps' rest' hps'⟩)
      pr (p5 :: rest) _ hr (by simp [headTok, h5]) hlen
    simp only [List.cons_append, List.append_assoc] at hm ⊢
    simp [parseDecl, expectIdent, expectP, h1, h2, h3, h5, hm, bind, Except.bind, pure, Except.pure,
      -List.length_append, -List.length_cons]
  | rule r =>
    simp only [Decl.wf] at hwf
    simp only [Decl.toks, Rule.toks] at hps
    obtain ⟨p1, q1, rfl, h1, hq1⟩ := map_cons_split hps
    have h := parseRule_toks r hwf q1 rest (by rw [hq1]; rfl)
    simp [parseDecl, h1, h, bind, Except.bind, pure, Except.pure]
  | budget n a b =>
    simp only [Decl.toks] at hps
    obtain ⟨p1, q1, rfl, h1, hq1⟩ := map_cons_split hps
    obtain ⟨p2, q2, rfl, h2, hq2⟩ := map_cons_split hq1
    obtain ⟨p3, q3, rfl, h3, hq3⟩ := map_cons_split hq2
    obtain ⟨pa, q4, rfl, ha, hq4⟩ := map_split hq3
    simp only [List.map_eq_cons_iff, List.map_eq_nil_iff] at hq4
    obtain ⟨p5, _, rfl, h5, p6, _, rfl, h6, p7, _, rfl, h7, rfl⟩ := hq4
    have hag := parseAgg_toks a pa (p5 :: p6 :: p7 :: rest) ha
    simp only [List.cons_append, List.append_assoc, List.nil_append] at hag ⊢
    simp [parseDecl, expectIdent, expectP, expectNat, h1, h2, h3, h5, h6, h7, hag, bind,
      Except.bind, pure, Except.pure]
  | policy n cs =>
    simp only [Decl.toks] at hps
    obtain ⟨p1, q1, rfl, h1, hq1⟩ := map_cons_split hps
    obtain ⟨p2, q2, rfl, h2, hq2⟩ := map_cons_split hq1
    obtain ⟨p3, q3, rfl, h3, hq3⟩ := map_cons_split hq2
    obtain ⟨pr, q4, rfl, hr, hq4⟩ := map_split hq3
    obtain ⟨p5, q5, rfl, h5, hq5⟩ := map_cons_split hq4
    cases map_nil_eq hq5
    have hlen : cs.length < (pr ++ p5 :: rest).length := by
      have h4 := flatMap_length_ge Claim.toks cs (fun x _ => by cases x <;> simp [Claim.toks])
      have h6 := len_of_map hr
      simp only [List.length_append, List.length_cons] at h4 h6 ⊢
      omega
    have hm := manyUntil_toks parseClaim (· = .punct .rbrace) Claim.toks cs
      (fun x _ => ⟨by cases x <;> exact ⟨_, _, rfl, by simp⟩,
        fun ps' rest' hps' => parseClaim_toks x ps' rest' hps'⟩)
      pr (p5 :: rest) _ hr (by simp [headTok, h5]) hlen
    simp only [List.cons_append, List.append_assoc] at hm ⊢
    simp [parseDecl, expectIdent, expectP, h1, h2, h3, h5, hm, bind, Except.bind, pure, Except.pure,
      -List.length_append, -List.length_cons]

theorem decl_toks_head (d : Decl) : ∃ t tl, d.toks = t :: tl ∧ t ≠ .eof := by
  cases d <;> exact ⟨_, _, rfl, by simp⟩

/-- ⚑ **The token-level round trip.** A well-formed policy's printed tokens, positioned anywhere,
followed by `eof`, parse back to the policy. -/
theorem parseTokens_toks (p : Policy) (hwf : p.wf = true) (ps : List PTok) (e : PTok)
    (he : e.tok = .eof) (hps : ps.map PTok.tok = p.toks) : parseTokens (ps ++ [e]) = .ok p := by
  obtain ⟨ds⟩ := p
  simp only [Policy.wf, List.all_eq_true] at hwf
  have hlen : ds.length < (ps ++ [e]).length := by
    have h4 := flatMap_length_ge Decl.toks ds (fun x _ => by
      obtain ⟨t, tl, h, _⟩ := decl_toks_head x; rw [h]; simp)
    have h6 := len_of_map hps
    simp only [Policy.toks, List.length_append, List.length_singleton] at h4 h6 ⊢
    omega
  have hm := manyUntil_toks parseDecl (· = .eof) Decl.toks ds
    (fun x hx => ⟨by obtain ⟨t, tl, h, hn⟩ := decl_toks_head x; exact ⟨t, tl, h, by simp [hn]⟩,
      fun ps' rest' hps' => parseDecl_toks x (hwf x hx) ps' rest' hps'⟩)
    ps [e] _ hps (by simp [headTok, he]) hlen
  simp [parseTokens, hm, he, bind, Except.bind, pure, Except.pure, -List.length_append]

#assert_all_clean [postfixLoop_ops, toks_head, reOK, parseRe_toks, parseReTop_toks, sepEnd_toks,
  manyUntil_toks, parseArgs_toks, parseAtom_toks, parseLit_toks, parseRule_toks, parseGAlt_toks,
  parseProd_toks, parseAgg_toks, parseClaim_toks, parseDecl_toks, parseTokens_toks]

end Dregg2.Policy
