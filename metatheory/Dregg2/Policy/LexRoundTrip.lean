/-
# Dregg2.Policy.LexRoundTrip — the lexer inverts the token spelling.

The character-level half of `parse_print_roundtrip`. `render ps` writes each token's canonical text
(`Tok.text`) followed by its separator; `Good ps` says the separators are whitespace, that an EMPTY
separator only appears where `Tok.delim` says the first token's lexer stops at the next token's
first character, and that each token is well formed (`TokWF`: identifiers are identifiers, bytes
are bytes, no `eof`). Then `lexChars (render ps)` returns exactly `ps.map Prod.fst` followed by
`eof` (`lexChars_render`), positions aside.

The printer's layout is `Good` for every well-formed policy (`layout_good`), because the only
empty separators it emits come from `sepWithin`, which asks `Tok.delim` itself.
-/
import Dregg2.Policy.Pretty
import Dregg2.Tactics

namespace Dregg2.Policy

set_option autoImplicit false

/-! ## Character facts. -/

theorem toNat_ofNat_lt {b : Nat} (hb : b < 55296) : (Char.ofNat b).toNat = b := by
  unfold Char.ofNat
  rw [dif_pos (Or.inl hb)]
  simp [Char.ofNatAux, Char.toNat]

theorem ofNat_ne_of_toNat {b : Nat} {c : Char} (hb : b < 55296) (h : b ≠ c.toNat) : Char.ofNat b ≠ c := by
  intro e; apply h; rw [← e, toNat_ofNat_lt hb]

theorem hex_facts : ∀ d, d < 16 → hexVal (hexChar d) = d ∧ isHexDigit (hexChar d) = true := by
  decide

theorem digit_facts : ∀ d, d < 10 → (digitChar d).isDigit = true ∧ (digitChar d).toNat - 48 = d ∧
    isIdStart (digitChar d) = false ∧ isWs (digitChar d) = false ∧ digitChar d ≠ '#' := by
  decide

theorem hexVal_hex2 {b : Nat} (hb : b < 256) :
    hexVal (hexChar (b / 16)) * 16 + hexVal (hexChar (b % 16)) = b := by
  rw [(hex_facts (b / 16) (by omega)).1, (hex_facts (b % 16) (by omega)).1]
  omega

/-! ## `spanP`. -/

theorem spanP_append (p : Char → Bool) : ∀ (a rest : List Char), a.all p = true →
    (∀ c cs, rest = c :: cs → p c = false) → spanP p (a ++ rest) = (a, rest) := by
  intro a
  induction a with
  | nil =>
    intro rest _ hr
    cases rest with
    | nil => rfl
    | cons c cs => simp [spanP, hr c cs rfl]
  | cons x xs ih =>
    intro rest ha hr
    simp only [List.all_cons, Bool.and_eq_true] at ha
    simp [spanP, ha.1, ih rest ha.2 hr]

/-! ## Numbers. -/

theorem natDigits_spec : ∀ n, (natDigits n).all Char.isDigit = true ∧ natDigits n ≠ [] ∧
    digitsVal (natDigits n) = n ∧ (∀ c cs, natDigits n = c :: cs → isIdStart c = false ∧
      isWs c = false ∧ c ≠ '#' ∧ c ≠ '\n') := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 10
    · rw [natDigits, dif_pos h]
      obtain ⟨d1, d2, d3, d4, d5⟩ := digit_facts n h
      refine ⟨by simp [d1], by simp, ?_, ?_⟩
      · simp [digitsVal, d2]
      · intro c cs he; simp at he; obtain ⟨rfl, -⟩ := he
        exact ⟨d3, d4, d5, by intro e; rw [e] at d1; exact absurd d1 (by decide)⟩
    · rw [natDigits, dif_neg h]
      obtain ⟨i1, i2, i3, i4⟩ := ih (n / 10) (by omega)
      obtain ⟨d1, d2, -, -, -⟩ := digit_facts (n % 10) (by omega)
      refine ⟨by simp [i1, d1], by simp, ?_, ?_⟩
      · simp only [digitsVal, List.foldl_append, List.foldl_cons, List.foldl_nil] at i3 ⊢
        rw [i3, d2]; omega
      · intro c cs he
        obtain ⟨c', cs', he'⟩ : ∃ c' cs', natDigits (n / 10) = c' :: cs' := by
          cases hh : natDigits (n / 10) with
          | nil => exact absurd hh i2
          | cons c' cs' => exact ⟨c', cs', rfl⟩
        rw [he'] at he; simp at he; obtain ⟨rfl, -⟩ := he
        exact i4 _ cs' he'

/-! ## String literals. -/

theorem lexStr_raw {c : Char} {rest : List Char} (h3 : c ≠ '\\') (h1 : c ≠ '"') (h2 : c ≠ '\n')
    (h4 : c.toNat < 128) : lexStr (c :: rest) = (lexStr rest).map (fun p => (c.toNat :: p.1, p.2)) := by
  rw [lexStr.eq_def]
  simp [h1, h2, h3, h4]

theorem lexStr_byte {b : Nat} (hb : b < 256) (rest : List Char) :
    lexStr (strByte b ++ rest) = (lexStr rest).map (fun p => (b :: p.1, p.2)) := by
  unfold strByte
  by_cases e34 : b = 34
  · subst e34; simp [lexStr]
  · by_cases e92 : b = 92
    · subst e92; simp [lexStr]
    · simp only [beq_iff_eq, e34, e92, if_false]
      by_cases hr : strRaw b = true
      · simp only [hr, if_true, List.singleton_append]
        simp only [strRaw, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hr
        have ht := toNat_ofNat_lt (b := b) (by omega)
        rw [lexStr_raw (ofNat_ne_of_toNat (by omega) (by simp; omega))
          (ofNat_ne_of_toNat (by omega) (by simp; omega)) (ofNat_ne_of_toNat (by omega) (by simp; omega))
          (by omega), ht]
      · simp only [hr, Bool.false_eq_true, if_false, hex2, List.cons_append, List.nil_append]
        obtain ⟨-, h1⟩ := hex_facts (b / 16) (by omega)
        obtain ⟨-, h2⟩ := hex_facts (b % 16) (by omega)
        simp [lexStr, h1, h2, hexVal_hex2 hb]

theorem lexStr_bytes : ∀ (bs : List Nat), bs.all isByte = true → ∀ rest : List Char,
    lexStr (bs.flatMap strByte ++ '"' :: rest) = .ok (bs, rest) := by
  intro bs
  induction bs with
  | nil => intro _ rest; simp [lexStr]
  | cons b bs ih =>
    intro h rest
    simp only [List.all_cons, Bool.and_eq_true, isByte, decide_eq_true_eq] at h
    rw [List.flatMap_cons, List.append_assoc, lexStr_byte h.1, ih h.2 rest]
    rfl

/-! ## Classes. -/

theorem clsByte_spec {b : Nat} (hb : b < 256) (rest : List Char) :
    lexClsByte (clsByte b ++ rest) = .ok (b, rest) ∧
    ∃ c cs, clsByte b = c :: cs ∧ c ≠ ']' ∧ c ≠ '-' ∧ c ≠ '^' := by
  unfold clsByte
  by_cases hs : clsSpecial b = true
  · simp only [hs, if_true]
    have ht := toNat_ofNat_lt (b := b) (by omega)
    simp only [clsSpecial, Bool.or_eq_true, beq_iff_eq] at hs
    refine ⟨?_, ⟨_, _, rfl, by decide, by decide, by decide⟩⟩
    rcases hs with (((h | h) | h) | h) | h <;> subst h <;> simp [lexClsByte]
  · simp only [hs, Bool.false_eq_true, if_false]
    by_cases hr : clsRaw b = true
    · simp only [hr, if_true, List.singleton_append]
      have hr' := hr
      simp only [clsRaw, clsSpecial, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hr'
      have ht := toNat_ofNat_lt (b := b) (by omega)
      have n1 : Char.ofNat b ≠ ']' := ofNat_ne_of_toNat (by omega) (by simp; omega)
      have n2 : Char.ofNat b ≠ '-' := ofNat_ne_of_toNat (by omega) (by simp; omega)
      have n3 : Char.ofNat b ≠ '\\' := ofNat_ne_of_toNat (by omega) (by simp; omega)
      have n4 : Char.ofNat b ≠ '\n' := ofNat_ne_of_toNat (by omega) (by simp; omega)
      have n5 : Char.ofNat b ≠ '^' := ofNat_ne_of_toNat (by omega) (by simp; omega)
      refine ⟨?_, ⟨_, _, rfl, n1, n2, n5⟩⟩
      rw [lexClsByte.eq_def]
      simp [n1, n2, n3, n4, ht]
      omega
    · simp only [hr, Bool.false_eq_true, if_false, hex2, List.cons_append, List.nil_append]
      obtain ⟨-, h1⟩ := hex_facts (b / 16) (by omega)
      obtain ⟨-, h2⟩ := hex_facts (b % 16) (by omega)
      refine ⟨?_, ⟨_, _, rfl, by decide, by decide, by decide⟩⟩
      simp [lexClsByte, lexHex, h1, h2, hexVal_hex2 hb]

theorem lexClsItems_close (rest : List Char) : lexClsItems (']' :: rest) = .ok ([], rest) := by
  rw [lexClsItems]

theorem lexClsItems_single {lo : Nat} (hlo : lo < 256) (R : List Char) (hR : ∀ cs, R ≠ '-' :: cs) :
    lexClsItems (clsByte lo ++ R) = (lexClsItems R).map (fun p => ((lo, lo) :: p.1, p.2)) := by
  obtain ⟨h, c, cs, he, hc1, -, -⟩ := clsByte_spec hlo R
  rw [he, List.cons_append] at h ⊢
  rw [lexClsItems]
  · split
    · rename_i e heq; rw [h] at heq; cases heq
    · rename_i lo' rest' heq
      rw [h] at heq; cases heq
      simp only []
      split
      · exact absurd rfl (hR _)
      · rfl
  · exact hc1

theorem lexClsItems_range {lo hi : Nat} (hlo : lo < 256) (hhi : hi < 256) (R : List Char) :
    lexClsItems (clsByte lo ++ '-' :: (clsByte hi ++ R)) =
      (lexClsItems R).map (fun p => ((lo, hi) :: p.1, p.2)) := by
  obtain ⟨h, c, cs, he, hc1, -, -⟩ := clsByte_spec hlo ('-' :: (clsByte hi ++ R))
  obtain ⟨h', -⟩ := clsByte_spec hhi R
  rw [he, List.cons_append] at h ⊢
  rw [lexClsItems]
  · split
    · rename_i e heq; rw [h] at heq; cases heq
    · rename_i lo' rest' heq
      rw [h] at heq; cases heq
      simp only
      split
      · rename_i e heq2; rw [h'] at heq2; cases heq2
      · rename_i hi' rest3 heq2; rw [h'] at heq2; cases heq2; rfl
  · exact hc1

theorem rangeText_head (p : Nat × Nat) (hp : p.1 < 256) :
    ∃ c cs, rangeText p = c :: cs ∧ c ≠ ']' ∧ c ≠ '-' ∧ c ≠ '^' := by
  obtain ⟨-, c, cs, he, h1, h2, h3⟩ := clsByte_spec hp []
  exact ⟨c, _, by rw [rangeText, he]; rfl, h1, h2, h3⟩

theorem lexClsItems_ranges : ∀ (rs : List (Nat × Nat)), rs.all (fun p => isByte p.1 && isByte p.2) = true →
    ∀ rest : List Char, lexClsItems (rs.flatMap rangeText ++ ']' :: rest) = .ok (rs, rest) := by
  intro rs
  induction rs with
  | nil => intro _ rest; exact lexClsItems_close rest
  | cons p ps ih =>
    intro h rest
    simp only [List.all_cons, Bool.and_eq_true, isByte, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have hR : ∀ cs, ps.flatMap rangeText ++ ']' :: rest ≠ '-' :: cs := by
      intro cs e
      cases ps with
      | nil => simp at e
      | cons q qs =>
        simp only [List.all_cons, Bool.and_eq_true, isByte, decide_eq_true_eq] at h3
        obtain ⟨c, cs', he, -, hc, -⟩ := rangeText_head q h3.1.1
        rw [List.flatMap_cons, he] at e; simp at e; exact hc e.1
    obtain ⟨lo, hi⟩ := p
    rw [List.flatMap_cons, List.append_assoc]
    have hrt : rangeText (lo, hi) = clsByte lo ++ (if lo == hi then [] else '-' :: clsByte hi) := rfl
    rw [hrt]
    by_cases e : lo = hi
    · subst e
      simp only [beq_self_eq_true, if_true, List.append_nil]
      rw [lexClsItems_single h1 _ hR, ih h3 rest]; rfl
    · simp only [beq_iff_eq, e, if_false, List.cons_append, List.append_assoc]
      rw [lexClsItems_range h1 h2, ih h3 rest]; rfl

theorem lexClass_plain {ds : List Char} (h : ∀ cs, ds ≠ '^' :: cs) :
    lexClass ds = (lexClsItems ds).map (fun p => (.cls false p.1, p.2)) := by
  cases ds with
  | nil => rfl
  | cons c cs =>
    by_cases hc : c = '^'
    · subst hc; exact absurd rfl (h cs)
    · simp [lexClass, hc]

/-! ## One token. -/

/-- A token the printer may emit. -/
def TokWF : Tok → Bool
  | .ident s => isIdent s
  | .str bs => bs.all isByte
  | .cls _ rs => rs.all (fun p => isByte p.1 && isByte p.2)
  | .eof => false
  | _ => true

theorem idStart_idChar {c : Char} (h : isIdStart c = true) : isIdChar c = true := by
  simp only [isIdStart, isIdChar, Bool.or_eq_true, Char.isAlphanum] at h ⊢
  rcases h with h | h
  · left; simp [h]
  · right; exact h

theorem ident_text {s : String} (h : isIdent s = true) :
    ∃ c cs, s.toList = c :: cs ∧ isIdStart c = true ∧ (c :: cs).all isIdChar = true := by
  unfold isIdent at h
  cases he : s.toList with
  | nil => rw [he] at h; simp at h
  | cons c cs =>
    rw [he] at h
    simp only [Bool.and_eq_true] at h
    exact ⟨c, cs, rfl, h.1, by simp [idStart_idChar h.1, h.2]⟩

theorem lexToken_text (t : Tok) (hwf : TokWF t = true) (rest : List Char)
    (hd : ∀ c cs, rest = c :: cs → t.delim c = true) : lexToken (t.text ++ rest) = .ok (t, rest) := by
  cases t with
  | ident s =>
    obtain ⟨c, cs, he, hs, ha⟩ := ident_text hwf
    simp only [Tok.text, he, List.cons_append]
    have hsp := spanP_append isIdChar (c :: cs) rest ha (fun c' cs' h => by
      have := hd c' cs' h; simp only [Tok.delim, Bool.not_eq_true'] at this; exact this)
    simp only [List.cons_append] at hsp
    simp [lexToken, hs, hsp, ← he]
  | int z =>
    cases z with
    | ofNat n =>
      obtain ⟨h1, h2, h3, h4⟩ := natDigits_spec n
      obtain ⟨c, cs, he⟩ : ∃ c cs, natDigits n = c :: cs := by
        cases hh : natDigits n with
        | nil => exact absurd hh h2
        | cons c cs => exact ⟨c, cs, rfl⟩
      obtain ⟨i1, -, -, -⟩ := h4 c cs he
      have hdig : c.isDigit = true := by rw [he] at h1; simp at h1; exact h1.1
      have hsp := spanP_append Char.isDigit (natDigits n) rest h1 (fun c' cs' h => by
        have := hd c' cs' h; simp only [Tok.delim, Bool.not_eq_true'] at this; exact this)
      simp only [Tok.text, intText]
      rw [he] at hsp ⊢
      simp only [List.cons_append] at hsp ⊢
      simp [lexToken, i1, hdig, hsp, ← he, h3]
    | negSucc n =>
      obtain ⟨h1, h2, h3, h4⟩ := natDigits_spec (n + 1)
      obtain ⟨c, cs, he⟩ : ∃ c cs, natDigits (n + 1) = c :: cs := by
        cases hh : natDigits (n + 1) with
        | nil => exact absurd hh h2
        | cons c cs => exact ⟨c, cs, rfl⟩
      have hdig : c.isDigit = true := by rw [he] at h1; simp at h1; exact h1.1
      have hsp := spanP_append Char.isDigit (natDigits (n + 1)) rest h1 (fun c' cs' h => by
        have := hd c' cs' h; simp only [Tok.delim, Bool.not_eq_true'] at this; exact this)
      simp only [Tok.text, intText, List.cons_append]
      rw [he] at hsp ⊢
      simp only [List.cons_append] at hsp ⊢
      simp [lexToken, isIdStart, hdig, hsp, ← he, h3]
      rw [Int.negSucc_eq]; omega
  | str bs =>
    simp only [TokWF] at hwf
    simp only [Tok.text, List.cons_append, List.append_assoc]
    simp [lexToken, isIdStart, lexStr_bytes bs hwf rest]; rfl
  | cls ng rs =>
    simp only [TokWF] at hwf
    have hi := lexClsItems_ranges rs hwf rest
    cases ng with
    | true =>
      simp only [Tok.text, if_true, List.cons_append, List.append_assoc]
      simp [lexToken, isIdStart, lexClass, hi]; rfl
    | false =>
      simp only [Tok.text, Bool.false_eq_true, if_false, List.nil_append, List.cons_append,
        List.append_assoc]
      have hnc : ∀ cs, rs.flatMap rangeText ++ ']' :: rest ≠ '^' :: cs := by
        intro cs e
        cases rs with
        | nil => simp at e
        | cons q qs =>
          simp only [List.all_cons, Bool.and_eq_true, isByte, decide_eq_true_eq] at hwf
          obtain ⟨c, cs', he, -, -, hc⟩ := rangeText_head q hwf.1.1
          rw [List.flatMap_cons, he] at e; simp at e; exact hc e.1
      simp [lexToken, isIdStart, lexClass_plain hnc, hi]; rfl
  | esc e => cases e <;> simp [Tok.text, ClassEsc.char, lexToken, isIdStart]
  | eps => simp [Tok.text, lexToken, isIdStart]
  | punct p =>
    cases p <;> simp [Tok.text, Punct.text, lexToken, isIdStart]
    -- the colon: the next character is not `-`
    cases rest with
    | nil => rfl
    | cons c cs =>
      have := hd c cs rfl
      simp only [Tok.delim, bne_iff_ne, ne_eq] at this
      simp [this]
  | eof => simp [TokWF] at hwf

/-! ## The main loop. -/

theorem idStart_not_ws {c : Char} (h : isIdStart c = true) : isWs c = false ∧ c ≠ '#' ∧ c ≠ '\n' := by
  refine ⟨?_, ?_, ?_⟩
  · cases hw : isWs c
    · rfl
    · exfalso
      simp only [isWs, Bool.or_eq_true, beq_iff_eq] at hw
      rcases hw with ((rfl | rfl) | rfl) | rfl <;> revert h <;> decide
  · rintro rfl; revert h; decide
  · rintro rfl; revert h; decide

theorem text_head (t : Tok) (hwf : TokWF t = true) :
    ∃ c cs, t.text = c :: cs ∧ isWs c = false ∧ c ≠ '#' ∧ c ≠ '\n' := by
  cases t with
  | ident s =>
    obtain ⟨c, cs, he, hs, -⟩ := ident_text hwf
    exact ⟨c, cs, he, idStart_not_ws hs⟩
  | int z =>
    cases z with
    | ofNat n =>
      obtain ⟨-, h2, -, h4⟩ := natDigits_spec n
      cases hh : natDigits n with
      | nil => exact absurd hh h2
      | cons c cs => obtain ⟨-, a, b, d⟩ := h4 c cs hh; exact ⟨c, cs, by simp [Tok.text, intText, hh], a, b, d⟩
    | negSucc n => exact ⟨'-', _, rfl, by decide, by decide, by decide⟩
  | str bs => exact ⟨'"', _, rfl, by decide, by decide, by decide⟩
  | cls ng rs => exact ⟨'[', _, rfl, by decide, by decide, by decide⟩
  | esc e => exact ⟨'\\', _, rfl, by decide, by decide, by decide⟩
  | eps => exact ⟨'ε', _, rfl, by decide, by decide, by decide⟩
  | punct p => cases p <;> exact ⟨_, _, rfl, by decide, by decide, by decide⟩
  | eof => simp [TokWF] at hwf

theorem delim_ws (t : Tok) {c : Char} (hc : isWs c = true) : t.delim c = true := by
  simp only [isWs, Bool.or_eq_true, beq_iff_eq] at hc
  cases t with
  | ident s => rcases hc with ((rfl | rfl) | rfl) | rfl <;> rfl
  | int z => rcases hc with ((rfl | rfl) | rfl) | rfl <;> rfl
  | punct p => cases p <;> rcases hc with ((rfl | rfl) | rfl) | rfl <;> decide
  | _ => rfl

/-- Whitespace is skipped, one fuel unit per character. -/
theorem lexAux_ws : ∀ (s : List Char), s.all isWs = true → ∀ (fuel : Nat) (pos : Pos) (cs : List Char),
    ∃ pos', lexAux (fuel + s.length) pos (s ++ cs) = lexAux fuel pos' cs := by
  intro s
  induction s with
  | nil => intro _ fuel pos cs; exact ⟨pos, rfl⟩
  | cons c s ih =>
    intro h fuel pos cs
    simp only [List.all_cons, Bool.and_eq_true] at h
    by_cases hn : c = '\n'
    · subst hn
      obtain ⟨pos', hp⟩ := ih h.2 fuel ⟨pos.line + 1, 1⟩ cs
      refine ⟨pos', ?_⟩
      rw [show fuel + (('\n' :: s).length) = (fuel + s.length) + 1 by simp; omega]
      simp only [List.cons_append, lexAux]
      simpa using hp
    · obtain ⟨pos', hp⟩ := ih h.2 fuel ⟨pos.line, pos.col + 1⟩ cs
      refine ⟨pos', ?_⟩
      rw [show fuel + ((c :: s).length) = (fuel + s.length) + 1 by simp; omega]
      simp only [List.cons_append, lexAux]
      simp [hn, h.1, hp]

/-- Adjacent tokens with an empty separator may be glued. -/
def Adj : List (Tok × List Char) → Prop
  | (t, s) :: (t', s') :: rest => (s = [] → t.delim (t'.text.headD ' ') = true) ∧ Adj ((t', s') :: rest)
  | _ => True

/-- **`Good ps`** — a rendering the lexer reads back exactly. -/
def Good (ps : List (Tok × List Char)) : Prop :=
  (∀ p ∈ ps, TokWF p.1 = true ∧ p.2.all isWs = true) ∧ Adj ps

theorem Adj.tail {p : Tok × List Char} {ps : List (Tok × List Char)} (h : Adj (p :: ps)) : Adj ps := by
  obtain ⟨t, s⟩ := p
  cases ps with
  | nil => trivial
  | cons q qs => obtain ⟨t', s'⟩ := q; exact h.2

theorem render_cons (t : Tok) (s : List Char) (ps : List (Tok × List Char)) :
    render ((t, s) :: ps) = t.text ++ (s ++ render ps) := by
  simp [render]

/-- ⚑ **The lexer inverts the rendering.** -/
theorem lexAux_render : ∀ (ps : List (Tok × List Char)), Good ps → ∀ (fuel : Nat) (pos : Pos),
    (render ps).length < fuel →
    ∃ pts, lexAux fuel pos (render ps) = .ok pts ∧ pts.map PTok.tok = ps.map Prod.fst ++ [.eof] := by
  intro ps
  induction ps with
  | nil =>
    intro _ fuel pos hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [render] at hf; omega⟩
    exact ⟨[⟨.eof, pos⟩], by simp [render, lexAux], rfl⟩
  | cons p ps ih =>
    intro hg fuel pos hf
    obtain ⟨t, s⟩ := p
    obtain ⟨hall, hadj⟩ := hg
    have hgt : Good ps := ⟨fun q hq => hall q (List.mem_cons_of_mem _ hq), hadj.tail⟩
    obtain ⟨hwf, hws⟩ := hall (t, s) List.mem_cons_self
    obtain ⟨c, cs, hte, hcw, hch, hcn⟩ := text_head t hwf
    -- the token
    have htok : lexToken (t.text ++ (s ++ render ps)) = .ok (t, s ++ render ps) := by
      apply lexToken_text t hwf
      intro c' cs' he
      cases s with
      | cons d ds =>
        simp only [List.cons_append, List.cons.injEq] at he
        rw [← he.1]
        exact delim_ws t (by simp only [List.all_cons, Bool.and_eq_true] at hws; exact hws.1)
      | nil =>
        cases ps with
        | nil => simp [render] at he
        | cons q qs =>
          obtain ⟨t', s'⟩ := q
          have hq := (hall (t', s') (by simp)).1
          obtain ⟨c'', cs'', he', -⟩ := text_head t' hq
          have hd := hadj.1 rfl
          rw [he'] at hd
          simp only [List.nil_append, render_cons, he', List.cons_append, List.cons.injEq] at he
          rw [← he.1]; exact hd
    rw [hte] at htok
    rw [render_cons, hte] at hf ⊢
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hlen : (s ++ render ps).length < (c :: (cs ++ (s ++ render ps))).length := by simp; omega
    obtain ⟨pos2, hp2⟩ := lexAux_ws s hws (f - s.length) ⟨pos.line, pos.col +
      ((c :: (cs ++ (s ++ render ps))).length - (s ++ render ps).length)⟩ (render ps)
    rw [show f - s.length + s.length = f by simp at hf; omega] at hp2
    obtain ⟨pts, hpts, hmap⟩ := ih hgt (f - s.length) pos2 (by simp at hf; omega)
    refine ⟨⟨t, pos⟩ :: pts, ?_, by simp [hmap]⟩
    have hcn' : (c == '\n') = false := by simpa using hcn
    have hch' : (c == '#') = false := by simpa using hch
    simp only [List.cons_append, lexAux, hcn', hcw, hch', Bool.false_eq_true, if_false]
    simp only [List.cons_append] at htok hlen
    rw [htok]
    simp only [hlen, if_true, hp2, hpts]
    rfl

/-- **`lexChars_render`** — `lexChars` of a good rendering returns its tokens and then `eof`. -/
theorem lexChars_render (ps : List (Tok × List Char)) (hg : Good ps) :
    ∃ pts, lexChars (render ps) = .ok pts ∧ pts.map PTok.tok = ps.map Prod.fst ++ [.eof] :=
  lexAux_render ps hg _ _ (Nat.lt_succ_self _)

/-! ## The printer's layout is good. -/

theorem layoutLine_fst (last : List Char) : ∀ ts, (layoutLine last ts).map Prod.fst = ts := by
  intro ts
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases ts with
    | nil => rfl
    | cons t' ts' => simp only [layoutLine, List.map_cons] at ih ⊢; rw [ih]

theorem sepWithin_ws (t t' : Tok) : (sepWithin t t').all isWs = true := by
  unfold sepWithin; split <;> rfl

theorem layoutLine_seps (last : List Char) (hl : last.all isWs = true) :
    ∀ ts, ∀ p ∈ layoutLine last ts, p.2.all isWs = true := by
  intro ts
  induction ts with
  | nil => intro p hp; simp [layoutLine] at hp
  | cons t ts ih =>
    cases ts with
    | nil => intro p hp; simp [layoutLine] at hp; rw [hp]; exact hl
    | cons t' ts' =>
      intro p hp
      simp only [layoutLine, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact sepWithin_ws t t'
      · exact ih p (by simpa [layoutLine] using hp)

theorem layoutLine_adj (last : List Char) : ∀ ts, Adj (layoutLine last ts) := by
  intro ts
  induction ts with
  | nil => trivial
  | cons t ts ih =>
    cases ts with
    | nil => trivial
    | cons t' ts' =>
      have hsep : sepWithin t t' = [] → t.delim (t'.text.headD ' ') = true := by
        unfold sepWithin; split
        · rename_i h; intro _; simp only [Bool.and_eq_true] at h; exact h.2
        · intro h; simp at h
      cases ts' with
      | nil => exact ⟨hsep, trivial⟩
      | cons t'' ts'' => exact ⟨hsep, ih⟩

theorem layoutLine_last (last : List Char) :
    ∀ ts, ∀ q, (layoutLine last ts).getLast? = some q → q.2 = last := by
  intro ts
  induction ts with
  | nil => intro q hq; simp [layoutLine] at hq
  | cons t ts ih =>
    cases ts with
    | nil => intro q hq; simp [layoutLine] at hq; rw [← hq]
    | cons t' ts' =>
      intro q hq
      apply ih q
      simp only [layoutLine] at hq
      obtain ⟨y, ys, hy⟩ : ∃ y ys, layoutLine last (t' :: ts') = y :: ys := by
        cases ts' with
        | nil => exact ⟨_, _, rfl⟩
        | cons _ _ => exact ⟨_, _, rfl⟩
      rw [hy, List.getLast?_cons_cons] at hq
      rw [hy]; exact hq

theorem adj_append : ∀ (xs ys : List (Tok × List Char)), Adj xs → Adj ys →
    (∀ q, xs.getLast? = some q → q.2 ≠ []) → Adj (xs ++ ys) := by
  intro xs
  induction xs with
  | nil => intro ys _ hy _; exact hy
  | cons x xs ih =>
    intro ys hx hy hl
    cases xs with
    | nil =>
      cases ys with
      | nil => trivial
      | cons y ys' =>
        obtain ⟨t, s⟩ := x; obtain ⟨t', s'⟩ := y
        exact ⟨fun h => absurd h (hl (t, s) rfl), hy⟩
    | cons x' xs' =>
      obtain ⟨t, s⟩ := x; obtain ⟨t', s'⟩ := x'
      refine ⟨hx.1, ?_⟩
      have := ih ys hx.2 hy (fun q hq => hl q (by rw [List.getLast?_cons_cons]; exact hq))
      simpa using this

theorem spaces_ws (n : Nat) : (spaces n).all isWs = true := by
  unfold spaces
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.all_cons, ih]; rfl

theorem layoutLines_good : ∀ (ls : List (Nat × List Tok)),
    (layoutLines ls).map Prod.fst = ls.flatMap Prod.snd ∧
    (∀ p ∈ layoutLines ls, p.2.all isWs = true) ∧ Adj (layoutLines ls) := by
  intro ls
  induction ls with
  | nil => exact ⟨rfl, by simp [layoutLines], trivial⟩
  | cons l ls ih =>
    obtain ⟨i, ts⟩ := l
    cases ls with
    | nil =>
      refine ⟨by simp [layoutLines, layoutLine_fst], ?_, layoutLine_adj _ ts⟩
      exact layoutLine_seps _ rfl ts
    | cons l' ls' =>
      obtain ⟨i', ts'⟩ := l'
      obtain ⟨ih1, ih2, ih3⟩ := ih
      have hl : ('\n' :: spaces i').all isWs = true := by
        simp only [List.all_cons, Bool.and_eq_true]; exact ⟨rfl, spaces_ws i'⟩
      refine ⟨?_, ?_, ?_⟩
      · simp only [layoutLines, List.map_append, layoutLine_fst] at ih1 ⊢
        rw [ih1]; simp
      · intro p hp
        simp only [layoutLines, List.mem_append] at hp
        rcases hp with hp | hp
        · exact layoutLine_seps _ hl ts p hp
        · exact ih2 p (by simpa [layoutLines] using hp)
      · simp only [layoutLines]
        refine adj_append _ _ (layoutLine_adj _ ts) (by simpa [layoutLines] using ih3) ?_
        intro q hq; rw [layoutLine_last _ ts q hq]; simp

/-! ## Every printed token is well formed. -/

theorem sepBy_all {α : Type} (P : Tok → Bool) (s : Tok) (f : α → List Tok) (hs : P s = true) :
    ∀ xs, (∀ x ∈ xs, (f x).all P = true) → (sepBy s f xs).all P = true := by
  intro xs
  induction xs with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro h
    cases xs with
    | nil => simpa [sepBy] using h x List.mem_cons_self
    | cons y ys =>
      rw [sepBy_cons_cons]
      simp only [List.all_append, List.all_cons, Bool.and_eq_true]
      exact ⟨h x List.mem_cons_self, hs, ih (fun z hz => h z (List.mem_cons_of_mem _ hz))⟩

theorem re_toks_all : ∀ r : Re, r.wf = true → r.toks.all TokWF = true := by
  intro r
  induction r with
  | lit bs => intro h; simpa [Re.toks, TokWF, Re.wf] using h
  | set n rs => intro h; simpa [Re.toks, TokWF, Re.wf] using h
  | esc e => intro _; rfl
  | any => intro _; rfl
  | alt l r ihl ihr | inter l r ihl ihr | cat l r ihl ihr =>
    intro h
    simp only [Re.wf, Bool.and_eq_true] at h
    have := ihl h.1; have := ihr h.2
    simp only [Re.toks, wrap]
    split <;> split <;> simp_all [TokWF]
  | neg r ih | star r ih | plus r ih | opt r ih | rep r _ _ ih =>
    intro h
    simp only [Re.wf] at h
    have := ih h
    simp only [Re.toks, wrap]
    split <;> simp_all [TokWF]

theorem atom_toks_all (a : Atom) (h : a.wf = true) : a.toks.all TokWF = true := by
  simp only [Atom.wf, Bool.and_eq_true, List.all_eq_true] at h
  have hs : (commaSep (fun x => [Arg.tok x]) a.args).all TokWF = true := by
    refine sepBy_all TokWF _ _ rfl _ (fun x hx => ?_)
    have := h.2 x hx
    cases x with
    | var v => simp only [Arg.wf, isVar, Bool.and_eq_true] at this; simp [Arg.tok, TokWF, this.1]
    | int z => rfl
  simp [Atom.toks, TokWF, h.1, hs]

theorem lit_toks_all (l : Lit) (h : l.atom.wf = true) : l.toks.all TokWF = true := by
  have := atom_toks_all _ h
  obtain ⟨ng, a⟩ := l
  cases ng <;> simp_all [Lit.toks, TokWF]

theorem rule_toks_all (r : Rule) (h : r.wf = true) : r.toks.all TokWF = true := by
  simp only [Rule.wf, Bool.and_eq_true, List.all_eq_true] at h
  have ha := atom_toks_all _ h.1
  have hk : isIdent "rule" = true := rfl
  have hb : (commaSep Lit.toks r.body).all TokWF = true :=
    sepBy_all TokWF _ _ rfl _ (fun l hl => lit_toks_all l (h.2 l hl))
  simp only [Rule.toks, List.all_cons, List.all_append, TokWF, hk, ha, Bool.true_and]
  split <;> simp_all [TokWF]

theorem prod_toks_all (p : Prod) (h : p.wf = true) : p.toks.all TokWF = true := by
  simp only [Prod.wf, Bool.and_eq_true, List.all_eq_true] at h
  have hb : (barSep p.alts).all TokWF = true := by
    refine sepBy_all TokWF _ _ rfl _ (fun a ha => ?_)
    have := h.2 a ha
    cases a with
    | nil => rfl
    | cons x xs =>
      show ((x :: xs).map GSym.tok).all TokWF = true
      simp only [List.all_map, List.all_eq_true, Function.comp_apply] at this ⊢
      intro g hg
      have := this g hg
      cases g <;> simpa [GSym.tok, TokWF, GSym.wf] using this
  simp [Prod.toks, TokWF, h.1, hb]

theorem agg_toks_all (a : Agg) (h : a.wf = true) : a.toks.all TokWF = true := by
  have k1 : isIdent "sum" = true := rfl
  have k2 : isIdent "count" = true := rfl
  cases a <;> simp_all [Agg.toks, TokWF, Agg.wf]

theorem claim_toks_all (c : Claim) (h : c.wf = true) : c.toks.all TokWF = true := by
  have k1 : isIdent "forbid" = true := rfl
  have k2 : isIdent "require" = true := rfl
  have k3 : isIdent "pattern" = true := rfl
  have k4 : isIdent "rule" = true := rfl
  have k5 : isIdent "budget" = true := rfl
  have k6 : isIdent "in" = true := rfl
  cases c <;> simp_all [Claim.toks, TokWF, Claim.wf]

theorem decl_toks_all (d : Decl) (h : d.wf = true) : d.toks.all TokWF = true := by
  cases d with
  | pattern n r =>
    simp only [Decl.wf, Bool.and_eq_true] at h
    have hk : isIdent "pattern" = true := rfl
    have hr : (r.toksAt 0).all TokWF = true := by
      have := re_toks_all r h.2
      simp only [Re.toksAt, wrap]; split <;> simp_all [TokWF]
    simp [Decl.toks, TokWF, hk, h.1, hr]
  | grammar n ps =>
    simp only [Decl.wf, Bool.and_eq_true, List.all_eq_true] at h
    have hk : isIdent "grammar" = true := rfl
    have hp : (ps.flatMap Prod.toks).all TokWF = true := by
      rw [List.all_flatMap, List.all_eq_true]
      exact fun p hp => prod_toks_all p (h.2 p hp)
    simp [Decl.toks, TokWF, hk, h.1, hp]
  | rule r =>
    exact rule_toks_all r (by simpa [Decl.wf] using h)
  | budget n a b =>
    simp only [Decl.wf, Bool.and_eq_true] at h
    have hk : isIdent "budget" = true := rfl
    have ha := agg_toks_all a h.2
    simp [Decl.toks, TokWF, hk, h.1, ha]
  | policy n cs =>
    simp only [Decl.wf, Bool.and_eq_true, List.all_eq_true] at h
    have hk : isIdent "policy" = true := rfl
    have hp : (cs.flatMap Claim.toks).all TokWF = true := by
      rw [List.all_flatMap, List.all_eq_true]
      exact fun c hc => claim_toks_all c (h.2 c hc)
    simp [Decl.toks, TokWF, hk, h.1, hp]

theorem decl_lines_flat (d : Decl) : d.lines.flatMap Prod.snd = d.toks := by
  cases d <;> simp [Decl.lines, Decl.toks, List.flatMap_map]

/-- ⚑ **The printer's layout is `Good`, and its tokens are the printed tokens.** -/
theorem layout_good (p : Policy) (hwf : p.wf = true) :
    Good p.layout ∧ p.layout.map Prod.fst = p.toks := by
  obtain ⟨h1, h2, h3⟩ := layoutLines_good p.lines
  have hfst : p.layout.map Prod.fst = p.toks := by
    rw [Policy.layout, h1, Policy.lines, List.flatMap_assoc]
    simp only [Policy.toks]
    congr 1; funext d; exact decl_lines_flat d
  refine ⟨⟨fun q hq => ⟨?_, h2 q hq⟩, h3⟩, hfst⟩
  have hmem : q.1 ∈ p.toks := by rw [← hfst]; exact List.mem_map_of_mem hq
  simp only [Policy.toks, List.mem_flatMap] at hmem
  obtain ⟨d, hd, ht⟩ := hmem
  simp only [Policy.wf, List.all_eq_true] at hwf
  have := decl_toks_all d (hwf d hd)
  rw [List.all_eq_true] at this
  exact this _ ht

end Dregg2.Policy
