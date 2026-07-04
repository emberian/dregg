/-
Arena — the parser's *soundness* theory: the meaning-preservation successor to
`parse_wf`.

`parse_wf` (Arena/ParseTheorems.lean) is a SAFETY result: every view range a
`complete` outcome registers is in-bounds of its arena, so `resolve` is total
and returns exactly `len` bytes. But bounds/totality say nothing about *which*
bytes. A degenerate parser that returned empty-but-in-bounds spans (every field
`⟨0,0⟩`) would satisfy `parse_wf` while resolving every field to the empty
string — total nonsense that still "type-checks" as well-formed.

This file states and proves the CORRECTNESS successor. For a `complete` parse:

* the two SP separators of the request line sit at *exactly* the byte offsets
  the parser reports — `input[i₁] = SP` and `input[i₁+1+i₂] = SP` — and there is
  no earlier SP in either the method or the target (so `i₁` is genuinely the
  first SP and `i₁+1+i₂` the second, per the RFC 9112 request-line grammar
  `method SP request-target SP HTTP-version`);
* each resolved field EQUALS its exact input substring:
  `resolve method  = input[0, i₁)`,
  `resolve target  = input[i₁+1, i₁+1+i₂)`,
  `resolve version = input[i₁+1+i₂+1, L)`  (L = the request-line length);
* **serialize-of-parse = input prefix**: concatenating the resolved fields back
  with their SP separators reproduces the consumed request line exactly —
  `method ++ " " ++ target ++ " " ++ version = input.take L`.

The degenerate empty-span parser FAILS this: it would need `input[0] = SP`
(method boundary at offset 0), false for any real request line like
`GET / HTTP/1.1`.

Scope: this proves the request-line field-extraction soundness — the real
soundness core. The header-block round-trip (each header name/value = its exact
input substring, and re-serialising the header block = the input head) is NOT
closed here; it is named UNCLOSED in ARENA-SOUND-README.md. What IS proven for
headers upstream is only the SAFETY result (`parse_wf`: their spans are
in-bounds), not this MEANING result.
-/
import Arena.ParseTheorems

namespace Arena
namespace Parse

/-! ## `resolve` of a freshly minted main-arena entry is its exact input slice -/

/-- `resolve` of an `mkEntry` addressing the main arena returns exactly the
main-arena slice `[off, off+len)`. This is the bridge from the abstract
`resolve` to a concrete `Array.extract`: for a main-arena entry whose
coordinates do not overflow the discriminant and whose range is in-bounds,
`resolve` is definitionally that slice. -/
theorem resolve_mkEntry_main {s : Store} {tag : NameTag} {off len : Nat}
    (hoff : off < sidecarBaseNat) (hlen : len < sidecarBaseNat)
    (hb : off + len ≤ s.main.size) :
    s.resolve (mkEntry tag off len) = some (s.main.extract off (off + len)) := by
  have hsize : UInt32.size = 4294967296 := rfl
  have hbase : sidecarBaseNat = 2147483648 := rfl
  have hoff' : (UInt32.ofNat off).toNat = off := UInt32.toNat_ofNat_of_lt (by omega)
  have hlen' : (UInt32.ofNat len).toNat = len := UInt32.toNat_ofNat_of_lt (by omega)
  have hside : (mkEntry tag off len).inSidecar = false := by
    simp only [mkEntry, Entry.inSidecar, decide_eq_false_iff_not]
    unfold isSidecarAddr
    rw [hoff']
    omega
  have hphys : (mkEntry tag off len).physOff = off := by
    unfold Entry.physOff
    rw [hside]
    simp only [mkEntry, Bool.false_eq_true, if_false]
    exact hoff'
  have hlent : (mkEntry tag off len).len.toNat = len := by
    simp only [mkEntry]
    exact hlen'
  have harena : s.arenaOf (mkEntry tag off len) = s.main := Store.arenaOf_main s hside
  simp only [Store.resolve, harena, hphys, hlent]
  rw [if_pos hb]

/-- `resolve` of a main-arena `mkEntry`, expressed directly as the concrete
input substring `(L'.drop off).take len` (where `s.main = L'.toArray`). This is
`resolve_mkEntry_main` composed with the `Array.extract`/`List` bridge, so the
soundness proof can speak entirely in `List.take`/`List.drop`. -/
theorem resolve_mkEntry_main_toList {s : Store} {tag : NameTag} {off len : Nat}
    {L' : List UInt8} (hmain : s.main = L'.toArray)
    (hoff : off < sidecarBaseNat) (hlen : len < sidecarBaseNat)
    (hb : off + len ≤ L'.length) :
    s.resolve (mkEntry tag off len) = some (((L'.drop off).take len).toArray) := by
  have hbsize : off + len ≤ s.main.size := by rw [hmain]; simpa using hb
  rw [resolve_mkEntry_main hoff hlen hbsize, hmain]
  rw [List.extract_toArray, List.extract_eq_drop_take, Nat.add_sub_cancel_left]

/-! ## The head of `segments` starts at `start` -/

/-- The first span `segments` cuts begins at the base offset `start`. In the
parser `start = 0`, so the request-line span begins at input offset `0`. -/
theorem segments_head_off {start hi : Nat} {ps : List Nat} {sp : Span}
    {rest : List Span} (h : segments start hi ps = sp :: rest) : sp.off = start := by
  cases ps with
  | nil =>
    unfold segments at h
    injection h with h1 _
    rw [← h1]
  | cons p ps =>
    unfold segments at h
    injection h with h1 _
    rw [← h1]

/-! ## Request-line field extraction: the spans denote exact grammar fields -/

/-- **`parseRequestLine` is sound.** When it accepts, there are offsets `i₁`
(first SP) and `i₂` (second SP, relative to just past the first) such that the
three spans denote exactly the grammar fields of `line`, the two SP separators
sit exactly at `i₁` and `i₁+1+i₂`, and there is no earlier SP inside the method
or the target. This is the meaning content: the spans are not merely in-bounds
(that is `parseRequestLine_end_le`), they are the *right* substrings. -/
theorem parseRequestLine_sound {off : Nat} {line : Bytes} {rl : ReqLineSpans}
    (h : parseRequestLine off line = some rl) :
    ∃ i₁ i₂,
      rl.method = ⟨off, i₁⟩ ∧
      rl.target = ⟨off + i₁ + 1, i₂⟩ ∧
      rl.version = ⟨off + i₁ + 1 + i₂ + 1, line.length - (i₁ + 1 + i₂ + 1)⟩ ∧
      i₁ < line.length ∧
      i₁ + 1 + i₂ < line.length ∧
      line[i₁]? = some SP ∧
      line[i₁ + 1 + i₂]? = some SP ∧
      (∀ j, j < i₁ → line[j]? ≠ some SP) ∧
      (∀ j, i₁ < j → j < i₁ + 1 + i₂ → line[j]? ≠ some SP) := by
  unfold parseRequestLine at h
  obtain ⟨i₁, h₁, h⟩ := Option.bind_eq_some.mp h
  obtain ⟨i₂, h₂, h⟩ := Option.bind_eq_some.mp h
  simp only [] at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · simp at h
  injection h with h
  subst h
  -- unfold the two byte searches into `findIdx?` form
  simp only [findByteIdx] at h₁ h₂
  obtain ⟨hlt1, hp1, hbefore1⟩ := List.findIdx?_eq_some_iff_getElem.mp h₁
  obtain ⟨hlt2, hp2, hbefore2⟩ := List.findIdx?_eq_some_iff_getElem.mp h₂
  -- lengths of the two suffixes (keep `hlt2` in drop-length form for getElem?)
  have hlt2' : i₂ < line.length - (i₁ + 1) := by
    have := hlt2; rw [List.length_drop] at this; exact this
  -- the second SP, mapped from `line.drop (i₁+1)` back to `line`
  have hidx2 : i₁ + 1 + i₂ < line.length := by omega
  refine ⟨i₁, i₂, ?_, ?_, ?_, hlt1, hidx2, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · -- version length = rest₂.length = line.length - (i₁+1+i₂+1)
    have hvl : (List.drop (i₂ + 1) (List.drop (i₁ + 1) line)).length
        = line.length - (i₁ + 1 + i₂ + 1) := by
      rw [List.drop_drop, List.length_drop]
      omega
    simp only [Span.mk.injEq, true_and]
    exact hvl
  · -- line[i₁]? = some SP
    rw [List.getElem?_eq_getElem hlt1, eq_of_beq hp1]
  · -- line[i₁+1+i₂]? = some SP
    have he : line[i₁ + 1 + i₂]? = (List.drop (i₁ + 1) line)[i₂]? := by
      rw [List.getElem?_drop]
    rw [he, List.getElem?_eq_getElem hlt2, eq_of_beq hp2]
  · -- no SP strictly before i₁ inside the method
    intro j hj hcontra
    obtain ⟨hjlt, hje⟩ := List.getElem?_eq_some_iff.mp hcontra
    exact hbefore1 j hj (by simp [hje])
  · -- no SP strictly between the separators inside the target
    intro j hjgt hjlt hcontra
    have hklt : j - (i₁ + 1) < i₂ := by omega
    -- map the input index into the target suffix `line.drop (i₁+1)`
    have hmap : (List.drop (i₁ + 1) line)[j - (i₁ + 1)]? = some SP := by
      rw [List.getElem?_drop]
      have hj' : (i₁ + 1) + (j - (i₁ + 1)) = j := by omega
      rw [hj']; exact hcontra
    obtain ⟨hh, hval⟩ := List.getElem?_eq_some_iff.mp hmap
    exact hbefore2 (j - (i₁ + 1)) hklt (by simp [hval])

/-! ## The request-line serialisation lemma -/

/-- Splitting a list at two separator positions and re-joining with the
separators reproduces the list: this is the pure list core of the
"serialize-of-parse = input prefix" round-trip, instantiated at the two SP
separators of the request line. -/
theorem reconstruct_two_sep {l : Bytes} {a b : Nat}
    (h1 : l[a]? = some SP) (h2 : l[a + 1 + b]? = some SP) :
    l.take a ++ SP :: ((l.drop (a + 1)).take b ++ SP :: l.drop (a + 1 + b + 1)) = l := by
  obtain ⟨ha, hla⟩ := List.getElem?_eq_some_iff.mp h1
  obtain ⟨hab, hlab⟩ := List.getElem?_eq_some_iff.mp h2
  refine Eq.symm ?_
  calc l = l.take a ++ l.drop a := (List.take_append_drop a l).symm
    _ = l.take a ++ (SP :: l.drop (a + 1)) := by
          rw [List.drop_eq_getElem_cons ha, hla]
    _ = l.take a ++ SP :: ((l.drop (a + 1)).take b ++ (l.drop (a + 1)).drop b) := by
          rw [List.take_append_drop]
    _ = l.take a ++ SP :: ((l.drop (a + 1)).take b ++ l.drop (a + 1 + b)) := by
          rw [List.drop_drop]
    _ = l.take a ++ SP :: ((l.drop (a + 1)).take b ++ (SP :: l.drop (a + 1 + b + 1))) := by
          rw [List.drop_eq_getElem_cons hab, hlab]

/-! ## The soundness theorem for a complete parse -/

/-- **The parser's request-line extraction is sound.** For a `complete`
outcome, there exist SP-separator offsets `i₁`, `i₂` and a request-line length
`L` such that:

* the two separators sit exactly where the parser reports (`input[i₁] = SP`,
  `input[i₁+1+i₂] = SP`) and there is no earlier SP inside the method or the
  target — so `i₁` really is the first SP and `i₁+1+i₂` the second;
* each resolved field equals its exact input substring — method = `input[0,i₁)`,
  target = `input[i₁+1, i₁+1+i₂)`, version = `input[i₁+1+i₂+1, L)`;
* re-serialising the resolved fields with their SP separators reconstructs the
  request line `input.take L` (serialize-of-parse = input prefix).

This is the MEANING successor to `parse_wf`: a degenerate parser returning
empty-but-in-bounds spans satisfies `parse_wf` but fails this — it would need
`input[0] = SP`, false for any real request line. -/
theorem parse_reqline_sound {input : Bytes} {maxHeaders : Nat} {req : Request}
    (h : parse input maxHeaders = .complete req) :
    ∃ (i₁ i₂ L : Nat),
      -- separator offsets and the request-line length, all inside the input
      i₁ < L ∧ i₁ + 1 + i₂ < L ∧ L ≤ input.length ∧
      -- the two SP separators sit exactly here
      input[i₁]? = some SP ∧
      input[i₁ + 1 + i₂]? = some SP ∧
      -- and nowhere earlier inside the method or the target
      (∀ j, j < i₁ → input[j]? ≠ some SP) ∧
      (∀ j, i₁ < j → j < i₁ + 1 + i₂ → input[j]? ≠ some SP) ∧
      -- each resolved field = its exact input substring
      (∃ mb, req.store.resolve req.method = some mb ∧ mb.toList = input.take i₁) ∧
      (∃ tb, req.store.resolve req.target = some tb ∧
          tb.toList = (input.drop (i₁ + 1)).take i₂) ∧
      (∃ vb, req.store.resolve req.version = some vb ∧
          vb.toList = (input.drop (i₁ + 1 + i₂ + 1)).take (L - (i₁ + 1 + i₂ + 1))) ∧
      -- serialize-of-parse = input prefix: the resolved fields rebuild the line
      (∀ mb tb vb, req.store.resolve req.method = some mb →
          req.store.resolve req.target = some tb →
          req.store.resolve req.version = some vb →
          mb.toList ++ SP :: (tb.toList ++ SP :: vb.toList) = input.take L) := by
  -- Unfold `parse` following the same split skeleton as `parse_complete_spec`.
  unfold parse at h
  split at h
  · simp at h
  next hin =>
  split at h
  · simp at h
  next headEnd hfd =>
  have hhead : headEnd + 4 ≤ input.length := findDoubleCrlf_add_four_le hfd
  have hinlen : input.length < sidecarBaseNat := by
    unfold isMainAddr at *; omega
  simp only [] at h
  split at h
  · simp at h
  next reqSpan headerSpans hseg =>
  split at h
  · simp at h
  next rl hrl =>
  split at h
  · simp at h
  next sidecar headers hph =>
  split at h
  · simp at h
  next hcount =>
  split at h
  · simp at h
  injection h with h
  -- Keep `req`; read its field shapes off `h : {…} = req`.
  have hSM : req.store.main = input.toArray := (congrArg (fun r => r.store.main) h).symm
  have hME : req.method = mkEntry .method rl.method.off rl.method.len :=
    (congrArg (fun r => r.method) h).symm
  have hTE : req.target = mkEntry .target rl.target.off rl.target.len :=
    (congrArg (fun r => r.target) h).symm
  have hVE : req.version = mkEntry .version rl.version.off rl.version.len :=
    (congrArg (fun r => r.version) h).symm
  -- Request-line span starts at offset 0.
  have hoff0 : reqSpan.off = 0 := segments_head_off hseg
  -- Span-end bounds (mirrors `parse_complete_spec`), to place `reqSpan` in input.
  have hlenHead : (input.take headEnd).length = headEnd := by
    rw [List.length_take]; omega
  have hpos : ∀ p ∈ crlfPositions (input.take headEnd), p < headEnd := by
    intro p hp; have := crlfPositions_lt hp; omega
  have hends : ∀ sp ∈ reqSpan :: headerSpans, sp.off + sp.len ≤ headEnd + 1 := by
    rw [← hseg]; exact segments_end_le hpos (by omega)
  have hreqEnd : reqSpan.off + reqSpan.len ≤ input.length := by
    have := hends reqSpan (by simp); omega
  have hLle : reqSpan.len ≤ input.length := by rw [hoff0] at hreqEnd; omega
  -- The request-line slice is the input prefix `input.take reqSpan.len`.
  have hslice : sliceSpan input reqSpan = input.take reqSpan.len := by
    unfold sliceSpan; rw [hoff0]; simp
  rw [hoff0, hslice] at hrl
  -- Length of the line.
  have hlineLen : (input.take reqSpan.len).length = reqSpan.len := by
    rw [List.length_take]; omega
  -- Field-extraction soundness of the request line.
  obtain ⟨i₁, i₂, hmeth, htgt, hver, hi1, hi12, hsp1, hsp2, hnb1, hnb2⟩ :=
    parseRequestLine_sound hrl
  rw [hlineLen] at hi1 hi12
  -- Name the request-line length `L` (core `generalize`, not Mathlib `set`).
  generalize hLdef : reqSpan.len = L at hi1 hi12 hLle hlineLen hver hsp1 hsp2 hnb1 hnb2
  -- Normalise the `0 + …` offsets and pin the version length to `L`.
  simp only [Nat.zero_add] at htgt hver
  rw [hlineLen] at hver
  -- Each field entry resolves to exactly its input substring.
  -- method: input[0, i₁) = input.take i₁
  have hMethodRes : req.store.resolve req.method
      = some (((input.drop 0).take i₁).toArray) := by
    rw [hME]; simp only [hmeth]
    exact resolve_mkEntry_main_toList hSM (by omega) (by omega) (by omega)
  -- target: input[i₁+1, i₁+1+i₂) = (input.drop (i₁+1)).take i₂
  have hTargetRes : req.store.resolve req.target
      = some (((input.drop (i₁ + 1)).take i₂).toArray) := by
    rw [hTE]; simp only [htgt]
    exact resolve_mkEntry_main_toList hSM (by omega) (by omega) (by omega)
  -- version: input[i₁+1+i₂+1, L) = (input.drop (i₁+1+i₂+1)).take (L - (i₁+1+i₂+1))
  have hVersionRes : req.store.resolve req.version
      = some (((input.drop (i₁ + 1 + i₂ + 1)).take (L - (i₁ + 1 + i₂ + 1))).toArray) := by
    rw [hVE]; simp only [hver]
    exact resolve_mkEntry_main_toList hSM (by omega) (by omega) (by omega)
  -- The list contents of each resolved field.
  have hMethodList : (((input.drop 0).take i₁).toArray).toList = input.take i₁ := by simp
  have hTargetList : (((input.drop (i₁ + 1)).take i₂).toArray).toList
      = (input.drop (i₁ + 1)).take i₂ := by simp
  have hVersionList : (((input.drop (i₁ + 1 + i₂ + 1)).take (L - (i₁ + 1 + i₂ + 1))).toArray).toList
      = (input.drop (i₁ + 1 + i₂ + 1)).take (L - (i₁ + 1 + i₂ + 1)) := by simp
  -- Lift the SP facts from `input.take L` back to `input`.
  have hspI1 : input[i₁]? = some SP := by
    rw [← List.getElem?_take_of_lt (show i₁ < L by omega)]; exact hsp1
  have hspI2 : input[i₁ + 1 + i₂]? = some SP := by
    rw [← List.getElem?_take_of_lt (show i₁ + 1 + i₂ < L by omega)]; exact hsp2
  have hnbI1 : ∀ j, j < i₁ → input[j]? ≠ some SP := by
    intro j hj
    rw [← List.getElem?_take_of_lt (show j < L by omega)]; exact hnb1 j hj
  have hnbI2 : ∀ j, i₁ < j → j < i₁ + 1 + i₂ → input[j]? ≠ some SP := by
    intro j hgt hlt
    rw [← List.getElem?_take_of_lt (show j < L by omega)]; exact hnb2 j hgt hlt
  -- Assemble.
  refine ⟨i₁, i₂, L, by omega, by omega, hLle, hspI1, hspI2, hnbI1, hnbI2,
    ⟨_, hMethodRes, hMethodList⟩, ⟨_, hTargetRes, hTargetList⟩,
    ⟨_, hVersionRes, hVersionList⟩, ?_⟩
  -- serialize-of-parse = input prefix
  intro mb tb vb hmb htb hvb
  -- pin the resolved bytes to the computed slices
  rw [hMethodRes] at hmb; rw [hTargetRes] at htb; rw [hVersionRes] at hvb
  injection hmb with hmb; injection htb with htb; injection hvb with hvb
  subst hmb; subst htb; subst hvb
  rw [hMethodList, hTargetList, hVersionList]
  clear hMethodList hTargetList hVersionList
  -- reconstruct over the line `input.take L`, then relate its pieces to input
  have hrec := reconstruct_two_sep (l := input.take L) (a := i₁) (b := i₂)
    (by rw [List.getElem?_take_of_lt (show i₁ < L by omega)]; exact hspI1)
    (by rw [List.getElem?_take_of_lt (show i₁ + 1 + i₂ < L by omega)]; exact hspI2)
  -- the three pieces of `input.take L` equal the input substrings
  have pm : (input.take L).take i₁ = input.take i₁ := by
    rw [List.take_take]; congr 1; omega
  have pt : ((input.take L).drop (i₁ + 1)).take i₂ = (input.drop (i₁ + 1)).take i₂ := by
    rw [List.drop_take, List.take_take]
    congr 1
    omega
  have pv : (input.take L).drop (i₁ + 1 + i₂ + 1)
      = (input.drop (i₁ + 1 + i₂ + 1)).take (L - (i₁ + 1 + i₂ + 1)) := by
    rw [List.drop_take]
  rw [pm, pt, pv] at hrec
  exact hrec

end Parse
end Arena
