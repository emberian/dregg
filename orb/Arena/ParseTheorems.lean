/-
Arena — the parser's static well-formedness theory.

Headline results:

* `parse_wf` — every `complete` outcome of the head parser carries a
  well-formed store (`Store.Wf`): every registered view range, including the
  sidecar entries the canonicalization path synthesizes, is in-bounds of the
  arena it addresses. This made the parser's old runtime `wfCheck` gate (and
  its `internal-wf-violation` error class) provably dead; both are gone from
  `parse`.
* `parse_sidecar_fits` — the synthesized-range bounds discipline stated on
  its own: in a complete store every sidecar entry ends inside the sidecar
  arena.
* `parse_consumed_le` — consumed-bytes monotonicity: a complete outcome never
  claims more bytes than the input holds.
* `parse_headers_bounded` — the header-count bound is enforced: a complete
  outcome carries at most `maxHeaders` headers (the count reject path is
  reachable only on a head that overflows the bound).

Proof shape (all elementary, `omega`-driven):

1. `findDoubleCrlf` finding `headEnd` means the input holds `headEnd + 4`
   bytes; `crlfPositions` are strictly sorted positions below the head end.
2. `segments` therefore cuts spans whose ends stay `≤ headEnd + 1` and whose
   *total length* stays `≤ headEnd + 1` — the second bound is what caps the
   sidecar: canonicalization appends at most one name-slice per header span,
   so sidecar offsets never overflow the packed 32-bit representation.
3. `parseRequestLine` / `parseHeaderLine` only cut inside the line they are
   given, so every produced span ends inside the input.
4. Every entry `parse` registers is then in-bounds of its arena
   (`EntryFits`, closed under sidecar growth), and the two theorem groups
   above assemble into `Store.Wf` of the final store.
-/
import Arena.Basic
import Arena.Theorems
import Arena.Parse

namespace Arena
namespace Parse

/-! ## Entry bounds against arena *sizes* -/

/-- An entry fits arenas of the given sizes: its physical range ends inside
the arena its discriminant selects. This is `Store.InBounds` stated against
sizes alone (see `Store.inBounds_of_entryFits`). -/
def EntryFits (mainLen sideLen : Nat) (e : Entry) : Prop :=
  e.physOff + e.len.toNat ≤ if e.inSidecar then sideLen else mainLen

theorem EntryFits.mono {mainLen sideLen sideLen' : Nat} {e : Entry}
    (h : EntryFits mainLen sideLen e) (hs : sideLen ≤ sideLen') :
    EntryFits mainLen sideLen' e := by
  unfold EntryFits at *
  by_cases hside : e.inSidecar <;> simp [hside] at * <;> omega

theorem Store.inBounds_of_entryFits {s : Store} {e : Entry}
    (h : EntryFits s.main.size s.sidecar.size e) : s.InBounds e := by
  unfold EntryFits at h
  unfold Arena.Store.InBounds Arena.Store.arenaOf
  by_cases hside : e.inSidecar <;> simp [hside] at * <;> omega

/-- A main-arena entry: both coordinates below the discriminant, range inside
the main arena. -/
theorem mkEntry_fits_main {tag : NameTag} {off len M : Nat} (S : Nat)
    (hM : M < sidecarBaseNat) (hend : off + len ≤ M) :
    EntryFits M S (mkEntry tag off len) := by
  have hsize : UInt32.size = 4294967296 := rfl
  have hbase : sidecarBaseNat = 2147483648 := rfl
  have hoff : (UInt32.ofNat off).toNat = off :=
    UInt32.toNat_ofNat_of_lt (by omega)
  have hlen : (UInt32.ofNat len).toNat = len :=
    UInt32.toNat_ofNat_of_lt (by omega)
  have hside : (mkEntry tag off len).inSidecar = false := by
    simp only [mkEntry, Entry.inSidecar, decide_eq_false_iff_not]
    unfold isSidecarAddr
    omega
  unfold EntryFits Entry.physOff
  rw [hside]
  simp only [mkEntry]
  simp [hoff, hlen]
  omega

/-- A sidecar entry minted at physical offset `physOff`: the packed offset
does not overflow, the discriminant reads sidecar, and the range ends inside
a sidecar of size `S`. -/
theorem mkEntry_fits_sidecar {tag : NameTag} {physOff len S : Nat} (M : Nat)
    (hphys : physOff < sidecarBaseNat) (hlen : len < sidecarBaseNat)
    (hend : physOff + len ≤ S) :
    EntryFits M S (mkEntry tag (sidecarBaseNat + physOff) len) := by
  have hsize : UInt32.size = 4294967296 := rfl
  have hbase : sidecarBaseNat = 2147483648 := rfl
  have hoff : (UInt32.ofNat (sidecarBaseNat + physOff)).toNat
      = sidecarBaseNat + physOff :=
    UInt32.toNat_ofNat_of_lt (by omega)
  have hlen' : (UInt32.ofNat len).toNat = len :=
    UInt32.toNat_ofNat_of_lt (by omega)
  have hside : (mkEntry tag (sidecarBaseNat + physOff) len).inSidecar = true := by
    simp only [mkEntry, Entry.inSidecar, decide_eq_true_eq]
    unfold isSidecarAddr
    omega
  unfold EntryFits Entry.physOff
  rw [hside]
  simp only [mkEntry]
  simp [hoff, hlen']
  omega

/-! ## Span accounting -/

/-- Total declared length of a span list. -/
def spanSum : List Span → Nat
  | [] => 0
  | sp :: rest => sp.len + spanSum rest

theorem sliceSpan_length (bs : Bytes) (s : Span) :
    (sliceSpan bs s).length = min s.len (bs.length - s.off) := by
  simp [sliceSpan]

/-! ## `findDoubleCrlf` finds a real `CRLFCRLF`: it fits inside the input -/

theorem findDoubleCrlf_add_four_le :
    ∀ {bs : Bytes} {n : Nat}, findDoubleCrlf bs = some n → n + 4 ≤ bs.length
  | _ :: _ :: _ :: _ :: _, n, h => by
    rw [findDoubleCrlf] at h
    split at h
    · cases h
      simp
    · obtain ⟨m, hm, rfl⟩ := Option.map_eq_some'.mp h
      have := findDoubleCrlf_add_four_le hm
      simp only [List.length_cons] at *
      omega
  | [], _, h => by simp [findDoubleCrlf] at h
  | [_], _, h => by simp [findDoubleCrlf] at h
  | [_, _], _, h => by simp [findDoubleCrlf] at h
  | [_, _, _], _, h => by simp [findDoubleCrlf] at h

/-! ## `crlfPositions`: strictly sorted positions inside the input -/

theorem crlfPositions_lt {bs : Bytes} {p : Nat} (h : p ∈ crlfPositions bs) :
    p < bs.length :=
  List.mem_range.mp (List.mem_filter.mp h).1

theorem crlfPositions_pairwise (bs : Bytes) :
    (crlfPositions bs).Pairwise (· < ·) :=
  (List.pairwise_lt_range bs.length).filter _

/-! ## `segments`: span ends and total length stay inside `[0, hi + 1]` -/

theorem segments_end_le :
    ∀ {ps : List Nat} {start hi : Nat}, (∀ p ∈ ps, p < hi) → start ≤ hi + 1 →
      ∀ sp ∈ segments start hi ps, sp.off + sp.len ≤ hi + 1
  | [], start, hi, _, hstart, sp, hsp => by
    unfold segments at hsp
    simp at hsp
    subst hsp
    show start + (hi - start) ≤ hi + 1
    omega
  | p :: ps, start, hi, hps, hstart, sp, hsp => by
    have hp : p < hi := hps p (by simp)
    unfold segments at hsp
    rcases List.mem_cons.mp hsp with h | h
    · subst h
      show start + (p - start) ≤ hi + 1
      omega
    · exact segments_end_le (ps := ps) (start := p + 2) (hi := hi)
        (fun q hq => hps q (List.mem_cons_of_mem p hq)) (by omega) sp h

theorem segments_spanSum_le :
    ∀ {ps : List Nat} {start hi : Nat}, ps.Pairwise (· < ·) →
      (∀ p ∈ ps, p < hi) → (∀ p ∈ ps, start ≤ p + 1) → start ≤ hi + 1 →
      spanSum (segments start hi ps) + start ≤ hi + 1
  | [], start, hi, _, _, _, hstart => by
    show hi - start + 0 + start ≤ hi + 1
    omega
  | p :: ps, start, hi, hpw, hlt, hge, hstart => by
    have hp : p < hi := hlt p (by simp)
    have hstartp : start ≤ p + 1 := hge p (by simp)
    have hpw' := List.pairwise_cons.mp hpw
    have ih := segments_spanSum_le (ps := ps) (start := p + 2) (hi := hi)
      hpw'.2 (fun q hq => hlt q (List.mem_cons_of_mem p hq))
      (fun q hq => by have := hpw'.1 q hq; omega) (by omega)
    show p - start + spanSum (segments (p + 2) hi ps) + start ≤ hi + 1
    omega

/-! ## The line parsers only cut inside the line they are given -/

theorem findByteIdx_lt {t : UInt8} {l : Bytes} {i : Nat}
    (h : findByteIdx t l = some i) : i < l.length := by
  unfold findByteIdx at h
  obtain ⟨hlt, -⟩ := List.findIdx?_eq_some_iff_getElem.mp h
  exact hlt

theorem parseRequestLine_end_le {off : Nat} {line : Bytes} {rl : ReqLineSpans}
    (h : parseRequestLine off line = some rl) :
    rl.method.off + rl.method.len ≤ off + line.length ∧
    rl.target.off + rl.target.len ≤ off + line.length ∧
    rl.version.off + rl.version.len ≤ off + line.length := by
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
  have hi₁ : i₁ < line.length := findByteIdx_lt h₁
  have hi₂ : i₂ < (line.drop (i₁ + 1)).length := findByteIdx_lt h₂
  rw [List.length_drop] at hi₂
  injection h with h
  subst h
  simp only [List.length_drop]
  refine ⟨by omega, by omega, by omega⟩

theorem parseHeaderLine_spec {off : Nat} {line : Bytes} {hs : RawHeaderSpans}
    (h : parseHeaderLine off line = some hs) :
    hs.name.off = off ∧ hs.name.len ≤ line.length ∧
    hs.name.off + hs.name.len ≤ off + line.length ∧
    hs.value.off + hs.value.len ≤ off + line.length := by
  unfold parseHeaderLine at h
  obtain ⟨ci, hci, h⟩ := Option.bind_eq_some.mp h
  split at h
  · simp at h
  simp only [] at h
  split at h
  · simp at h
  split at h
  · simp at h
  have hlt : ci < line.length := findByteIdx_lt hci
  have hlead : (List.takeWhile isOws (line.drop (ci + 1))).length
      ≤ (line.drop (ci + 1)).length :=
    (List.takeWhile_sublist _).length_le
  rw [List.length_drop] at hlead
  injection h with h
  subst h
  simp only [List.length_drop]
  exact ⟨trivial, by omega, by omega, by omega⟩

/-! ## Canonicalization: sidecar growth is bounded, entries fit -/

theorem canonNameEntry_length {input sidecar : Bytes} {sp : Span}
    {sidecar' : Bytes} {e : Entry}
    (hce : canonNameEntry input sidecar sp = (sidecar', e)) :
    sidecar.length ≤ sidecar'.length ∧
    sidecar'.length ≤ sidecar.length + sp.len := by
  unfold canonNameEntry at hce
  simp only [] at hce
  split at hce
  · injection hce with h₁ h₂
    subst h₁
    have := sliceSpan_length input sp
    simp only [List.length_append, List.length_map]
    omega
  · injection hce with h₁ h₂
    subst h₁
    omega

theorem canonNameEntry_fits {input sidecar : Bytes} {sp : Span}
    {sidecar' : Bytes} {e : Entry} {S : Nat}
    (hce : canonNameEntry input sidecar sp = (sidecar', e))
    (hin : input.length < sidecarBaseNat)
    (hsp : sp.off + sp.len ≤ input.length)
    (hside : sidecar.length < sidecarBaseNat)
    (hS : sidecar'.length ≤ S) :
    EntryFits input.length S e := by
  unfold canonNameEntry at hce
  simp only [] at hce
  split at hce
  · injection hce with h₁ h₂
    subst h₁; subst h₂
    have hraw : (sliceSpan input sp).length = sp.len := by
      rw [sliceSpan_length]; omega
    apply mkEntry_fits_sidecar
    · exact hside
    · omega
    · rw [List.length_append, List.length_map, hraw] at hS
      omega
  · injection hce with h₁ h₂
    subst h₁; subst h₂
    exact mkEntry_fits_main S hin hsp

/-! ## `parseHeaders`: every produced entry fits, sidecar growth is capped -/

theorem parseHeaders_spec {input : Bytes} :
    ∀ {spans : List Span} {sidecar sidecarF : Bytes}
      {headers : List ParsedHeader},
      input.length < sidecarBaseNat →
      (∀ sp ∈ spans, sp.off + sp.len ≤ input.length) →
      sidecar.length + spanSum spans < sidecarBaseNat →
      parseHeaders input spans sidecar = some (sidecarF, headers) →
      sidecar.length ≤ sidecarF.length ∧
      sidecarF.length ≤ sidecar.length + spanSum spans ∧
      ∀ ph ∈ headers,
        EntryFits input.length sidecarF.length ph.name ∧
        EntryFits input.length sidecarF.length ph.value
  | [], sidecar, sidecarF, headers, _, _, _, h => by
    unfold parseHeaders at h
    injection h with h
    injection h with h₁ h₂
    subst h₁; subst h₂
    refine ⟨Nat.le_refl _, ?_, by simp⟩
    show sidecar.length ≤ sidecar.length + 0
    omega
  | sp :: rest, sidecar, sidecarF, headers, hin, hsp, hcap, h => by
    have hsc : spanSum (sp :: rest) = sp.len + spanSum rest := rfl
    unfold parseHeaders at h
    split at h
    · simp at h
    obtain ⟨raw, hraw, h⟩ := Option.bind_eq_some.mp h
    -- destructure the canonicalization pair
    rcases hce : canonNameEntry input sidecar raw.name with ⟨sidecar', nameEntry⟩
    rw [hce] at h
    obtain ⟨⟨sidecarF', parsed⟩, hrec, h⟩ := Option.bind_eq_some.mp h
    injection h with h
    injection h with h₁ h₂
    subst h₁; subst h₂
    -- facts about the current span and header line
    have hspHere : sp.off + sp.len ≤ input.length := hsp sp (by simp)
    have hslice := sliceSpan_length input sp
    obtain ⟨hnOff, hnLen, hnEnd, hvEnd⟩ := parseHeaderLine_spec hraw
    have hnEnd' : raw.name.off + raw.name.len ≤ input.length := by omega
    have hvEnd' : raw.value.off + raw.value.len ≤ input.length := by omega
    have hnLen' : raw.name.len ≤ sp.len := by omega
    -- sidecar growth across the canonicalization
    have hgrow := canonNameEntry_length hce
    -- the inductive step
    have hcap' : sidecar'.length + spanSum rest < sidecarBaseNat := by omega
    obtain ⟨ihGrow, ihLen, ihFits⟩ :=
      parseHeaders_spec hin (fun q hq => hsp q (by simp [hq])) hcap' hrec
    refine ⟨by omega, by omega, ?_⟩
    intro ph hph
    rcases List.mem_cons.mp hph with hph | hph
    · subst hph
      exact ⟨canonNameEntry_fits hce hin hnEnd' (by omega) ihGrow,
             mkEntry_fits_main _ hin hvEnd'⟩
    · exact ihFits ph hph

/-! ## The parser's complete outcome: well-formed store, bounded consumed -/

/-- The one-pass invariant of a `complete` outcome: the store is well-formed,
the consumed count fits the input, and the header count respects the configured
bound. `parse_wf`, `parse_sidecar_fits`, `parse_consumed_le` and
`parse_headers_bounded` are its corollaries. The header bound is the honest
statement of the count-hardening: the `maxHeaders < headers.length` reject path
is reachable only on a head that overflows the bound, so every `complete`
outcome carries at most `maxHeaders` headers. -/
theorem parse_complete_spec {input : Bytes} {maxHeaders : Nat} {req : Request}
    (h : parse input maxHeaders = .complete req) :
    req.store.Wf ∧ req.consumed ≤ input.length ∧ req.headers.length ≤ maxHeaders := by
  unfold parse at h
  split at h
  · simp at h
  next hin =>
  split at h
  · simp at h
  next headEnd hfd =>
  have hhead : headEnd + 4 ≤ input.length := findDoubleCrlf_add_four_le hfd
  have hin' : input.length < sidecarBaseNat := by omega
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
  -- the header-count bound: the `complete` outcome is on the ≤-bound branch,
  -- so `hcount` records that the head did not overflow `maxHeaders`.
  split at h
  · simp at h
  next hcount =>
  split at h
  · simp at h
  injection h with h
  subst h
  -- positions in the head
  have hlenHead : (input.take headEnd).length = headEnd := by
    simp
    omega
  have hpos : ∀ p ∈ crlfPositions (input.take headEnd), p < headEnd := by
    intro p hp
    have := crlfPositions_lt hp
    omega
  -- every segment span ends by headEnd + 1 ≤ input.length
  have hends : ∀ sp ∈ reqSpan :: headerSpans, sp.off + sp.len ≤ headEnd + 1 := by
    rw [← hseg]
    exact segments_end_le hpos (by omega)
  have hendsIn : ∀ sp ∈ reqSpan :: headerSpans,
      sp.off + sp.len ≤ input.length := by
    intro sp hsp
    have := hends sp hsp
    omega
  -- total span length is capped, so the sidecar never overflows
  have hsum : spanSum (reqSpan :: headerSpans) ≤ headEnd + 1 := by
    have := segments_spanSum_le (start := 0) (hi := headEnd)
      (crlfPositions_pairwise (input.take headEnd)) hpos
      (fun p _ => by omega) (by omega)
    rw [hseg] at this
    omega
  -- the request-line entries are main-arena ranges inside the input
  have hreqIn : reqSpan.off + reqSpan.len ≤ input.length :=
    hendsIn reqSpan (by simp)
  have hrlLine := parseRequestLine_end_le hrl
  have hrlLen : reqSpan.off + (sliceSpan input reqSpan).length
      ≤ input.length := by
    have := sliceSpan_length input reqSpan
    omega
  -- the header entries fit via parseHeaders_spec
  have hsc : spanSum (reqSpan :: headerSpans)
      = reqSpan.len + spanSum headerSpans := rfl
  have hcap : (([] : Bytes)).length + spanSum headerSpans < sidecarBaseNat := by
    show 0 + spanSum headerSpans < sidecarBaseNat
    omega
  obtain ⟨-, -, hfits⟩ := parseHeaders_spec hin'
    (fun q hq => hendsIn q (by simp [hq])) hcap hph
  -- assemble Wf of the literal store; the header bound falls out of `hcount`
  refine ⟨?_, show headEnd + 4 ≤ input.length by omega,
    show headers.length ≤ maxHeaders by omega⟩
  intro e he
  have he' : e ∈ mkEntry .method rl.method.off rl.method.len ::
      mkEntry .target rl.target.off rl.target.len ::
      mkEntry .version rl.version.off rl.version.len ::
      headers.flatMap (fun ph => [ph.name, ph.value]) :=
    List.mem_reverse.mp he
  apply Store.inBounds_of_entryFits
  simp only [Array.size_toArray]
  rcases List.mem_cons.mp he' with rfl | he'
  · exact mkEntry_fits_main _ hin' (by omega)
  rcases List.mem_cons.mp he' with rfl | he'
  · exact mkEntry_fits_main _ hin' (by omega)
  rcases List.mem_cons.mp he' with rfl | he'
  · exact mkEntry_fits_main _ hin' (by omega)
  obtain ⟨ph, hph', hmem⟩ := List.mem_flatMap.mp he'
  have hfit := hfits ph hph'
  rcases List.mem_cons.mp hmem with rfl | hmem
  · exact hfit.1
  rcases List.mem_cons.mp hmem with rfl | hmem
  · exact hfit.2
  · simp at hmem

/-- **The parser produces well-formed stores, statically.** Every `complete`
outcome satisfies `Store.Wf`: each registered view range — wire ranges in the
main arena and synthesized canonical names in the sidecar — is in-bounds of
the arena its offset addresses. -/
theorem parse_wf {input : Bytes} {maxHeaders : Nat} {req : Request}
    (h : parse input maxHeaders = .complete req) : req.store.Wf :=
  (parse_complete_spec h).1

/-- The sidecar bounds discipline on its own: every sidecar entry of a
complete store ends inside the synthesized sidecar arena. -/
theorem parse_sidecar_fits {input : Bytes} {maxHeaders : Nat} {req : Request}
    (h : parse input maxHeaders = .complete req) :
    ∀ e ∈ req.store.entries, e.inSidecar = true →
      e.physOff + e.len.toNat ≤ req.store.sidecar.size := by
  intro e he hside
  have hb := parse_wf h e he
  unfold Store.InBounds at hb
  rwa [Store.arenaOf_sidecar _ hside] at hb

/-- **Consumed-bytes monotonicity**: a complete outcome never claims more
bytes than the input holds. -/
theorem parse_consumed_le {input : Bytes} {maxHeaders : Nat} {req : Request}
    (h : parse input maxHeaders = .complete req) : req.consumed ≤ input.length :=
  (parse_complete_spec h).2.1

/-- **Header-count bound is enforced**: a complete outcome never carries more
than `maxHeaders` headers. Equivalently, the `maxHeaders < headers.length`
reject path is reachable only on a head that overflows the bound — a head with
more headers cannot parse `complete`. -/
theorem parse_headers_bounded {input : Bytes} {maxHeaders : Nat} {req : Request}
    (h : parse input maxHeaders = .complete req) : req.headers.length ≤ maxHeaders :=
  (parse_complete_spec h).2.2

/-- On a complete outcome, `resolve` succeeds for every stored entry — the
parser's stores inherit totality of the view from `parse_wf`. -/
theorem parse_resolve_total {input : Bytes} {maxHeaders : Nat} {req : Request}
    (h : parse input maxHeaders = .complete req) :
    ∀ e ∈ req.store.entries, (req.store.resolve e).isSome :=
  req.store.resolve_total (parse_wf h)

end Parse
end Arena
