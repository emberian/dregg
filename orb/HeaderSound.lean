/-
Arena — the header-block *soundness* theory: the meaning-preservation successor
to `parse_wf` for the header fields.

`parse_wf` (Arena/ParseTheorems.lean) is a SAFETY result: every header view
range a `complete` outcome registers — the wire ranges in the main arena and the
synthesized canonical names in the sidecar — is in-bounds of the arena it
addresses, so `resolve` is total and returns exactly `len` bytes. But bounds say
nothing about *which* bytes. A degenerate parser that returned empty-but-in-bounds
header spans (every name/value `⟨0,0⟩`) satisfies `parse_wf` while resolving every
header field to the empty string.

`ArenaSound.lean` closed the request-LINE meaning (each method/target/version
field = its exact input substring). This file closes the header-BLOCK meaning —
per-header field-extraction soundness. For a `complete` parse, for EACH header:

* the header line contains a `:` at offset `ci`, `ci` is the FIRST `:`, and the
  name before it is non-empty (`0 < ci`) — so the name/value split is the RFC
  9112 `field-name ":" OWS field-value OWS` split, at the right byte;
* the resolved VALUE equals its exact OWS-trimmed input substring — the value
  region of the line with leading and trailing SP/HTAB stripped, byte for byte;
* the resolved canonical NAME equals the lowercased pre-colon name bytes — this
  covers BOTH representations: an already-lowercase name resolves out of the main
  arena to the name bytes themselves, and a mixed-case name resolves out of the
  SIDECAR to the lowercased bytes the canonicalization synthesized there.

The degenerate empty-span parser FAILS this: an empty name span forces `ci = 0`
(no room for a name byte), but soundness demands `0 < ci` and `line[ci] = ':'`.

Scope. This proves the per-header field-extraction soundness — the real
soundness core the goal clause asks for ("each safety claim upgraded to a
correctness claim (parse-soundness etc.)"). What is NOT closed here — named
UNCLOSED in HEADER-SOUND-README.md — is the full header-BLOCK re-serialization
(concatenating every reconstructed header line with its CRLF separators back into
the exact input head region); the request-line analogue of that
(`reconstruct_two_sep`) is closed in ArenaSound, but the header-block version
ranges over an arbitrary number of lines with OWS on each and is left open. HPACK
/ QPACK decode-correctness (HTTP/2 and HTTP/3 header compression) is a SEPARATE
codec and is not in scope for this HTTP/1.1 head parser at all.
-/
import Arena.Parse
import Arena.Theorems
import Arena.ParseTheorems
import ArenaSound

namespace Arena
namespace Parse

/-! ## Lowercasing is the identity on an already-lowercase span -/

/-- If a byte list carries no uppercase-ASCII byte, mapping `lowerByte` over it
is the identity. This is what makes the two name representations agree: an
already-lowercase name points into the main arena, and its stored bytes already
equal its own lowercasing. -/
theorem map_lowerByte_id : ∀ {l : Bytes}, hasUpper l = false → l.map lowerByte = l
  | [], _ => rfl
  | x :: xs, h => by
    unfold hasUpper at h
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    obtain ⟨hx, hxs⟩ := h
    have hxl : lowerByte x = x := by simp [lowerByte, hx]
    rw [List.map_cons, hxl, map_lowerByte_id (l := xs) hxs]

/-! ## `resolve` of a freshly minted sidecar entry is its exact sidecar slice -/

/-- `resolve` of an `mkEntry` addressing the sidecar arena returns exactly the
sidecar slice `[physOff, physOff+len)`. The sidecar analogue of
`resolve_mkEntry_main`: for a sidecar entry whose physical offset and length do
not overflow the discriminant and whose range is in-bounds of the sidecar,
`resolve` is definitionally that slice. -/
theorem resolve_mkEntry_sidecar {s : Store} {tag : NameTag} {physOff len : Nat}
    (hphys : physOff < sidecarBaseNat) (hlen : len < sidecarBaseNat)
    (hb : physOff + len ≤ s.sidecar.size) :
    s.resolve (mkEntry tag (sidecarBaseNat + physOff) len)
      = some (s.sidecar.extract physOff (physOff + len)) := by
  have hsize : UInt32.size = 4294967296 := rfl
  have hbase : sidecarBaseNat = 2147483648 := rfl
  have hoff' : (UInt32.ofNat (sidecarBaseNat + physOff)).toNat = sidecarBaseNat + physOff :=
    UInt32.toNat_ofNat_of_lt (by omega)
  have hlen' : (UInt32.ofNat len).toNat = len := UInt32.toNat_ofNat_of_lt (by omega)
  have hside : (mkEntry tag (sidecarBaseNat + physOff) len).inSidecar = true := by
    simp only [mkEntry, Entry.inSidecar, decide_eq_true_eq]
    unfold isSidecarAddr
    rw [hoff']
    omega
  have hphysOff : (mkEntry tag (sidecarBaseNat + physOff) len).physOff = physOff := by
    unfold Entry.physOff
    rw [hside]
    simp only [mkEntry, if_true]
    rw [hoff']
    omega
  have hlent : (mkEntry tag (sidecarBaseNat + physOff) len).len.toNat = len := by
    simp only [mkEntry]
    exact hlen'
  have harena : s.arenaOf (mkEntry tag (sidecarBaseNat + physOff) len) = s.sidecar :=
    Store.arenaOf_sidecar s hside
  simp only [Store.resolve, harena, hphysOff, hlent]
  rw [if_pos hb]

/-- `resolve` of a sidecar `mkEntry`, expressed directly as the concrete sidecar
substring `(S'.drop physOff).take len` (where `s.sidecar = S'.toArray`). -/
theorem resolve_mkEntry_sidecar_toList {s : Store} {tag : NameTag} {physOff len : Nat}
    {S' : List UInt8} (hside : s.sidecar = S'.toArray)
    (hphys : physOff < sidecarBaseNat) (hlen : len < sidecarBaseNat)
    (hb : physOff + len ≤ S'.length) :
    s.resolve (mkEntry tag (sidecarBaseNat + physOff) len)
      = some (((S'.drop physOff).take len).toArray) := by
  have hbsize : physOff + len ≤ s.sidecar.size := by rw [hside]; simpa using hb
  rw [resolve_mkEntry_sidecar hphys hlen hbsize, hside]
  rw [List.extract_toArray, List.extract_eq_drop_take, Nat.add_sub_cancel_left]

/-! ## Slice arithmetic: a drop of a span-slice is an input substring -/

/-- Dropping `k` bytes off a span slice is the input substring `[off+k, off+len)`.
Unconditional list arithmetic — the bridge from the line the header parser sees
(`sliceSpan input sp`) back to concrete input offsets. -/
theorem sliceSpan_drop (input : Bytes) (sp : Span) (k : Nat) :
    (sliceSpan input sp).drop k = (input.drop (sp.off + k)).take (sp.len - k) := by
  unfold sliceSpan
  rw [List.drop_take, List.drop_drop]

/-! ## A prefix knows its own slice -/

/-- If `a ++ b` is a prefix of `t`, then reading `b.length` bytes at offset
`a.length` in `t` returns exactly `b`. This is the sidecar-aware core: a
canonical name written at the current sidecar end survives every later append
(the sidecar only grows to the right), so it still resolves to the bytes that
were written. -/
theorem prefix_drop_take {α : Type _} {a b t : List α} (h : a ++ b <+: t) :
    (t.drop a.length).take b.length = b := by
  obtain ⟨u, hu⟩ := h
  rw [← hu, List.append_assoc]
  rw [show a.length = a.length + 0 by omega, List.drop_append, List.drop_zero, List.take_left]

/-! ## `canonNameEntry` / `parseHeaders` only grow the sidecar (prefix chain) -/

/-- Canonicalizing a name only appends to the sidecar: the incoming sidecar is a
prefix of the outgoing one. -/
theorem canonNameEntry_prefix {input sidecar : Bytes} {sp : Span}
    {sidecar' : Bytes} {e : Entry}
    (h : canonNameEntry input sidecar sp = (sidecar', e)) : sidecar <+: sidecar' := by
  unfold canonNameEntry at h
  simp only [] at h
  split at h
  · injection h with h₁ _; subst h₁; exact ⟨_, rfl⟩
  · injection h with h₁ _; subst h₁; exact List.prefix_refl _

/-- The whole header pass only grows the sidecar: the incoming sidecar is a
prefix of the final one. -/
theorem parseHeaders_prefix {input : Bytes} :
    ∀ {spans : List Span} {sidecar sidecarF : Bytes} {headers : List ParsedHeader},
      parseHeaders input spans sidecar = some (sidecarF, headers) →
      sidecar <+: sidecarF
  | [], sidecar, sidecarF, headers, h => by
    unfold parseHeaders at h
    injection h with h; injection h with h₁ _; subst h₁; exact List.prefix_refl _
  | sp :: rest, sidecar, sidecarF, headers, h => by
    unfold parseHeaders at h
    split at h
    · simp at h
    obtain ⟨raw, hraw, h⟩ := Option.bind_eq_some.mp h
    rcases hce : canonNameEntry input sidecar raw.name with ⟨sidecar', nameEntry⟩
    rw [hce] at h
    obtain ⟨⟨sidecarF', parsed⟩, hrec, h⟩ := Option.bind_eq_some.mp h
    injection h with h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hsf, _⟩ := h
    subst hsf
    exact (canonNameEntry_prefix hce).trans (parseHeaders_prefix hrec)

/-! ## Per-header-line soundness: the spans denote the exact grammar fields -/

/-- **`parseHeaderLine` is sound.** When it accepts a line, there is a first-`:`
offset `ci` and OWS lengths `lead`/`trail` such that the name span is the exact
pre-colon region `⟨off, ci⟩`, the value span is the exact OWS-trimmed value
region `⟨off+ci+1+lead, |trimmed|-trail⟩`, `ci` is genuinely the FIRST `:`, and
the name is non-empty (`0 < ci`). The meaning content: the spans are not merely
in-bounds (`parseHeaderLine_spec`), they are the *right* substrings. -/
theorem parseHeaderLine_sound {off : Nat} {line : Bytes} {hs : RawHeaderSpans}
    (h : parseHeaderLine off line = some hs) :
    ∃ ci lead trail,
      hs.name = ⟨off, ci⟩ ∧
      hs.value = ⟨off + ci + 1 + lead, ((line.drop (ci + 1)).drop lead).length - trail⟩ ∧
      lead = ((line.drop (ci + 1)).takeWhile isOws).length ∧
      trail = (((line.drop (ci + 1)).drop lead).reverse.takeWhile isOws).length ∧
      0 < ci ∧
      ci < line.length ∧
      line[ci]? = some COLON ∧
      (∀ j, j < ci → line[j]? ≠ some COLON) := by
  unfold parseHeaderLine at h
  obtain ⟨ci, hci, h⟩ := Option.bind_eq_some.mp h
  split at h
  · simp at h
  next hz =>
  simp only [] at h
  split at h
  · simp at h
  next hname =>
  split at h
  · simp at h
  next hval =>
  injection h with h
  subst h
  simp only [findByteIdx] at hci
  obtain ⟨hlt, hp, hbefore⟩ := List.findIdx?_eq_some_iff_getElem.mp hci
  have hpos : 0 < ci := Nat.pos_of_ne_zero (by intro hc; apply hz; simp [hc])
  refine ⟨ci, _, _, rfl, rfl, rfl, rfl, hpos, hlt, ?_, ?_⟩
  · rw [List.getElem?_eq_getElem hlt, eq_of_beq hp]
  · intro j hj hcontra
    obtain ⟨hjlt, hje⟩ := List.getElem?_eq_some_iff.mp hcontra
    exact hbefore j hj (by simp [hje])

/-! ## The per-header field-extraction soundness relation -/

/-- Field-extraction soundness of a single parsed header `ph` at head span `sp`,
resolved against store `s`. Packs the per-header meaning content: the header line
`L = sliceSpan input sp` has its first `:` at `ci` with a non-empty name, the
value entry resolves to exactly the OWS-trimmed value substring, and the name
entry resolves to exactly the lowercased pre-colon name bytes. -/
def HeaderFieldSound (input : Bytes) (s : Store) (sp : Span) (ph : ParsedHeader) : Prop :=
  ∃ ci lead trail,
    lead = (((sliceSpan input sp).drop (ci + 1)).takeWhile isOws).length ∧
    trail = ((((sliceSpan input sp).drop (ci + 1)).drop lead).reverse.takeWhile isOws).length ∧
    0 < ci ∧
    ci < (sliceSpan input sp).length ∧
    (sliceSpan input sp)[ci]? = some COLON ∧
    (∀ j, j < ci → (sliceSpan input sp)[j]? ≠ some COLON) ∧
    (∃ vb, s.resolve ph.value = some vb ∧
      vb.toList = (((sliceSpan input sp).drop (ci + 1)).drop lead).take
        ((((sliceSpan input sp).drop (ci + 1)).drop lead).length - trail)) ∧
    (∃ nb, s.resolve ph.name = some nb ∧
      nb.toList = ((sliceSpan input sp).take ci).map lowerByte)

/-- Header-span/parsed-header lists stand in one-to-one `HeaderFieldSound`
correspondence. (A local stand-in for `List.Forall₂`, which is not in the
core library this tree builds against.) -/
inductive HeadersSound (input : Bytes) (s : Store) :
    List Span → List ParsedHeader → Prop where
  | nil : HeadersSound input s [] []
  | cons {sp : Span} {ph : ParsedHeader} {sps : List Span} {phs : List ParsedHeader} :
      HeaderFieldSound input s sp ph → HeadersSound input s sps phs →
      HeadersSound input s (sp :: sps) (ph :: phs)

/-! ## The header-pass soundness theorem -/

/-- **The header pass is sound.** Every parsed header's value and name resolve —
in the FINAL store — to their exact input meanings: the value to its OWS-trimmed
input substring, the name to its lowercased pre-colon bytes (main-arena or
sidecar). Threaded so the sidecar entries resolve against the final sidecar
`SFull`, of which every intermediate sidecar is a prefix. -/
theorem parseHeaders_sound {input : Bytes} {s : Store} {SFull : List UInt8}
    (hmain : s.main = input.toArray) (hsc : s.sidecar = SFull.toArray)
    (hin : input.length < sidecarBaseNat) :
    ∀ {spans : List Span} {sidecar sidecarF : Bytes} {headers : List ParsedHeader},
      (∀ sp ∈ spans, sp.off + sp.len ≤ input.length) →
      sidecar.length + spanSum spans < sidecarBaseNat →
      parseHeaders input spans sidecar = some (sidecarF, headers) →
      sidecarF <+: SFull →
      HeadersSound input s spans headers
  | [], sidecar, sidecarF, headers, _, _, h, _ => by
    unfold parseHeaders at h
    injection h with h; injection h with _ h₂; subst h₂
    exact HeadersSound.nil
  | sp :: rest, sidecar, sidecarF, headers, hsp, hcap, h, hpre => by
    have hsc' : spanSum (sp :: rest) = sp.len + spanSum rest := rfl
    unfold parseHeaders at h
    split at h
    · simp at h
    obtain ⟨raw, hraw, h⟩ := Option.bind_eq_some.mp h
    rcases hce : canonNameEntry input sidecar raw.name with ⟨sidecar', nameEntry⟩
    rw [hce] at h
    obtain ⟨⟨sidecarF', parsed⟩, hrec, h⟩ := Option.bind_eq_some.mp h
    injection h with h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hsf, hhd⟩ := h
    subst hsf
    subst hhd
    -- geometry of the current header span
    have hspHere : sp.off + sp.len ≤ input.length := hsp sp (by simp)
    have hLlen : (sliceSpan input sp).length = sp.len := by
      rw [sliceSpan_length]; omega
    -- soundness of the line parse
    obtain ⟨ci, lead, trail, hnameSp, hvalSp, hleadEq, htrailEq, hpos, hciLt,
        hcolon, hbefore⟩ := parseHeaderLine_sound hraw
    have hciSpLt : ci < sp.len := hLlen ▸ hciLt
    -- span-length facts
    have hleadLe : lead ≤ (sliceSpan input sp).length - (ci + 1) := by
      rw [hleadEq, ← List.length_drop]
      exact (List.takeWhile_sublist _).length_le
    have hci1lead : ci + 1 + lead ≤ sp.len := by rw [hLlen] at hleadLe; omega
    -- the value entry and its input substring
    have hvalOff : raw.value.off = sp.off + ci + 1 + lead := by rw [hvalSp]
    have hvalLen : raw.value.len
        = (((sliceSpan input sp).drop (ci + 1)).drop lead).length - trail := by rw [hvalSp]
    have htfInput : ((sliceSpan input sp).drop (ci + 1)).drop lead
        = (input.drop (sp.off + (ci + 1 + lead))).take (sp.len - (ci + 1 + lead)) := by
      rw [List.drop_drop, sliceSpan_drop]
    have htfLen : (((sliceSpan input sp).drop (ci + 1)).drop lead).length
        = sp.len - (ci + 1 + lead) := by
      rw [htfInput, List.length_take, List.length_drop]; omega
    -- value resolves to exactly its OWS-trimmed input substring
    have hvOffAssoc : sp.off + ci + 1 + lead = sp.off + (ci + 1 + lead) := by omega
    have hb1 : raw.value.off < sidecarBaseNat := by rw [hvalOff]; omega
    have hb2 : raw.value.len < sidecarBaseNat := by rw [hvalLen, htfLen]; omega
    have hb3 : raw.value.off + raw.value.len ≤ input.length := by
      rw [hvalOff, hvalLen, htfLen]; omega
    have hVres := resolve_mkEntry_main_toList (tag := .headerValue) hmain hb1 hb2 hb3
    have hVList : (input.drop raw.value.off).take raw.value.len
        = (((sliceSpan input sp).drop (ci + 1)).drop lead).take
            ((((sliceSpan input sp).drop (ci + 1)).drop lead).length - trail) := by
      rw [hvalOff, hvOffAssoc, hvalLen, htfLen, htfInput, List.take_take,
        Nat.min_eq_left (show sp.len - (ci + 1 + lead) - trail ≤ sp.len - (ci + 1 + lead) by omega)]
    -- name geometry
    have hRN : sliceSpan input raw.name = (input.drop sp.off).take ci := by
      rw [hnameSp]; simp [sliceSpan]
    have hRNlen : ((input.drop sp.off).take ci).length = ci := by
      rw [List.length_take, List.length_drop]; omega
    have hSliceTake : (sliceSpan input sp).take ci = (input.drop sp.off).take ci := by
      unfold sliceSpan
      rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hciSpLt)]
    -- sidecar growth / prefix facts (computed before `hce` is consumed)
    have hchain : sidecar' <+: SFull := (parseHeaders_prefix hrec).trans hpre
    have hnLenLe : raw.name.len ≤ sp.len := by rw [hnameSp]; exact Nat.le_of_lt hciSpLt
    have hgrow := (canonNameEntry_length hce).2
    have hcap' : sidecar'.length + spanSum rest < sidecarBaseNat := by
      simp only [spanSum] at hcap; omega
    -- name resolves to exactly the lowercased pre-colon name bytes
    have hName : ∃ nb, s.resolve nameEntry = some nb ∧
        nb.toList = ((sliceSpan input sp).take ci).map lowerByte := by
      unfold canonNameEntry at hce
      simp only [] at hce
      split at hce
      · -- mixed-case name → sidecar
        injection hce with he1 he2
        subst he2
        have hnlen : raw.name.len = ci := by rw [hnameSp]
        have hpfx : sidecar ++ (sliceSpan input raw.name).map lowerByte <+: SFull := by
          rw [he1]; exact hchain
        have hmapLen : ((sliceSpan input raw.name).map lowerByte).length = ci := by
          rw [List.length_map, hRN, hRNlen]
        have hsb1 : sidecar.length < sidecarBaseNat := by omega
        have hsb2 : ci < sidecarBaseNat := by omega
        have hsb3 : sidecar.length + ci ≤ SFull.length := by
          have hle := hpfx.length_le
          rw [List.length_append, hmapLen] at hle
          omega
        rw [hnlen]
        have hres := resolve_mkEntry_sidecar_toList (tag := .headerName) (S' := SFull)
          hsc hsb1 hsb2 hsb3
        refine ⟨_, hres, ?_⟩
        rw [Array.toList_toArray]
        have hpref := prefix_drop_take hpfx
        rw [hmapLen] at hpref
        rw [hpref, hRN, hSliceTake]
      · -- already-lowercase name → main arena
        rename_i hup
        injection hce with _ he2
        subst he2
        have hnoff : raw.name.off = sp.off := by rw [hnameSp]
        have hnlen : raw.name.len = ci := by rw [hnameSp]
        have hmb1 : raw.name.off < sidecarBaseNat := by rw [hnoff]; omega
        have hmb2 : raw.name.len < sidecarBaseNat := by rw [hnlen]; omega
        have hmb3 : raw.name.off + raw.name.len ≤ input.length := by rw [hnoff, hnlen]; omega
        have hres := resolve_mkEntry_main_toList (tag := .headerName) hmain hmb1 hmb2 hmb3
        have hUp : hasUpper ((input.drop sp.off).take ci) = false := by
          have hupF : hasUpper (sliceSpan input raw.name) = false := by simpa using hup
          rw [hRN] at hupF; exact hupF
        refine ⟨_, hres, ?_⟩
        rw [Array.toList_toArray, hnoff, hnlen, hSliceTake, map_lowerByte_id hUp]
    -- assemble the head + recurse on the tail
    refine HeadersSound.cons ?_ ?_
    · exact ⟨ci, lead, trail, hleadEq, htrailEq, hpos, hciLt, hcolon, hbefore,
        ⟨_, hVres, by rw [Array.toList_toArray]; exact hVList⟩, hName⟩
    · exact parseHeaders_sound hmain hsc hin
        (fun q hq => hsp q (List.mem_cons_of_mem sp hq)) hcap' hrec hpre

/-! ## Top-level: a complete parse extracts every header field soundly -/

/-- **The parser's header-field extraction is sound.** For a `complete`
outcome there is a list of header-line spans (the request-head segments after the
request line) in one-to-one correspondence with `req.headers`, and every header
satisfies `HeaderFieldSound`: its value resolves to its exact OWS-trimmed input
substring and its canonical name resolves to its exact lowercased pre-colon input
bytes (main-arena or sidecar). The MEANING successor to `parse_wf` for headers: a
degenerate parser returning empty header spans satisfies `parse_wf` but fails
this — an empty name span forces `ci = 0`, contradicting `0 < ci`. -/
theorem parse_headers_sound {input : Bytes} {maxHeaders : Nat} {req : Request}
    (h : parse input maxHeaders = .complete req) :
    ∃ headerSpans : List Span,
      (∀ sp ∈ headerSpans, sp.off + sp.len ≤ input.length) ∧
      HeadersSound input req.store headerSpans req.headers := by
  unfold parse at h
  split at h
  · simp at h
  next hin =>
  split at h
  · simp at h
  next headEnd hfd =>
  have hhead : headEnd + 4 ≤ input.length := findDoubleCrlf_add_four_le hfd
  have hin' : input.length < sidecarBaseNat := by
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
  -- store field shapes off `h : {…} = req`
  have hSM : req.store.main = input.toArray := (congrArg (fun r => r.store.main) h).symm
  have hSS : req.store.sidecar = sidecar.toArray := (congrArg (fun r => r.store.sidecar) h).symm
  have hHE : req.headers = headers := (congrArg (fun r => r.headers) h).symm
  -- span accounting: every header span ends inside the input; sidecar starts empty
  have hlenHead : (input.take headEnd).length = headEnd := by
    rw [List.length_take]; omega
  have hpos : ∀ p ∈ crlfPositions (input.take headEnd), p < headEnd := by
    intro p hp; have := crlfPositions_lt hp; omega
  have hends : ∀ sp ∈ reqSpan :: headerSpans, sp.off + sp.len ≤ headEnd + 1 := by
    rw [← hseg]; exact segments_end_le hpos (by omega)
  have hendsIn : ∀ sp ∈ headerSpans, sp.off + sp.len ≤ input.length := by
    intro sp hsp; have := hends sp (by simp [hsp]); omega
  have hsum : spanSum (reqSpan :: headerSpans) ≤ headEnd + 1 := by
    have := segments_spanSum_le (start := 0) (hi := headEnd)
      (crlfPositions_pairwise (input.take headEnd)) hpos (fun p _ => by omega) (by omega)
    rw [hseg] at this; omega
  have hcap : ([] : Bytes).length + spanSum headerSpans < sidecarBaseNat := by
    have : spanSum (reqSpan :: headerSpans) = reqSpan.len + spanSum headerSpans := rfl
    simp only [List.length_nil, Nat.zero_add]; omega
  refine ⟨headerSpans, hendsIn, ?_⟩
  rw [hHE]
  exact parseHeaders_sound hSM hSS hin' hendsIn hcap hph (List.prefix_refl _)

end Parse
end Arena
