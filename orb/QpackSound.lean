/-
H3 QPACK — the decoder's *correctness* theory: the meaning-preservation
successor to the `Wf`-only theorems of `H3/Qpack.lean`.

`decodeFieldSection_wf` (H3/Qpack.lean) is a SAFETY result: every view entry the
QPACK decode emits into the arena `Store` is in-bounds. But bounds say nothing
about *which* bytes. This file proves the CORRECTNESS successor for the
literal-field-line-with-literal-name representation (RFC 9204 §4.5.6),
non-Huffman (H=0) literal name and value:

* the decode of `encQLit name value` accepts, yields exactly one regular field
  `⟨ne, ve⟩` and no pseudo-headers, and
* the decoded field EQUALS the encoded field byte for byte: the decoded store
  RESOLVES `ne` to exactly `name` and `ve` to exactly `value`
  (`decodeQ_literalName_sound`).

See H2-SOUND-README.md (the QPACK analogue is documented there too). The Arena
-level `resolve`/append lemmas are re-proved here (identical to the H2Sound ones)
because H3.Qpack has its own emit primitive; the two protocol libraries stay
independent.

Scope. The Huffman string representation (H=1) is UNCLOSED — the axiomatized
`HuffmanDecoder` interface; every theorem fixes H=0 and the decoder is never
consulted. Static/dynamic-table references and multi-line sections are out of
scope, exactly as in H2Sound.lean. Zero sorries; #print axioms is the sacred
subset.
-/
import H3.Qpack

namespace H3
namespace Qpack

open Arena

/-! ## Array-extract algebra (the `resolve`/append bridge) -/

theorem extract_append_right (pre q : Array UInt8) :
    (pre ++ q).extract pre.size (pre.size + q.size) = q := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  simp [Array.toList_append, List.drop_append, Nat.add_sub_cancel_left]

theorem extract_append_left_of_le (A B : Array UInt8) (start stop : Nat)
    (hss : start ≤ stop) (h : stop ≤ A.size) :
    (A ++ B).extract start stop = A.extract start stop := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract, Array.toList_extract, Array.toList_append,
      List.extract_eq_drop_take, List.extract_eq_drop_take]
  have hlen : A.toList.length = A.size := by simp
  rw [List.drop_append_of_le_length (by omega),
      List.take_append_of_le_length (by rw [List.length_drop]; omega)]

/-! ## `resolve` of a sidecar entry, and its stability -/

theorem resolve_of_sidecar (s : Store) (e : Entry)
    (hside : e.inSidecar = true)
    (hfit : e.physOff + e.len.toNat ≤ s.sidecar.size) :
    s.resolve e = some (s.sidecar.extract e.physOff (e.physOff + e.len.toNat)) := by
  unfold Store.resolve
  rw [Store.arenaOf_sidecar s hside]
  simp only [hfit, if_pos]

theorem resolve_pushEntry (s : Store) (e' e : Entry) :
    (s.pushEntry e').resolve e = s.resolve e := rfl

theorem resolve_appendSidecar (s : Store) (bs2 : Array UInt8) (e : Entry)
    (hib : s.InBounds e) : (s.appendSidecar bs2).resolve e = s.resolve e := by
  by_cases hside : e.inSidecar
  · have hfit : e.physOff + e.len.toNat ≤ s.sidecar.size := by
      unfold Store.InBounds Store.arenaOf at hib
      simp only [hside, if_pos] at hib
      exact hib
    have hfit' : e.physOff + e.len.toNat ≤ (s.appendSidecar bs2).sidecar.size := by
      unfold Store.appendSidecar
      simp only [Array.size_append]
      omega
    rw [resolve_of_sidecar (s.appendSidecar bs2) e hside hfit',
        resolve_of_sidecar s e hside hfit]
    unfold Store.appendSidecar
    simp only
    rw [extract_append_left_of_le s.sidecar bs2 e.physOff (e.physOff + e.len.toNat)
      (by omega) hfit]
  · simp only [Bool.not_eq_true] at hside
    unfold Store.resolve Store.arenaOf Store.appendSidecar
    simp only [hside, Bool.false_eq_true, if_false]

theorem resolve_emitSidecar (st : Store) (tag : NameTag) (bs : Bytes)
    (st' : Store) (e : Entry) (h : emitSidecar st tag bs = some (st', e)) :
    st'.resolve e = some bs.toArray := by
  unfold emitSidecar at h
  split at h
  · exact absurd h (by simp)
  · rename_i hlt
    injection h with h
    injection h with h₁ h₂
    subst h₁; subst h₂
    have hsz : st.sidecar.size + bs.length < sidecarBaseNat := by omega
    have hoff : (UInt32.ofNat (sidecarBaseNat + st.sidecar.size)).toNat
        = sidecarBaseNat + st.sidecar.size := by
      show (sidecarBaseNat + st.sidecar.size) % 2 ^ 32 = sidecarBaseNat + st.sidecar.size
      unfold sidecarBaseNat at *; omega
    have hlen : (UInt32.ofNat bs.length).toNat = bs.length := by
      show bs.length % 2 ^ 32 = bs.length
      unfold sidecarBaseNat at hsz; omega
    have hside : Entry.inSidecar
        { tag := tag, off := UInt32.ofNat (sidecarBaseNat + st.sidecar.size),
          len := UInt32.ofNat bs.length } = true := by
      unfold Entry.inSidecar
      simp only [hoff, decide_eq_true_eq]
      unfold isSidecarAddr; omega
    have hphys : Entry.physOff
        { tag := tag, off := UInt32.ofNat (sidecarBaseNat + st.sidecar.size),
          len := UInt32.ofNat bs.length } = st.sidecar.size := by
      unfold Entry.physOff
      simp only [hside, if_true, hoff]
      omega
    have hlent : ((UInt32.ofNat bs.length)).toNat = bs.length := hlen
    rw [resolve_pushEntry]
    have hsidecar : (st.appendSidecar bs.toArray).sidecar = st.sidecar ++ bs.toArray := rfl
    have hbta : bs.toArray.size = bs.length := rfl
    have hfit : Entry.physOff
        { tag := tag, off := UInt32.ofNat (sidecarBaseNat + st.sidecar.size),
          len := UInt32.ofNat bs.length }
        + ((UInt32.ofNat bs.length)).toNat
        ≤ (st.appendSidecar bs.toArray).sidecar.size := by
      rw [hsidecar, hphys, hlent]
      simp only [Array.size_append, hbta]
      omega
    rw [resolve_of_sidecar (st.appendSidecar bs.toArray) _ hside hfit]
    rw [hsidecar, hphys, hlent]
    congr 1
    have := extract_append_right st.sidecar bs.toArray
    rw [hbta] at this
    exact this

/-! ## `emitSidecar` / `emitField` succeed and are correct -/

theorem emitSidecar_ok (st : Store) (tag : NameTag) (bs : Bytes)
    (hroom : st.sidecar.size + bs.length < sidecarBaseNat) :
    ∃ st' e, emitSidecar st tag bs = some (st', e) := by
  unfold emitSidecar
  rw [if_neg (by omega)]
  exact ⟨_, _, rfl⟩

theorem emitField_field_ok (st : Store) (name value : Bytes)
    (hcl : classifyName name = none)
    (hroom : st.sidecar.size + name.length + value.length < sidecarBaseNat) :
    ∃ st' ne ve, emitField st name value = .ok (st', .field ⟨ne, ve⟩) ∧
      st'.resolve ne = some name.toArray ∧
      st'.resolve ve = some value.toArray := by
  obtain ⟨st₁, ne, hemit₁⟩ := emitSidecar_ok st .headerName name (by omega)
  have hs₁ : st₁.sidecar.size = st.sidecar.size + name.length := by
    rw [(emitSidecar_eq st .headerName name st₁ ne hemit₁).1]
    show (st.appendSidecar name.toArray).sidecar.size = _
    unfold Store.appendSidecar
    simp [Array.size_append]
  obtain ⟨st₂, ve, hemit₂⟩ := emitSidecar_ok st₁ .headerValue value (by rw [hs₁]; omega)
  refine ⟨st₂, ne, ve, ?_, ?_, ?_⟩
  · unfold emitField
    rw [hcl]
    simp only [hemit₁, hemit₂]
  · have hib₁ : st₁.InBounds ne := by
      have hst₁ := (emitSidecar_eq st .headerName name st₁ ne hemit₁).1
      have hbnd := emitSidecar_inBounds st .headerName name st₁ ne hemit₁
      rw [hst₁, Store.inBounds_pushEntry]
      exact hbnd
    rw [(emitSidecar_eq st₁ .headerValue value st₂ ve hemit₂).1,
        resolve_pushEntry, resolve_appendSidecar _ _ _ hib₁]
    exact resolve_emitSidecar st .headerName name st₁ ne hemit₁
  · exact resolve_emitSidecar st₁ .headerValue value st₂ ve hemit₂

/-! ## Non-Huffman string literals decode to their exact bytes -/

/-- A 3-bit length prefix `< 7` in a first byte `0x20 + len` (N=0, H=0) decodes to
exactly `len`, consuming no continuation bytes. -/
theorem decPrefixInt3_ofNat (len : Nat) (rest : Bytes) (h : len < 7) :
    decPrefixInt 3 (UInt8.ofNat (0x20 + len)) rest = some (len, 0) := by
  unfold decPrefixInt
  have ht : (UInt8.ofNat (0x20 + len)).toNat = 0x20 + len :=
    UInt8.toNat_ofNat_of_lt (show 0x20 + len < 256 by omega)
  have hp : (2:Nat) ^ 3 = 8 := by decide
  simp only [ht]
  have hmod : (0x20 + len) % 2 ^ 3 = len := by rw [hp]; omega
  rw [hmod, if_pos (by rw [hp]; omega)]

/-- A zero prefix byte `0x00` decodes to 0 with no continuation. -/
theorem decPrefixInt8_zero (rest : Bytes) : decPrefixInt 8 0x00 rest = some (0, 0) := by
  unfold decPrefixInt; rfl

theorem decPrefixInt7_zero (rest : Bytes) : decPrefixInt 7 0x00 rest = some (0, 0) := by
  unfold decPrefixInt; rfl

/-- A raw (H=0) 3-bit-prefixed string literal decodes to exactly its bytes. -/
theorem decStr3_raw (hd : HuffmanDecoder) (s t : Bytes) (hlen : s.length < 7) :
    decStr hd 3 (UInt8.ofNat (0x20 + s.length)) (s ++ t) = .ok (s, s.length) := by
  unfold decStr
  rw [decPrefixInt3_ofNat s.length (s ++ t) hlen]
  simp only [List.drop_zero, List.take_left]
  rw [if_neg (by omega : ¬ (s.length < s.length))]
  have ht : (UInt8.ofNat (0x20 + s.length)).toNat = 0x20 + s.length :=
    UInt8.toNat_ofNat_of_lt (show 0x20 + s.length < 256 by omega)
  have hp : (2:Nat) ^ 3 = 8 := by decide
  have hhuff : ¬ ((UInt8.ofNat (0x20 + s.length)).toNat / 2 ^ 3 % 2 = 1) := by
    rw [ht, hp]; omega
  rw [if_neg hhuff, Nat.zero_add]

/-- A 7-bit length prefix `< 127` decodes to exactly that length. -/
theorem decPrefixInt7_ofNat (len : Nat) (rest : Bytes) (h : len < 127) :
    decPrefixInt 7 (UInt8.ofNat len) rest = some (len, 0) := by
  unfold decPrefixInt
  have ht : (UInt8.ofNat len).toNat = len := UInt8.toNat_ofNat_of_lt (show len < 256 by omega)
  have hp : (2:Nat) ^ 7 = 128 := by decide
  simp only [ht]
  rw [Nat.mod_eq_of_lt (by rw [hp]; omega), if_pos (by rw [hp]; omega)]

/-- A raw (H=0) 7-bit-prefixed string literal decodes to exactly its bytes. -/
theorem decStr7_raw (hd : HuffmanDecoder) (s t : Bytes) (hlen : s.length < 127) :
    decStr hd 7 (UInt8.ofNat s.length) (s ++ t) = .ok (s, s.length) := by
  unfold decStr
  rw [decPrefixInt7_ofNat s.length (s ++ t) hlen]
  simp only [List.drop_zero, List.take_left]
  rw [if_neg (by omega : ¬ (s.length < s.length))]
  have ht : (UInt8.ofNat s.length).toNat = s.length :=
    UInt8.toNat_ofNat_of_lt (show s.length < 256 by omega)
  have hp : (2:Nat) ^ 7 = 128 := by decide
  have hhuff : ¬ ((UInt8.ofNat s.length).toNat / 2 ^ 7 % 2 = 1) := by
    rw [ht, hp]; omega
  rw [if_neg hhuff, Nat.zero_add]

/-- The value read at end of input (no trailing bytes). -/
theorem decStr7_raw_nil (hd : HuffmanDecoder) (s : Bytes) (hlen : s.length < 127) :
    decStr hd 7 (UInt8.ofNat s.length) s = .ok (s, s.length) := by
  have h := decStr7_raw hd s [] hlen
  rwa [List.append_nil] at h

/-! ## One §4.5.6 literal-with-literal-name line decodes to its (name, value) -/

/-- The wire encoding of one RFC 9204 §4.5.6 literal field line with a literal
name: first byte `0x20 + nameLen` (pattern `001`, N=0, H=0, 3-bit name length),
raw name bytes, then a raw (H=0) 7-bit-length-prefixed value literal. -/
def encQLine (name value : Bytes) : Bytes :=
  UInt8.ofNat (0x20 + name.length) :: (name ++ UInt8.ofNat value.length :: value)

/-- **`decodeOneLine` correctness for the §4.5.6 representation.** -/
theorem decodeOneLine_literalName_sound (hd : HuffmanDecoder) (st : Store)
    (name value : Bytes)
    (hnl : name.length < 7) (hvl : value.length < 127)
    (hnu : utf8Ok name = true) (hvu : utf8Ok value = true)
    (hcl : classifyName name = none)
    (hroom : st.sidecar.size + name.length + value.length < sidecarBaseNat) :
    ∃ st' ne ve,
      decodeOneLine hd st (encQLine name value)
        = .ok (st', .field ⟨ne, ve⟩, 1 + name.length + 1 + value.length) ∧
      st'.resolve ne = some name.toArray ∧
      st'.resolve ve = some value.toArray := by
  obtain ⟨st', ne, ve, hem, hrn, hrv⟩ := emitField_field_ok st name value hcl (by omega)
  refine ⟨st', ne, ve, ?_, hrn, hrv⟩
  have hb : (UInt8.ofNat (0x20 + name.length)).toNat = 0x20 + name.length :=
    UInt8.toNat_ofNat_of_lt (show 0x20 + name.length < 256 by omega)
  have hdrop : (name ++ UInt8.ofNat value.length :: value).drop name.length
      = UInt8.ofNat value.length :: value := by rw [List.drop_left]
  have h80 : (0x80 ≤ (UInt8.ofNat (0x20 + name.length)).toNat) = False := by
    rw [hb]; simp only [eq_iff_iff, iff_false, Nat.not_le]; omega
  have h40 : (0x40 ≤ (UInt8.ofNat (0x20 + name.length)).toNat) = False := by
    rw [hb]; simp only [eq_iff_iff, iff_false, Nat.not_le]; omega
  have h20 : (0x20 ≤ (UInt8.ofNat (0x20 + name.length)).toNat) = True := by
    rw [hb]; simp only [eq_iff_iff, iff_true]; omega
  unfold decodeOneLine encQLine
  simp only [h80, h40, h20, reduceIte,
    decStr3_raw hd name (UInt8.ofNat value.length :: value) hnl, hnu, hdrop,
    decStr7_raw_nil hd value hvl, hvu, hem]

/-! ## A single-line field section -/

theorem decodeLines_one_line (hd : HuffmanDecoder) (st st' : Store)
    (b : UInt8) (rest : Bytes) (fl : FieldLine) (n : Nat)
    (hone : decodeOneLine hd st (b :: rest) = .ok (st', .field fl, n))
    (hdrop : (b :: rest).drop n = []) :
    decodeLines hd st (b :: rest) {} [] = .ok (st', {}, [fl]) := by
  rw [decodeLines]
  split
  · rename_i e heq; rw [hone] at heq; exact absurd heq (by simp)
  · rename_i st'' out n' heq
    rw [hone] at heq
    simp only [Except.ok.injEq, Prod.mk.injEq] at heq
    obtain ⟨hs, hout, hn⟩ := heq
    subst hs; subst hout; subst hn
    simp only [hdrop]
    rw [decodeLines]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]

/-! ## The headline correctness theorem -/

/-- The empty store. -/
def emptyStore : Store := { main := #[], sidecar := #[], entries := [] }

/-- The full field section: the `00 00` prefix (encoded Required Insert Count 0,
Delta Base 0 — no dynamic references) followed by one §4.5.6 line. -/
def encQLit (name value : Bytes) : Bytes := 0x00 :: 0x00 :: encQLine name value

/-- **QPACK decode correctness (RFC 9204 §4.5.6, literal name, H=0).** Decoding
`encQLit name value` — a field section with the no-dynamic-reference prefix and
one literal-name literal-value line — into the empty store accepts, yields
exactly one regular field `⟨ne, ve⟩` and no pseudo-headers, and the decoded field
RESOLVES to exactly the encoded bytes: `ne` to `name`, `ve` to `value`. Holds for
every Huffman-decoder behavior (the Huffman bit is clear). -/
theorem decodeQ_literalName_sound (hd : HuffmanDecoder) (name value : Bytes)
    (hnl : name.length < 7) (hvl : value.length < 127)
    (hnu : utf8Ok name = true) (hvu : utf8Ok value = true)
    (hcl : classifyName name = none) :
    ∃ (r : Decoded) (ne ve : Entry),
      decodeFieldSection hd emptyStore (encQLit name value) = .ok r ∧
      r.fields = [⟨ne, ve⟩] ∧ r.pseudo = {} ∧
      r.store.resolve ne = some name.toArray ∧
      r.store.resolve ve = some value.toArray := by
  have hroom : emptyStore.sidecar.size + name.length + value.length < sidecarBaseNat := by
    show 0 + name.length + value.length < sidecarBaseNat
    unfold sidecarBaseNat; omega
  obtain ⟨st', ne, ve, hone, hrn, hrv⟩ :=
    decodeOneLine_literalName_sound hd emptyStore name value hnl hvl hnu hvu hcl hroom
  simp only [encQLine] at hone
  have hdrop : (UInt8.ofNat (0x20 + name.length) ::
      (name ++ UInt8.ofNat value.length :: value)).drop
      (1 + name.length + 1 + value.length) = [] := by
    apply List.drop_eq_nil_of_le
    simp only [List.length_cons, List.length_append]
    omega
  have hlines := decodeLines_one_line hd emptyStore st'
    (UInt8.ofNat (0x20 + name.length))
    (name ++ UInt8.ofNat value.length :: value) ⟨ne, ve⟩ _ hone hdrop
  refine ⟨⟨st', {}, [⟨ne, ve⟩]⟩, ne, ve, ?_, rfl, rfl, hrn, hrv⟩
  unfold decodeFieldSection encQLit encQLine
  simp only [decPrefixInt8_zero, decPrefixInt7_zero, List.drop_zero, ne_eq,
    not_true_eq_false, reduceIte, hlines]

end Qpack
end H3
