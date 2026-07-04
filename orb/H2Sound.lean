/-
H2 HPACK — the decoder's *correctness* theory: the meaning-preservation
successor to the `Wf`-only theorems of `H2/Hpack.lean`.

`decodeHeaderBlock_wf` (H2/Hpack.lean) is a SAFETY result: every view entry the
HPACK decode emits into the arena `Store` is in-bounds of the arena it
addresses, so `resolve` is total and returns exactly `len` bytes. But bounds say
nothing about *which* bytes. A degenerate decoder that appended nothing and
registered empty spans (`⟨sidecarBase, 0⟩`) would satisfy `decodeHeaderBlock_wf`
while resolving every decoded name/value to the empty string — total nonsense
that still "type-checks" as well-formed.

This file states and proves the CORRECTNESS successor for the literal-header
-field-with-incremental-indexing representation (RFC 7541 §6.2.1), non-Huffman
(H=0) literal name and value — the real correctness core:

* the decode of `encLit name value` accepts, yields exactly one regular field
  `⟨ne, ve⟩` and no pseudo-headers, and
* the decoded field EQUALS the encoded field byte for byte: the decoded store
  RESOLVES the name entry `ne` to exactly `name` and the value entry `ve` to
  exactly `value` (`decode_literalInc_sound`). The decode is a faithful inverse
  of the literal encoding.

The degenerate empty-span decoder FAILS this: for any non-empty `name`,
`resolve ne = some name.toArray ≠ some #[]` (`degenerate_decoder_refuted`).

Scope. The Huffman string representation (H=1) is UNCLOSED — it is the
axiomatized `HuffmanDecoder` interface of `H2/Hpack.lean`, with no implementation
to be sound against; every theorem here fixes H=0 and the decoder is never
consulted, so the results hold for *every* Huffman-decoder behavior. The
dynamic-table insertion side effect of §6.2.1 is the explicit out-of-scope stub
of `H2/Hpack.lean` (no table state exists); the store-emit it performs IS the
"insertion" this model realizes, and that emit is what is proven faithful here.
See H2-SOUND-README.md.
-/
import H2.Hpack

namespace H2
namespace Hpack

open Arena

/-! ## Array-extract algebra (the `resolve`/append bridge) -/

/-- Extracting the trailing block of an append at exactly its boundary returns
that block. This is the sidecar analogue of `Arena.Parse.resolve_mkEntry_main`'s
`Array.extract` bridge: the emitted view range is exactly the appended bytes. -/
theorem extract_append_right (pre q : Array UInt8) :
    (pre ++ q).extract pre.size (pre.size + q.size) = q := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  simp [Array.toList_append, List.drop_append, Nat.add_sub_cancel_left]

/-- Extracting a range that fits inside the *left* operand of an append is
unaffected by the right operand. This is what makes an already-emitted sidecar
entry keep resolving to the same bytes when the sidecar grows again (the value
append after the name append). -/
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

/-- `resolve` of an in-bounds sidecar entry is exactly the sidecar slice it
names. -/
theorem resolve_of_sidecar (s : Store) (e : Entry)
    (hside : e.inSidecar = true)
    (hfit : e.physOff + e.len.toNat ≤ s.sidecar.size) :
    s.resolve e = some (s.sidecar.extract e.physOff (e.physOff + e.len.toNat)) := by
  unfold Store.resolve
  rw [Store.arenaOf_sidecar s hside]
  simp only [hfit, if_pos]

/-- Registering another entry never changes what an entry resolves to. -/
theorem resolve_pushEntry (s : Store) (e' e : Entry) :
    (s.pushEntry e').resolve e = s.resolve e := rfl

/-- Growing the sidecar never changes what an already-in-bounds entry resolves
to. -/
theorem resolve_appendSidecar (s : Store) (bs2 : Array UInt8) (e : Entry)
    (hib : s.InBounds e) : (s.appendSidecar bs2).resolve e = s.resolve e := by
  by_cases hside : e.inSidecar
  · -- sidecar entry: the fit is preserved, and the extract ignores the tail
    have hfit : e.physOff + e.len.toNat ≤ s.sidecar.size := by
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
  · -- main entry: appendSidecar leaves the main arena untouched
    simp only [Bool.not_eq_true] at hside
    unfold Store.resolve Store.arenaOf Store.appendSidecar
    simp only [hside, Bool.false_eq_true, if_false]

/-- **The one-emit correctness lemma.** The entry `emitSidecar` registers
resolves, in the store it returns, to exactly the appended bytes. -/
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
    -- resolve the emitted entry over the pushEntry(appendSidecar) store
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

/-! ## One decoded regular field resolves to its two byte strings -/

/-- **`emitField` correctness** (regular-field, i.e. non-pseudo, case). When the
name is not a routed pseudo-header, `emitField` registers a name entry and a
value entry that resolve, in the returned store, to exactly `name` and `value`.
-/
theorem emitField_field_resolve (st : Store) (name value : Bytes) (st' : Store)
    (out : LineOut) (hcl : classifyName name = none)
    (h : emitField st name value = .ok (st', out)) :
    ∃ ne ve, out = .field ⟨ne, ve⟩ ∧
      st'.resolve ne = some name.toArray ∧
      st'.resolve ve = some value.toArray := by
  unfold emitField at h
  rw [hcl] at h
  simp only [] at h
  split at h
  · exact absurd h (by simp)
  · rename_i st₁ ne hemit₁
    split at h
    · exact absurd h (by simp)
    · rename_i st₂ ve hemit₂
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1; subst h2
      refine ⟨ne, ve, rfl, ?_, ?_⟩
      · have hst₂ := (emitSidecar_eq st₁ .headerValue value st₂ ve hemit₂).1
        have hib₁ : st₁.InBounds ne := by
          have hst₁ := (emitSidecar_eq st .headerName name st₁ ne hemit₁).1
          have hbnd := emitSidecar_inBounds st .headerName name st₁ ne hemit₁
          rw [hst₁, Store.inBounds_pushEntry]
          exact hbnd
        rw [hst₂, resolve_pushEntry, resolve_appendSidecar _ _ _ hib₁]
        exact resolve_emitSidecar st .headerName name st₁ ne hemit₁
      · exact resolve_emitSidecar st₁ .headerValue value st₂ ve hemit₂

/-! ## Non-Huffman string literals decode to their exact bytes -/

/-- A 7-bit length prefix `< 127` decodes to exactly that length, consuming no
continuation bytes. -/
theorem decPrefixInt7_ofNat (len : Nat) (rest : Bytes) (h : len < 127) :
    decPrefixInt 7 (UInt8.ofNat len) rest = some (len, 0) := by
  unfold decPrefixInt
  have ht : (UInt8.ofNat len).toNat = len := UInt8.toNat_ofNat_of_lt (show len < 256 by omega)
  have hp : (2:Nat) ^ 7 = 128 := by decide
  simp only [ht]
  rw [Nat.mod_eq_of_lt (by rw [hp]; omega), if_pos (by rw [hp]; omega)]

/-- One raw (H=0) string literal, whose 7-bit length prefix is `< 127`, decodes
to exactly its bytes `s`, consuming `s.length` bytes past the prefix — for every
Huffman decoder (it is never consulted, the Huffman bit being clear). -/
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
    rw [ht, hp, Nat.div_eq_of_lt (by omega : s.length < 128)]
    decide
  rw [if_neg hhuff, Nat.zero_add]

/-- The whole string-literal read (length-prefix byte + body). -/
theorem readStr7_raw (hd : HuffmanDecoder) (s t : Bytes) (hlen : s.length < 127) :
    readStr hd (UInt8.ofNat s.length :: (s ++ t)) = .ok (s, 1 + s.length) := by
  unfold readStr
  simp only [decStr7_raw hd s t hlen]

/-- The whole string-literal read at end of input (no trailing bytes). -/
theorem readStr7_raw_nil (hd : HuffmanDecoder) (s : Bytes) (hlen : s.length < 127) :
    readStr hd (UInt8.ofNat s.length :: s) = .ok (s, 1 + s.length) := by
  have h := readStr7_raw hd s [] hlen
  rwa [List.append_nil] at h

/-! ## `emitSidecar` / `emitField` succeed when the sidecar has room -/

/-- `emitSidecar` succeeds whenever the append stays inside the offset space. -/
theorem emitSidecar_ok (st : Store) (tag : NameTag) (bs : Bytes)
    (hroom : st.sidecar.size + bs.length < sidecarBaseNat) :
    ∃ st' e, emitSidecar st tag bs = some (st', e) := by
  unfold emitSidecar
  rw [if_neg (by omega)]
  exact ⟨_, _, rfl⟩

/-- **`emitField` succeeds and is correct** (regular-field case) whenever the
name and value together fit the sidecar: it registers a name entry and a value
entry that resolve, in the returned store, to exactly `name` and `value`. -/
theorem emitField_field_ok (st : Store) (name value : Bytes)
    (hcl : classifyName name = none)
    (hroom : st.sidecar.size + name.length + value.length < sidecarBaseNat) :
    ∃ st' ne ve, emitField st name value = .ok (st', .field ⟨ne, ve⟩) ∧
      st'.resolve ne = some name.toArray ∧
      st'.resolve ve = some value.toArray := by
  obtain ⟨st₁, ne, hemit₁⟩ := emitSidecar_ok st .headerName name (by omega)
  -- st₁.sidecar grew by name.length
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
  · -- resolve ne survives the value append
    have hib₁ : st₁.InBounds ne := by
      have hst₁ := (emitSidecar_eq st .headerName name st₁ ne hemit₁).1
      have hbnd := emitSidecar_inBounds st .headerName name st₁ ne hemit₁
      rw [hst₁, Store.inBounds_pushEntry]
      exact hbnd
    rw [(emitSidecar_eq st₁ .headerValue value st₂ ve hemit₂).1,
        resolve_pushEntry, resolve_appendSidecar _ _ _ hib₁]
    exact resolve_emitSidecar st .headerName name st₁ ne hemit₁
  · exact resolve_emitSidecar st₁ .headerValue value st₂ ve hemit₂

/-! ## One literal field with a literal name decodes to its (name, value) -/

/-- **`decodeLiteralField` correctness, literal-name (`idx = 0`), H=0.** The body
`nameLen :: name ++ valueLen :: value` (raw literals, lengths `< 127`) decodes to
one regular field whose two entries resolve to exactly `name` and `value`. -/
theorem decodeLiteralField_lit_sound (hd : HuffmanDecoder) (st : Store)
    (name value : Bytes) (base : Nat)
    (hnl : name.length < 127) (hvl : value.length < 127)
    (hnu : utf8Ok name = true) (hvu : utf8Ok value = true)
    (hcl : classifyName name = none)
    (hroom : st.sidecar.size + name.length + value.length < sidecarBaseNat) :
    ∃ st' ne ve,
      decodeLiteralField hd st 0
          (UInt8.ofNat name.length :: (name ++ UInt8.ofNat value.length :: value)) base
        = .ok (st', .field ⟨ne, ve⟩, base + (1 + name.length) + (1 + value.length)) ∧
      st'.resolve ne = some name.toArray ∧
      st'.resolve ve = some value.toArray := by
  obtain ⟨st', ne, ve, hem, hrn, hrv⟩ := emitField_field_ok st name value hcl hroom
  refine ⟨st', ne, ve, ?_, hrn, hrv⟩
  have hdrop : (UInt8.ofNat name.length :: (name ++ UInt8.ofNat value.length :: value)).drop
      (1 + name.length) = UInt8.ofNat value.length :: value := by
    rw [Nat.add_comm 1 name.length, List.drop_succ_cons, List.drop_left]
  unfold decodeLiteralField
  simp only [reduceIte,
    readStr7_raw hd name (UInt8.ofNat value.length :: value) hnl,
    hnu, hdrop, readStr7_raw_nil hd value hvl, hvu, if_true, hem]

/-! ## One field representation: literal-with-incremental-indexing (§6.2.1) -/

/-- The wire encoding of a literal header field with incremental indexing
(RFC 7541 §6.2.1), literal name (index 0), both name and value as raw (H=0)
string literals with 7-bit length prefixes. First byte `0x40` = pattern `01`
with a 6-bit index of 0. -/
def encLit (name value : Bytes) : Bytes :=
  0x40 :: UInt8.ofNat name.length :: (name ++ UInt8.ofNat value.length :: value)

/-- The 6-bit index prefix of the first byte `0x40` is index 0, no continuation. -/
theorem decPrefixInt6_0x40 (rest : Bytes) : decPrefixInt 6 0x40 rest = some (0, 0) := by
  unfold decPrefixInt
  rfl

/-- **`decodeOneField` correctness for the §6.2.1 representation.** `encLit name
value` decodes to exactly one regular field whose entries resolve to `name` and
`value`, consuming the whole encoding. -/
theorem decodeOneField_literalInc_sound (hd : HuffmanDecoder) (st : Store)
    (name value : Bytes)
    (hnl : name.length < 127) (hvl : value.length < 127)
    (hnu : utf8Ok name = true) (hvu : utf8Ok value = true)
    (hcl : classifyName name = none)
    (hroom : st.sidecar.size + name.length + value.length < sidecarBaseNat) :
    ∃ st' ne ve,
      decodeOneField hd st (encLit name value)
        = .ok (st', .field ⟨ne, ve⟩, 1 + (1 + name.length) + (1 + value.length)) ∧
      st'.resolve ne = some name.toArray ∧
      st'.resolve ve = some value.toArray := by
  obtain ⟨st', ne, ve, hlf, hrn, hrv⟩ :=
    decodeLiteralField_lit_sound hd st name value 1 hnl hvl hnu hvu hcl hroom
  refine ⟨st', ne, ve, ?_, hrn, hrv⟩
  unfold decodeOneField encLit
  have hb : (0x40 : UInt8).toNat = 64 := by decide
  simp only [hb, Nat.reduceLeDiff, reduceIte, decPrefixInt6_0x40, List.drop_zero,
    Nat.add_zero, hlf]

/-! ## A single-field header block -/

/-- When the first field representation consumes the whole block and produces a
regular field, `decodeBlock` yields exactly that one field and no pseudo-headers.
-/
theorem decodeBlock_one_field (hd : HuffmanDecoder) (st st' : Store)
    (b : UInt8) (rest : Bytes) (fl : FieldLine) (n : Nat)
    (hone : decodeOneField hd st (b :: rest) = .ok (st', .field fl, n))
    (hdrop : (b :: rest).drop n = []) :
    decodeBlock hd st (b :: rest) {} [] = .ok (st', {}, [fl]) := by
  rw [decodeBlock]
  split
  · rename_i e heq
    rw [hone] at heq; exact absurd heq (by simp)
  · rename_i st'' out n' heq
    rw [hone] at heq
    simp only [Except.ok.injEq, Prod.mk.injEq] at heq
    obtain ⟨hs, hout, hn⟩ := heq
    subst hs; subst hout; subst hn
    simp only [hdrop]
    rw [decodeBlock]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]

/-! ## The headline correctness theorem -/

/-- The empty store: no wire bytes, no sidecar bytes, no entries. -/
def emptyStore : Store := { main := #[], sidecar := #[], entries := [] }

/-- **HPACK decode correctness (RFC 7541 §6.2.1, literal name, H=0).** Decoding
`encLit name value` — a literal header field with incremental indexing whose
name and value are raw string literals — into the empty store accepts, yields
exactly one regular field `⟨ne, ve⟩` and no pseudo-headers, and the decoded field
RESOLVES to exactly the encoded bytes: `ne` to `name` and `ve` to `value`. The
decode is a faithful inverse of the literal encoding.

This is the MEANING successor to `decodeHeaderBlock_wf`: the `Wf`-only theorem
constrains bounds; this constrains *which bytes*. A degenerate decoder that
registered empty-but-in-bounds spans satisfies `decodeHeaderBlock_wf` but fails
this — for any non-empty `name` it would resolve `ne` to `#[] ≠ name.toArray`
(see `degenerate_decoder_refuted`). Holds for every Huffman-decoder behavior (the
Huffman bit is clear, so the decoder is never consulted). -/
theorem decode_literalInc_sound (hd : HuffmanDecoder) (name value : Bytes)
    (hnl : name.length < 127) (hvl : value.length < 127)
    (hnu : utf8Ok name = true) (hvu : utf8Ok value = true)
    (hcl : classifyName name = none) :
    ∃ (r : Decoded) (ne ve : Entry),
      decodeHeaderBlock hd emptyStore (encLit name value) = .ok r ∧
      r.fields = [⟨ne, ve⟩] ∧ r.pseudo = {} ∧
      r.store.resolve ne = some name.toArray ∧
      r.store.resolve ve = some value.toArray := by
  have hroom : emptyStore.sidecar.size + name.length + value.length < sidecarBaseNat := by
    show 0 + name.length + value.length < sidecarBaseNat
    unfold sidecarBaseNat; omega
  obtain ⟨st', ne, ve, hone, hrn, hrv⟩ :=
    decodeOneField_literalInc_sound hd emptyStore name value hnl hvl hnu hvu hcl hroom
  simp only [encLit] at hone
  have hdrop : (0x40 :: (UInt8.ofNat name.length :: (name ++ UInt8.ofNat value.length :: value))).drop
      (1 + (1 + name.length) + (1 + value.length)) = [] := by
    apply List.drop_eq_nil_of_le
    simp only [List.length_cons, List.length_append]
    omega
  have hblk := decodeBlock_one_field hd emptyStore st' 0x40
    (UInt8.ofNat name.length :: (name ++ UInt8.ofNat value.length :: value))
    ⟨ne, ve⟩ _ hone hdrop
  refine ⟨⟨st', {}, [⟨ne, ve⟩]⟩, ne, ve, ?_, rfl, rfl, hrn, hrv⟩
  unfold decodeHeaderBlock encLit
  rw [hblk]

/-- **The degenerate decoder is refuted.** For any NON-EMPTY name, the decoded
name entry does NOT resolve to the empty string — so a decoder that registered
empty-but-well-formed spans (the trap `decodeHeaderBlock_wf` cannot catch) fails
`decode_literalInc_sound`: it would resolve `ne` to `some #[]`, but this theorem
pins it to `some name.toArray ≠ some #[]`. -/
theorem degenerate_decoder_refuted (hd : HuffmanDecoder) (name value : Bytes)
    (hnl : name.length < 127) (hvl : value.length < 127)
    (hnu : utf8Ok name = true) (hvu : utf8Ok value = true)
    (hcl : classifyName name = none) (hne : name ≠ []) :
    ∃ (r : Decoded) (ne ve : Entry),
      decodeHeaderBlock hd emptyStore (encLit name value) = .ok r ∧
      r.fields = [⟨ne, ve⟩] ∧
      r.store.resolve ne = some name.toArray ∧
      r.store.resolve ne ≠ some #[] := by
  obtain ⟨r, ne, ve, hdec, hf, _hp, hrn, hrv⟩ :=
    decode_literalInc_sound hd name value hnl hvl hnu hvu hcl
  refine ⟨r, ne, ve, hdec, hf, hrn, ?_⟩
  rw [hrn]
  intro hc
  simp only [Option.some.injEq] at hc
  apply hne
  have hs : name.length = 0 := by
    have := congrArg Array.size hc
    simpa using this
  exact List.length_eq_zero.mp hs

end Hpack
end H2
