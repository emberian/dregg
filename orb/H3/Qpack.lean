import H3.Varint
import Arena.Basic
import Arena.Theorems

/-!
# QPACK field-section decoding into the arena store (RFC 9204)

Decodes an encoded field section (the payload of an HTTP/3 HEADERS frame)
*into* the two-arena `Arena.Store`: every decoded name/value byte string is
appended to the **sidecar** arena and registered as a view `Entry` whose
offset carries the sidecar discriminant (`Arena.sidecarBase`). The main
arena is never touched — the caller keeps the wire bytes there.

Scope (deliberate cuts, all decodable-prefix layers included):

* **Prefix integers** (§4.1.1) — full, including the continuation-byte cap
  at 62 bits of shift.
* **String literals** (§4.1.2) — full framing; **Huffman is an axiomatized
  decoder interface** (`HuffmanDecoder`), not an implementation: theorems
  hold uniformly for *every* decoder behavior.
* **Static table** (Appendix A) — the subset of indices 0–31; higher indices
  fail with `Err.staticIndex`.
* **Dynamic table** (§2.3) — explicit out-of-scope stub: any dynamic-table
  reference (indexed post-base, non-static `T` bits, nonzero encoded
  Required Insert Count) fails with `Err.dynamicUnsupported`; there is no
  table state to consult.

Headline theorem — the H3 analogue of the H1 parser's `Wf` discharge:
`decodeFieldSection_wf` / `decodeFieldSection_entries_inBounds`: decoding
into a well-formed store yields a well-formed store, i.e. **every view entry
the decode emits is in-bounds of the arena it addresses** — for every
Huffman-decoder behavior and every input. `decodeFieldSection_main` shows
the main arena is preserved byte-for-byte.
-/

namespace H3
namespace Qpack

open Arena

/-! ## Prefix integers (RFC 9204 §4.1.1) -/

/-- Continuation-byte loop of the prefix integer. `shift` is the current
7-bit shift, `acc` the value so far. A continuation reaching past a shift of
62 is rejected (the 62-bit overflow cap); `none` also covers running out of
bytes. Returns `(value, bytesConsumed)`. -/
def decIntCont : Bytes → Nat → Nat → Option (Nat × Nat)
  | [], _, _ => none
  | b :: rest, shift, acc =>
    let acc' := acc + b.toNat % 128 * 2 ^ shift
    if b.toNat < 128 then some (acc', 1)
    else if 62 < shift + 7 then none
    else
      match decIntCont rest (shift + 7) acc' with
      | some (v, n) => some (v, n + 1)
      | none => none

theorem decIntCont_consumed (bs : Bytes) (shift acc v n : Nat)
    (h : decIntCont bs shift acc = some (v, n)) : 1 ≤ n ∧ n ≤ bs.length := by
  induction bs generalizing shift acc v n with
  | nil => exact absurd h (by simp [decIntCont])
  | cons b rest ih =>
    unfold decIntCont at h
    simp only [] at h
    split at h
    · cases h
      simp
    · split at h
      · exact absurd h (by simp)
      · split at h
        · rename_i v' n' hrec
          cases h
          have := ih _ _ _ _ hrec
          simp only [List.length_cons]
          omega
        · exact absurd h (by simp)

/-- Decode a prefix integer whose low `prefixBits` bits live in `first` and
whose continuation bytes (if any) are at the head of `rest`. Returns
`(value, bytesConsumedFromRest)` — the first byte is the caller's. -/
def decPrefixInt (prefixBits : Nat) (first : UInt8) (rest : Bytes) :
    Option (Nat × Nat) :=
  let maxPrefix := 2 ^ prefixBits - 1
  let v := first.toNat % 2 ^ prefixBits
  if v < maxPrefix then some (v, 0)
  else decIntCont rest 0 maxPrefix

theorem decPrefixInt_consumed (p : Nat) (first : UInt8) (rest : Bytes)
    (v n : Nat) (h : decPrefixInt p first rest = some (v, n)) :
    n ≤ rest.length := by
  unfold decPrefixInt at h
  simp only [] at h
  split at h
  · cases h; omega
  · exact (decIntCont_consumed rest 0 _ v n h).2

/-! ## String literals (§4.1.2) and the Huffman interface -/

/-- **The axiomatized Huffman decoder interface** (RFC 9204 §4.1.2; the code
itself is the HPACK table of RFC 7541 Appendix B). Deliberately *not*
implemented: the decoder enters the model as an uninterpreted total
function — the same convention as the abstract codec fields of the
connection-FSM model — so every theorem in this file holds uniformly over
every decoder behavior. `none` means the coded bit string is invalid
(e.g. bad EOS padding). -/
structure HuffmanDecoder where
  decode : Bytes → Option Bytes

/-- Typed error classes of the field-section decode. -/
inductive Err where
  /-- Ran off the end of the field section (or a malformed prefix integer). -/
  | truncated
  /-- A dynamic-table reference: the dynamic table is the explicit
  out-of-scope stub — no table state exists to resolve it. -/
  | dynamicUnsupported
  /-- Static-table index outside the modeled subset. -/
  | staticIndex
  /-- The Huffman decoder rejected a coded string. -/
  | huffman
  /-- A decoded name or value is not valid UTF-8. -/
  | nonUtf8
  /-- The sidecar arena's `2^31` offset space would be exhausted. -/
  | tooLarge
deriving Repr, DecidableEq

/-- Decode one string literal: a length prefix integer of `prefixBits` bits
in `first` (the Huffman flag is the bit just above the prefix), then the
string bytes at the head of `rest` after any continuation bytes. Returns the
(possibly Huffman-decoded) bytes and the count consumed from `rest`. -/
def decStr (hd : HuffmanDecoder) (prefixBits : Nat) (first : UInt8)
    (rest : Bytes) : Except Err (Bytes × Nat) :=
  match decPrefixInt prefixBits first rest with
  | none => .error .truncated
  | some (len, n) =>
    let body := (rest.drop n).take len
    if body.length < len then .error .truncated
    else if first.toNat / 2 ^ prefixBits % 2 = 1 then
      match hd.decode body with
      | some out => .ok (out, n + len)
      | none => .error .huffman
    else .ok (body, n + len)

theorem decStr_consumed (hd : HuffmanDecoder) (p : Nat) (first : UInt8)
    (rest : Bytes) (out : Bytes) (n : Nat)
    (h : decStr hd p first rest = .ok (out, n)) : n ≤ rest.length := by
  unfold decStr at h
  split at h
  · exact absurd h (by simp)
  · rename_i len m hlen
    have hm := decPrefixInt_consumed p first rest len m hlen
    simp only [] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hguard
      simp only [List.length_take, List.length_drop] at hguard
      split at h
      · split at h
        · cases h; omega
        · exact absurd h (by simp)
      · cases h; omega

/-- Executable UTF-8 validity check (the dynamic discharge of the model's
explicit UTF-8 hypothesis, as in the H1 parser). -/
def utf8Ok (bs : Bytes) : Bool := String.validateUTF8 (ByteArray.mk bs.toArray)

/-! ## The static table subset (RFC 9204 Appendix A, indices 0–31) -/

/-- RFC 9204 Appendix A, indices 0–31 (0-based, as in the RFC). Indices
32–98 are a deliberate scope cut. -/
def staticTable : List (String × String) := [
  (":authority", ""), (":path", "/"), ("age", "0"),
  ("content-disposition", ""), ("content-length", "0"), ("cookie", ""),
  ("date", ""), ("etag", ""), ("if-modified-since", ""),
  ("if-none-match", ""), ("last-modified", ""), ("link", ""),
  ("location", ""), ("referer", ""), ("set-cookie", ""),
  (":method", "CONNECT"), (":method", "DELETE"), (":method", "GET"),
  (":method", "HEAD"), (":method", "OPTIONS"), (":method", "POST"),
  (":method", "PUT"), (":scheme", "http"), (":scheme", "https"),
  (":status", "103"), (":status", "200"), (":status", "304"),
  (":status", "404"), (":status", "503"), ("accept", "*/*"),
  ("accept", "application/dns-message"),
  ("accept-encoding", "gzip, deflate, br")]

def staticEntry (i : Nat) : Option (String × String) := staticTable[i]?

/-- UTF-8 bytes of a string (static-table materialization). -/
def strBytes (s : String) : Bytes := s.toUTF8.toList

/-! ## Emitting into the store -/

/-- Append `bs` to the sidecar arena and register a view entry addressing
exactly the appended range (the offset carries the sidecar discriminant).
`none` iff the append would exhaust the sidecar's `2^31` offset space —
the check that keeps every emitted offset/length exact in `UInt32`. -/
def emitSidecar (st : Store) (tag : NameTag) (bs : Bytes) :
    Option (Store × Entry) :=
  if sidecarBaseNat ≤ st.sidecar.size + bs.length then none
  else
    let e : Entry :=
      { tag := tag
        off := UInt32.ofNat (sidecarBaseNat + st.sidecar.size)
        len := UInt32.ofNat bs.length }
    some ((st.appendSidecar bs.toArray).pushEntry e, e)

theorem emitSidecar_eq (st : Store) (tag : NameTag) (bs : Bytes)
    (st' : Store) (e : Entry) (h : emitSidecar st tag bs = some (st', e)) :
    st' = (st.appendSidecar bs.toArray).pushEntry e ∧
      st.sidecar.size + bs.length < sidecarBaseNat := by
  unfold emitSidecar at h
  split at h
  · exact absurd h (by simp)
  · rename_i hlt
    cases h
    exact ⟨rfl, by omega⟩

/-- The emitted entry is in-bounds **by construction**: the size guard keeps
the offset arithmetic exact, the offset lands in the sidecar address space,
and the referenced range is exactly the appended block. -/
theorem emitSidecar_inBounds (st : Store) (tag : NameTag) (bs : Bytes)
    (st' : Store) (e : Entry) (h : emitSidecar st tag bs = some (st', e)) :
    (st.appendSidecar bs.toArray).InBounds e := by
  unfold emitSidecar at h
  split at h
  · exact absurd h (by simp)
  · rename_i hlt
    injection h with h
    injection h with h₁ h₂
    subst h₂
    have hsz : st.sidecar.size + bs.length < sidecarBaseNat := by omega
    have hoff : (UInt32.ofNat (sidecarBaseNat + st.sidecar.size)).toNat
        = sidecarBaseNat + st.sidecar.size := by
      show (sidecarBaseNat + st.sidecar.size) % 2 ^ 32
          = sidecarBaseNat + st.sidecar.size
      unfold sidecarBaseNat at *
      omega
    have hlen : (UInt32.ofNat bs.length).toNat = bs.length := by
      show bs.length % 2 ^ 32 = bs.length
      unfold sidecarBaseNat at hsz
      omega
    have hside : Entry.inSidecar
        { tag := tag
          off := UInt32.ofNat (sidecarBaseNat + st.sidecar.size)
          len := UInt32.ofNat bs.length } = true := by
      unfold Entry.inSidecar
      simp only [hoff, decide_eq_true_eq]
      unfold isSidecarAddr
      omega
    unfold Store.InBounds Store.arenaOf Entry.physOff
    simp only [hside, if_true, hoff, hlen]
    unfold Store.appendSidecar
    simp only [Array.size_append]
    have hta : bs.toArray.size = bs.length := rfl
    omega

/-- **Wf preservation for one emit**: pushing the constructed entry after the
sidecar append preserves store well-formedness. -/
theorem emitSidecar_wf (st : Store) (tag : NameTag) (bs : Bytes)
    (st' : Store) (e : Entry) (hwf : st.Wf)
    (h : emitSidecar st tag bs = some (st', e)) : st'.Wf := by
  have heq := (emitSidecar_eq st tag bs st' e h).1
  have hib := emitSidecar_inBounds st tag bs st' e h
  rw [heq]
  exact Store.wf_pushEntry _ (Store.wf_appendSidecar st hwf _) hib

/-- Emitting never touches the main arena. -/
theorem emitSidecar_main (st : Store) (tag : NameTag) (bs : Bytes)
    (st' : Store) (e : Entry) (h : emitSidecar st tag bs = some (st', e)) :
    st'.main = st.main := by
  rw [(emitSidecar_eq st tag bs st' e h).1]
  rfl

/-! ## Field lines -/

/-- A decoded (non-pseudo) field: name and value view entries. -/
structure FieldLine where
  name : Entry
  value : Entry
deriving Repr

/-- The four request pseudo-headers the decode routes into dedicated fields;
other pseudo names (e.g. `:status`) fall through as regular fields — the RFC
leaves that routing to the consumer. -/
inductive PseudoKind where
  | method | path | scheme | authority
deriving Repr, DecidableEq

/-- Pseudo-header values: the name is implied by the field, so only the
value entry is registered. -/
structure Pseudo where
  method : Option Entry := none
  path : Option Entry := none
  scheme : Option Entry := none
  authority : Option Entry := none
deriving Repr

def Pseudo.set (p : Pseudo) (k : PseudoKind) (e : Entry) : Pseudo :=
  match k with
  | .method => { p with method := some e }
  | .path => { p with path := some e }
  | .scheme => { p with scheme := some e }
  | .authority => { p with authority := some e }

/-- What one decoded field line contributes. -/
inductive LineOut where
  | pseudo (k : PseudoKind) (value : Entry)
  | field (fl : FieldLine)

def classifyName (name : Bytes) : Option PseudoKind :=
  if name = strBytes ":method" then some .method
  else if name = strBytes ":path" then some .path
  else if name = strBytes ":scheme" then some .scheme
  else if name = strBytes ":authority" then some .authority
  else none

/-- Emit one decoded field into the store: pseudo-headers register only a
value entry; regular fields register a name entry then a value entry. -/
def emitField (st : Store) (name value : Bytes) :
    Except Err (Store × LineOut) :=
  match classifyName name with
  | some k =>
    match emitSidecar st .headerValue value with
    | some (st', ve) => .ok (st', .pseudo k ve)
    | none => .error .tooLarge
  | none =>
    match emitSidecar st .headerName name with
    | none => .error .tooLarge
    | some (st₁, ne) =>
      match emitSidecar st₁ .headerValue value with
      | none => .error .tooLarge
      | some (st₂, ve) => .ok (st₂, .field ⟨ne, ve⟩)

theorem emitField_wf (st : Store) (name value : Bytes) (st' : Store)
    (out : LineOut) (hwf : st.Wf)
    (h : emitField st name value = .ok (st', out)) : st'.Wf := by
  unfold emitField at h
  split at h
  · split at h
    · rename_i hemit
      cases h
      exact emitSidecar_wf _ _ _ _ _ hwf hemit
    · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · rename_i st₁ ne hemit₁
      split at h
      · exact absurd h (by simp)
      · rename_i st₂ ve hemit₂
        cases h
        exact emitSidecar_wf _ _ _ _ _
          (emitSidecar_wf _ _ _ _ _ hwf hemit₁) hemit₂

theorem emitField_main (st : Store) (name value : Bytes) (st' : Store)
    (out : LineOut) (h : emitField st name value = .ok (st', out)) :
    st'.main = st.main := by
  unfold emitField at h
  split at h
  · split at h
    · rename_i hemit
      cases h
      exact emitSidecar_main _ _ _ _ _ hemit
    · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · rename_i st₁ ne hemit₁
      split at h
      · exact absurd h (by simp)
      · rename_i st₂ ve hemit₂
        cases h
        rw [emitSidecar_main _ _ _ _ _ hemit₂,
          emitSidecar_main _ _ _ _ _ hemit₁]

/-! ## Decoding one field line (§4.5) -/

/-- Decode one field-line representation from the head of `bs`.

Taxonomy by the top bits of the first byte (RFC 9204 §4.5.2–§4.5.6):

* `1 T idx(6)` — indexed field line; `T=1` static, `T=0` dynamic (stub).
* `01 N T idx(4)` — literal with name reference; `T=1` static name,
  `T=0` dynamic (stub).
* `001 N H len(3)` — literal with literal name.
* `0001 idx(4)` — indexed, post-base (dynamic; stub).
* `0000 N idx(3)` — literal with post-base name reference (dynamic; stub).

Returns the grown store, the line's contribution, and bytes consumed. -/
def decodeOneLine (hd : HuffmanDecoder) (st : Store) (bs : Bytes) :
    Except Err (Store × LineOut × Nat) :=
  match bs with
  | [] => .error .truncated
  | b :: rest =>
    if 0x80 ≤ b.toNat then
      -- Indexed field line (§4.5.2)
      if 0x40 ≤ b.toNat % 0x80 then
        match decPrefixInt 6 b rest with
        | none => .error .truncated
        | some (idx, n) =>
          match staticEntry idx with
          | none => .error .staticIndex
          | some (name, value) =>
            match emitField st (strBytes name) (strBytes value) with
            | .error e => .error e
            | .ok (st', out) => .ok (st', out, 1 + n)
      else .error .dynamicUnsupported
    else if 0x40 ≤ b.toNat then
      -- Literal field line with name reference (§4.5.4)
      if 0x10 ≤ b.toNat % 0x20 then
        match decPrefixInt 4 b rest with
        | none => .error .truncated
        | some (idx, n) =>
          match staticEntry idx with
          | none => .error .staticIndex
          | some (name, _) =>
            match rest.drop n with
            | [] => .error .truncated
            | vb :: vrest =>
              match decStr hd 7 vb vrest with
              | .error e => .error e
              | .ok (value, m) =>
                if utf8Ok value then
                  match emitField st (strBytes name) value with
                  | .error e => .error e
                  | .ok (st', out) => .ok (st', out, 1 + n + 1 + m)
                else .error .nonUtf8
      else .error .dynamicUnsupported
    else if 0x20 ≤ b.toNat then
      -- Literal field line with literal name (§4.5.6)
      match decStr hd 3 b rest with
      | .error e => .error e
      | .ok (name, n) =>
        if utf8Ok name then
          match rest.drop n with
          | [] => .error .truncated
          | vb :: vrest =>
            match decStr hd 7 vb vrest with
            | .error e => .error e
            | .ok (value, m) =>
              if utf8Ok value then
                match emitField st name value with
                | .error e => .error e
                | .ok (st', out) => .ok (st', out, 1 + n + 1 + m)
              else .error .nonUtf8
        else .error .nonUtf8
    else
      -- §4.5.3 indexed post-base / §4.5.5 literal with post-base name
      -- reference: dynamic-table territory, out of scope.
      .error .dynamicUnsupported

/-- **Progress + boundedness** for one field line: at least one byte, never
more than the input. -/
theorem decodeOneLine_consumed (hd : HuffmanDecoder) (st : Store)
    (bs : Bytes) (st' : Store) (out : LineOut) (n : Nat)
    (h : decodeOneLine hd st bs = .ok (st', out, n)) :
    1 ≤ n ∧ n ≤ bs.length := by
  unfold decodeOneLine at h
  split at h
  · exact absurd h (by simp)
  · rename_i b rest
    split at h
    · split at h
      · split at h
        · exact absurd h (by simp)
        · rename_i idx n₁ hpi
          have hn₁ := decPrefixInt_consumed 6 b rest idx n₁ hpi
          split at h
          · exact absurd h (by simp)
          · split at h
            · exact absurd h (by simp)
            · cases h
              simp only [List.length_cons]
              omega
      · exact absurd h (by simp)
    · split at h
      · split at h
        · split at h
          · exact absurd h (by simp)
          · rename_i idx n₁ hpi
            have hn₁ := decPrefixInt_consumed 4 b rest idx n₁ hpi
            split at h
            · exact absurd h (by simp)
            · split at h
              · exact absurd h (by simp)
              · rename_i vb vrest hdrop
                have hlen : rest.length - n₁ = vrest.length + 1 := by
                  have := congrArg List.length hdrop
                  simp only [List.length_drop, List.length_cons] at this
                  omega
                split at h
                · exact absurd h (by simp)
                · rename_i value m hstr
                  have hm := decStr_consumed hd 7 vb vrest value m hstr
                  split at h
                  · split at h
                    · exact absurd h (by simp)
                    · cases h
                      simp only [List.length_cons]
                      omega
                  · exact absurd h (by simp)
        · exact absurd h (by simp)
      · split at h
        · split at h
          · exact absurd h (by simp)
          · rename_i name n₁ hstr₁
            have hn₁ := decStr_consumed hd 3 b rest name n₁ hstr₁
            split at h
            · split at h
              · exact absurd h (by simp)
              · rename_i vb vrest hdrop
                have hlen : rest.length - n₁ = vrest.length + 1 := by
                  have := congrArg List.length hdrop
                  simp only [List.length_drop, List.length_cons] at this
                  omega
                split at h
                · exact absurd h (by simp)
                · rename_i value m hstr₂
                  have hm := decStr_consumed hd 7 vb vrest value m hstr₂
                  split at h
                  · split at h
                    · exact absurd h (by simp)
                    · cases h
                      simp only [List.length_cons]
                      omega
                  · exact absurd h (by simp)
            · exact absurd h (by simp)
        · exact absurd h (by simp)

/-- One field line preserves store well-formedness. -/
theorem decodeOneLine_wf (hd : HuffmanDecoder) (st : Store) (bs : Bytes)
    (st' : Store) (out : LineOut) (n : Nat) (hwf : st.Wf)
    (h : decodeOneLine hd st bs = .ok (st', out, n)) : st'.Wf := by
  unfold decodeOneLine at h
  repeat' split at h
  all_goals cases h
  all_goals exact emitField_wf _ _ _ _ _ hwf (by assumption)

/-- One field line never touches the main arena. -/
theorem decodeOneLine_main (hd : HuffmanDecoder) (st : Store) (bs : Bytes)
    (st' : Store) (out : LineOut) (n : Nat)
    (h : decodeOneLine hd st bs = .ok (st', out, n)) :
    st'.main = st.main := by
  unfold decodeOneLine at h
  repeat' split at h
  all_goals cases h
  all_goals exact emitField_main _ _ _ _ _ (by assumption)

/-! ## The field-line loop and the section prefix (§4.5.1) -/

set_option linter.unusedVariables false in
/-- Decode all field lines of a section. Termination is
`decodeOneLine_consumed` (every line eats at least one byte; the
discriminant name `h` is used only by `decreasing_by`). -/
def decodeLines (hd : HuffmanDecoder) (st : Store) (bs : Bytes)
    (pseudo : Pseudo) (acc : List FieldLine) :
    Except Err (Store × Pseudo × List FieldLine) :=
  match bs with
  | [] => .ok (st, pseudo, acc.reverse)
  | b :: rest =>
    match h : decodeOneLine hd st (b :: rest) with
    | .error e => .error e
    | .ok (st', out, n) =>
      decodeLines hd st' ((b :: rest).drop n)
        (match out with
         | .pseudo k ve => pseudo.set k ve
         | .field _ => pseudo)
        (match out with
         | .pseudo _ _ => acc
         | .field fl => fl :: acc)
termination_by bs.length
decreasing_by
  all_goals
    have := decodeOneLine_consumed hd st (b :: rest) st' out n h
    simp only [List.length_drop, List.length_cons]
    omega

/-- The loop preserves well-formedness. -/
theorem decodeLines_wf (hd : HuffmanDecoder) (st : Store) (bs : Bytes)
    (pseudo : Pseudo) (acc : List FieldLine) :
    ∀ r : Store × Pseudo × List FieldLine, st.Wf →
      decodeLines hd st bs pseudo acc = .ok r → r.1.Wf := by
  induction st, bs, pseudo, acc using decodeLines.induct hd with
  | case1 st pseudo acc =>
    intro r hwf h
    simp only [decodeLines] at h
    cases h
    exact hwf
  | case2 st pseudo acc b rest e hline =>
    intro r hwf h
    simp only [decodeLines] at h
    split at h
    · cases h
    · rename_i st' out n heq
      rw [hline] at heq
      cases heq
  | case3 st pseudo acc b rest st' out n hline ih =>
    intro r hwf h
    simp only [decodeLines] at h
    split at h
    · rename_i e heq
      rw [hline] at heq
      cases heq
    · rename_i st'' out'' n'' heq
      rw [hline] at heq
      cases heq
      exact ih r (decodeOneLine_wf _ _ _ _ _ _ hwf hline) h

/-- The loop never touches the main arena. -/
theorem decodeLines_main (hd : HuffmanDecoder) (st : Store) (bs : Bytes)
    (pseudo : Pseudo) (acc : List FieldLine) :
    ∀ r : Store × Pseudo × List FieldLine,
      decodeLines hd st bs pseudo acc = .ok r → r.1.main = st.main := by
  induction st, bs, pseudo, acc using decodeLines.induct hd with
  | case1 st pseudo acc =>
    intro r h
    simp only [decodeLines] at h
    cases h
    rfl
  | case2 st pseudo acc b rest e hline =>
    intro r h
    simp only [decodeLines] at h
    split at h
    · cases h
    · rename_i st' out n heq
      rw [hline] at heq
      cases heq
  | case3 st pseudo acc b rest st' out n hline ih =>
    intro r h
    simp only [decodeLines] at h
    split at h
    · rename_i e heq
      rw [hline] at heq
      cases heq
    · rename_i st'' out'' n'' heq
      rw [hline] at heq
      cases heq
      rw [ih r h, decodeOneLine_main _ _ _ _ _ _ hline]

/-- A decoded field section: the grown store, the routed pseudo-headers,
and the regular fields in wire order. -/
structure Decoded where
  store : Store
  pseudo : Pseudo
  fields : List FieldLine

/-- Decode an encoded field section (§4.5.1) into the store.

The section prefix is the encoded Required Insert Count (8-bit prefix) and
the Delta Base (7-bit prefix + sign). With the dynamic table stubbed out,
only `encodedRic = 0` is decodable (RFC 9204 §4.5.1.1: an encoder that makes
no dynamic references encodes 0); the delta base is decoded and discarded. -/
def decodeFieldSection (hd : HuffmanDecoder) (st : Store) (bs : Bytes) :
    Except Err Decoded :=
  match bs with
  | [] => .error .truncated
  | b0 :: r0 =>
    match decPrefixInt 8 b0 r0 with
    | none => .error .truncated
    | some (encRic, n0) =>
      if encRic ≠ 0 then .error .dynamicUnsupported
      else
        match r0.drop n0 with
        | [] => .error .truncated
        | b1 :: r1 =>
          match decPrefixInt 7 b1 r1 with
          | none => .error .truncated
          | some (_deltaBase, n1) =>
            match decodeLines hd st (r1.drop n1) {} [] with
            | .error e => .error e
            | .ok (st', pseudo, fields) => .ok ⟨st', pseudo, fields⟩

/-- **The headline theorem — Wf preservation** (the H3 analogue of the H1
parser's `Wf` discharge): decoding a field section into a well-formed store
yields a well-formed store, for every Huffman-decoder behavior and every
input. -/
theorem decodeFieldSection_wf (hd : HuffmanDecoder) (st : Store) (bs : Bytes)
    (r : Decoded) (hwf : st.Wf) (h : decodeFieldSection hd st bs = .ok r) :
    r.store.Wf := by
  unfold decodeFieldSection at h
  repeat' split at h
  all_goals cases h
  all_goals exact decodeLines_wf _ _ _ _ _ _ hwf (by assumption)

/-- Corollary, in emitted-entry form: **every view entry of the decoded
store — the emitted ones included — is in-bounds of the arena it
addresses.** -/
theorem decodeFieldSection_entries_inBounds (hd : HuffmanDecoder)
    (st : Store) (bs : Bytes) (r : Decoded) (hwf : st.Wf)
    (h : decodeFieldSection hd st bs = .ok r) :
    ∀ e ∈ r.store.entries, r.store.InBounds e :=
  decodeFieldSection_wf hd st bs r hwf h

/-- The decode only appends to the sidecar: the main arena — the wire
bytes — is preserved byte-for-byte. -/
theorem decodeFieldSection_main (hd : HuffmanDecoder) (st : Store)
    (bs : Bytes) (r : Decoded) (h : decodeFieldSection hd st bs = .ok r) :
    r.store.main = st.main := by
  unfold decodeFieldSection at h
  repeat' split at h
  all_goals cases h
  all_goals exact decodeLines_main _ _ _ _ _ _ (by assumption)

/-! ## Wire vectors, checker-verified at build time (through `#guard`:
well-founded definitions do not kernel-reduce). All with the empty store and
a Huffman decoder that rejects everything — none of these vectors sets the
Huffman bit, so the decoder is never consulted. -/

private def rejectAllHuffman : HuffmanDecoder := ⟨fun _ => none⟩

private def emptyStore : Store := { main := #[], sidecar := #[], entries := [] }

/-- Section prefix `00 00`, then `0xd1` = indexed static 17 (`:method: GET`):
routed to the pseudo record, value entry emitted, store well-formed. -/
private def vecIndexedStatic : Bool :=
  match decodeFieldSection rejectAllHuffman emptyStore [0x00, 0x00, 0xd1] with
  | .ok r => r.pseudo.method.isSome && r.fields.isEmpty && r.store.wfCheck
  | .error _ => false
#guard vecIndexedStatic

/-- `0x51` = literal with static name reference, index 1 (`:path`), then the
value literal `/idx` (raw, 7-bit length prefix). -/
private def vecPathLiteral : Bool :=
  match decodeFieldSection rejectAllHuffman emptyStore
      ([0x00, 0x00, 0x51, 0x04] ++ strBytes "/idx") with
  | .ok r => r.pseudo.path.isSome && r.fields.isEmpty && r.store.wfCheck
  | .error _ => false
#guard vecPathLiteral

/-- `0x27 0x00` = literal field line with literal name, name length 7 (the
full 3-bit prefix plus a zero continuation byte), name `x-seven`, then value
literal `ok`: one regular field, name + value entries, store well-formed. -/
private def vecLiteralLiteral : Bool :=
  match decodeFieldSection rejectAllHuffman emptyStore
      ([0x00, 0x00, 0x27, 0x00] ++ strBytes "x-seven" ++
        [0x02] ++ strBytes "ok") with
  | .ok r =>
    r.fields.length == 1 && r.store.entries.length == 2 && r.store.wfCheck
  | .error _ => false
#guard vecLiteralLiteral

/-- `0x80` = indexed field line, dynamic table: must hit the explicit stub. -/
private def vecDynamicStub : Bool :=
  match decodeFieldSection rejectAllHuffman emptyStore [0x00, 0x00, 0x80] with
  | .error .dynamicUnsupported => true
  | _ => false
#guard vecDynamicStub

/-- A nonzero encoded Required Insert Count needs dynamic-table state. -/
private def vecRicStub : Bool :=
  match decodeFieldSection rejectAllHuffman emptyStore [0x01, 0x00, 0xd1] with
  | .error .dynamicUnsupported => true
  | _ => false
#guard vecRicStub

end Qpack
end H3
