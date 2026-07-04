import H2.Basic
import Arena.Basic
import Arena.Theorems

/-!
# HPACK header-block decoding into the arena store (RFC 7541)

Decodes an HPACK-encoded header block (the payload of an HTTP/2 HEADERS or
CONTINUATION frame) *into* the two-arena `Arena.Store`: every decoded
name/value byte string is appended to the **sidecar** arena and registered as a
view `Entry` whose offset carries the sidecar discriminant
(`Arena.sidecarBase`). The main arena is never touched — the caller keeps the
wire bytes there. This is the H2 realization of the same Rank-1 arena model the
QPACK decoder uses; the two decoders share the committed `Arena.Store` theory
but each derives its own audited emit primitive, so the protocol libraries stay
independent.

Scope (deliberate cuts, all decodable-prefix layers included):

* **Prefix integers** (§5.1) — full, including the continuation-byte overflow
  cap.
* **String literals** (§5.2) — full framing; **Huffman is an axiomatized
  decoder interface** (`HuffmanDecoder`), not an implementation: theorems hold
  uniformly for *every* decoder behavior.
* **Static table** (Appendix A) — the subset of indices 1–32 (1-based, as in
  the RFC; index 0 is the invalid sentinel); indices 33–61 fail with
  `Err.staticIndex` (a modeled-subset cut).
* **Dynamic table** (§2.3) — explicit out-of-scope stub: an indexed reference
  into the dynamic table (index ≥ 62), a dynamic-table size update (§6.3), and
  the incremental-indexing insertion side effect (§6.2.1) are all treated as
  the stub — an index ≥ 62 fails with `Err.dynamicUnsupported`, a size update
  fails with `Err.dynamicUnsupported`, and incremental indexing decodes the
  field but performs no table insertion. There is no table state to consult.

Headline theorem — the H2 analogue of the QPACK `Wf` discharge:
`decodeHeaderBlock_wf` / `decodeHeaderBlock_entries_inBounds`: decoding into a
well-formed store yields a well-formed store, i.e. **every view entry the
decode emits is in-bounds of the arena it addresses** — for every Huffman
-decoder behavior and every input. `decodeHeaderBlock_main` shows the main
arena is preserved byte-for-byte.
-/

namespace H2
namespace Hpack

open Arena

/-! ## Prefix integers (RFC 7541 §5.1) -/

/-- Continuation-byte loop of the prefix integer. `shift` is the current 7-bit
shift, `acc` the value so far. A continuation reaching past a shift of 28 is
rejected (the overflow cap, RFC 7541 §5.1: the receiver bounds the number of
continuation bytes); `none` also covers running out of bytes. Returns
`(value, bytesConsumed)`. -/
def decIntCont : Bytes → Nat → Nat → Option (Nat × Nat)
  | [], _, _ => none
  | b :: rest, shift, acc =>
    let acc' := acc + b.toNat % 128 * 2 ^ shift
    if b.toNat < 128 then some (acc', 1)
    else if 28 < shift + 7 then none
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

/-! ## String literals (§5.2) and the Huffman interface -/

/-- **The axiomatized Huffman decoder interface** (RFC 7541 §5.2; the code
itself is the HPACK table of Appendix B). Deliberately *not* implemented: the
decoder enters the model as an uninterpreted total function, so every theorem
in this file holds uniformly over every decoder behavior. `none` means the
coded bit string is invalid (e.g. bad EOS padding). -/
structure HuffmanDecoder where
  decode : Bytes → Option Bytes

/-- Typed error classes of the header-block decode. -/
inductive Err where
  /-- Ran off the end of the header block (or a malformed prefix integer). -/
  | truncated
  /-- A dynamic-table reference or size update: the dynamic table is the
  explicit out-of-scope stub — no table state exists to resolve it. -/
  | dynamicUnsupported
  /-- Static-table index outside the modeled subset (33–61). -/
  | staticIndex
  /-- Static-table index 0, which is invalid (RFC 7541 §6.1). -/
  | invalidIndex
  /-- The Huffman decoder rejected a coded string. -/
  | huffman
  /-- A decoded name or value is not valid UTF-8. -/
  | nonUtf8
  /-- The sidecar arena's `2^31` offset space would be exhausted. -/
  | tooLarge
deriving Repr, DecidableEq

/-- Decode one string literal: a length prefix integer of `prefixBits` bits in
`first` (the Huffman flag is the bit just above the prefix), then the string
bytes at the head of `rest` after any continuation bytes. Returns the
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

/-- Read a whole string literal (its length-prefix first byte plus body) from
the head of `bs`. HPACK string literals always use a 7-bit length prefix with
the Huffman flag in bit 7. Returns the decoded bytes and the total count
consumed from `bs` (including the first byte). -/
def readStr (hd : HuffmanDecoder) (bs : Bytes) : Except Err (Bytes × Nat) :=
  match bs with
  | [] => .error .truncated
  | b :: rest =>
    match decStr hd 7 b rest with
    | .error e => .error e
    | .ok (s, m) => .ok (s, 1 + m)

theorem readStr_consumed (hd : HuffmanDecoder) (bs : Bytes) (s : Bytes) (n : Nat)
    (h : readStr hd bs = .ok (s, n)) : 1 ≤ n ∧ n ≤ bs.length := by
  unfold readStr at h
  split at h
  · exact absurd h (by simp)
  · rename_i b rest
    split at h
    · exact absurd h (by simp)
    · rename_i s' m hstr
      have hm := decStr_consumed hd 7 b rest s' m hstr
      cases h
      simp only [List.length_cons]
      omega

/-- Executable UTF-8 validity check (the dynamic discharge of the model's
explicit UTF-8 hypothesis, as in the H1 parser and QPACK). -/
def utf8Ok (bs : Bytes) : Bool := String.validateUTF8 (ByteArray.mk bs.toArray)

/-! ## The static table subset (RFC 7541 Appendix A, indices 1–32) -/

/-- RFC 7541 Appendix A, indices 0–32 (1-based, as in the RFC; index 0 is the
unused sentinel). Indices 33–61 are a deliberate scope cut. -/
def staticTable : List (String × String) := [
  ("", ""),                                             -- 0 (unused)
  (":authority", ""), (":method", "GET"),               -- 1, 2
  (":method", "POST"), (":path", "/"),                  -- 3, 4
  (":path", "/index.html"), (":scheme", "http"),        -- 5, 6
  (":scheme", "https"), (":status", "200"),             -- 7, 8
  (":status", "204"), (":status", "206"),               -- 9, 10
  (":status", "304"), (":status", "400"),               -- 11, 12
  (":status", "404"), (":status", "500"),               -- 13, 14
  ("accept-charset", ""), ("accept-encoding", "gzip, deflate"), -- 15, 16
  ("accept-language", ""), ("accept-ranges", ""),       -- 17, 18
  ("accept", ""), ("access-control-allow-origin", ""),  -- 19, 20
  ("age", ""), ("allow", ""),                           -- 21, 22
  ("authorization", ""), ("cache-control", ""),         -- 23, 24
  ("content-disposition", ""), ("content-encoding", ""),-- 25, 26
  ("content-language", ""), ("content-length", ""),     -- 27, 28
  ("content-location", ""), ("content-range", ""),      -- 29, 30
  ("content-type", ""), ("cookie", "")]                 -- 31, 32

/-- Resolve a 1-based static-table index in the modeled subset. Index 0 and
indices ≥ 33 fall outside the modeled table (`none`). -/
def staticEntry (i : Nat) : Option (String × String) :=
  if i = 0 then none else staticTable[i]?

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

/-- Pseudo-header values: the name is implied by the field, so only the value
entry is registered. -/
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

/-- What one decoded field contributes. -/
inductive LineOut where
  | pseudo (k : PseudoKind) (value : Entry)
  | field (fl : FieldLine)

def classifyName (name : Bytes) : Option PseudoKind :=
  if name = strBytes ":method" then some .method
  else if name = strBytes ":path" then some .path
  else if name = strBytes ":scheme" then some .scheme
  else if name = strBytes ":authority" then some .authority
  else none

/-- Emit one decoded field into the store: pseudo-headers register only a value
entry; regular fields register a name entry then a value entry. -/
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

/-! ## Decoding a literal field (shared by §6.2.1/§6.2.2/§6.2.3) -/

/-- Decode a literal header field from `body` (the bytes following the first
byte and its index prefix), given the resolved index `idx` and the running
`base` count (first byte + index-prefix continuation bytes). If `idx = 0` the
name is a literal string; otherwise it is a static-table name reference.
The value is always a literal string. Returns the grown store, the field's
contribution, and the total bytes consumed (from the original input). -/
def decodeLiteralField (hd : HuffmanDecoder) (st : Store) (idx : Nat)
    (body : Bytes) (base : Nat) : Except Err (Store × LineOut × Nat) :=
  if idx = 0 then
    match readStr hd body with
    | .error e => .error e
    | .ok (name, nm) =>
      if utf8Ok name then
        match readStr hd (body.drop nm) with
        | .error e => .error e
        | .ok (value, vm) =>
          if utf8Ok value then
            match emitField st name value with
            | .error e => .error e
            | .ok (st', out) => .ok (st', out, base + nm + vm)
          else .error .nonUtf8
      else .error .nonUtf8
  else
    match staticEntry idx with
    | none => if idx ≤ 61 then .error .staticIndex else .error .dynamicUnsupported
    | some (name, _) =>
      match readStr hd body with
      | .error e => .error e
      | .ok (value, vm) =>
        if utf8Ok value then
          match emitField st (strBytes name) value with
          | .error e => .error e
          | .ok (st', out) => .ok (st', out, base + vm)
        else .error .nonUtf8

theorem decodeLiteralField_consumed (hd : HuffmanDecoder) (st : Store) (idx : Nat)
    (body : Bytes) (base : Nat) (st' : Store) (out : LineOut) (n : Nat)
    (h : decodeLiteralField hd st idx body base = .ok (st', out, n)) :
    base ≤ n ∧ n ≤ base + body.length := by
  unfold decodeLiteralField at h
  split at h
  · split at h
    · exact absurd h (by simp)
    · rename_i name nm hrs1
      have h1 := readStr_consumed hd body name nm hrs1
      split at h
      · split at h
        · exact absurd h (by simp)
        · rename_i value vm hrs2
          have h2 := readStr_consumed hd (body.drop nm) value vm hrs2
          simp only [List.length_drop] at h2
          split at h
          · split at h
            · exact absurd h (by simp)
            · cases h; omega
          · exact absurd h (by simp)
      · exact absurd h (by simp)
  · split at h
    · split at h <;> exact absurd h (by simp)
    · rename_i name _hv
      split at h
      · exact absurd h (by simp)
      · rename_i value vm hrs
        have h2 := readStr_consumed hd body value vm hrs
        split at h
        · split at h
          · exact absurd h (by simp)
          · cases h; omega
        · exact absurd h (by simp)

theorem decodeLiteralField_wf (hd : HuffmanDecoder) (st : Store) (idx : Nat)
    (body : Bytes) (base : Nat) (st' : Store) (out : LineOut) (n : Nat)
    (hwf : st.Wf) (h : decodeLiteralField hd st idx body base = .ok (st', out, n)) :
    st'.Wf := by
  unfold decodeLiteralField at h
  repeat' split at h
  all_goals cases h
  all_goals exact emitField_wf _ _ _ _ _ hwf (by assumption)

theorem decodeLiteralField_main (hd : HuffmanDecoder) (st : Store) (idx : Nat)
    (body : Bytes) (base : Nat) (st' : Store) (out : LineOut) (n : Nat)
    (h : decodeLiteralField hd st idx body base = .ok (st', out, n)) :
    st'.main = st.main := by
  unfold decodeLiteralField at h
  repeat' split at h
  all_goals cases h
  all_goals exact emitField_main _ _ _ _ _ (by assumption)

/-! ## Decoding one field representation (§6.1–§6.3) -/

/-- Decode one header-field representation from the head of `bs`.

Taxonomy by the top bits of the first byte (RFC 7541 §6):

* `1 idx(7)` — indexed header field (§6.1); index ≥ 62 → dynamic stub.
* `01 idx(6)` — literal with incremental indexing (§6.2.1); the table insert is
  the dynamic stub (no-op), but the field itself decodes.
* `001 xxxxx` — dynamic table size update (§6.3): dynamic stub.
* `0000 idx(4)` / `0001 idx(4)` — literal without indexing / never indexed
  (§6.2.2, §6.2.3).

Returns the grown store, the field's contribution, and bytes consumed. -/
def decodeOneField (hd : HuffmanDecoder) (st : Store) (bs : Bytes) :
    Except Err (Store × LineOut × Nat) :=
  match bs with
  | [] => .error .truncated
  | b :: rest =>
    if 0x80 ≤ b.toNat then
      -- Indexed header field (§6.1)
      match decPrefixInt 7 b rest with
      | none => .error .truncated
      | some (idx, n) =>
        match staticEntry idx with
        | some (name, value) =>
          match emitField st (strBytes name) (strBytes value) with
          | .error e => .error e
          | .ok (st', out) => .ok (st', out, 1 + n)
        | none =>
          if idx = 0 then .error .invalidIndex
          else if idx ≤ 61 then .error .staticIndex
          else .error .dynamicUnsupported
    else if 0x40 ≤ b.toNat then
      -- Literal with incremental indexing (§6.2.1)
      match decPrefixInt 6 b rest with
      | none => .error .truncated
      | some (idx, n) => decodeLiteralField hd st idx (rest.drop n) (1 + n)
    else if 0x20 ≤ b.toNat then
      -- Dynamic table size update (§6.3): dynamic-table state, out of scope
      .error .dynamicUnsupported
    else
      -- Literal without indexing / never indexed (§6.2.2, §6.2.3)
      match decPrefixInt 4 b rest with
      | none => .error .truncated
      | some (idx, n) => decodeLiteralField hd st idx (rest.drop n) (1 + n)

/-- **Progress + boundedness** for one field: at least one byte, never more
than the input. -/
theorem decodeOneField_consumed (hd : HuffmanDecoder) (st : Store) (bs : Bytes)
    (st' : Store) (out : LineOut) (n : Nat)
    (h : decodeOneField hd st bs = .ok (st', out, n)) :
    1 ≤ n ∧ n ≤ bs.length := by
  unfold decodeOneField at h
  split at h
  · exact absurd h (by simp)
  · rename_i b rest
    split at h
    · -- indexed
      split at h
      · exact absurd h (by simp)
      · rename_i idx n₁ hpi
        have hn₁ := decPrefixInt_consumed 7 b rest idx n₁ hpi
        split at h
        · split at h
          · exact absurd h (by simp)
          · cases h
            simp only [List.length_cons]
            omega
        · split at h
          · exact absurd h (by simp)
          · split at h <;> exact absurd h (by simp)
    · split at h
      · -- incremental indexing
        split at h
        · exact absurd h (by simp)
        · rename_i idx n₁ hpi
          have hn₁ := decPrefixInt_consumed 6 b rest idx n₁ hpi
          have hlf := decodeLiteralField_consumed hd st idx (rest.drop n₁) (1 + n₁)
            st' out n h
          simp only [List.length_drop, List.length_cons] at hlf ⊢
          omega
      · split at h
        · exact absurd h (by simp)
        · -- literal without / never indexed
          split at h
          · exact absurd h (by simp)
          · rename_i idx n₁ hpi
            have hn₁ := decPrefixInt_consumed 4 b rest idx n₁ hpi
            have hlf := decodeLiteralField_consumed hd st idx (rest.drop n₁) (1 + n₁)
              st' out n h
            simp only [List.length_drop, List.length_cons] at hlf ⊢
            omega

/-- One field preserves store well-formedness. -/
theorem decodeOneField_wf (hd : HuffmanDecoder) (st : Store) (bs : Bytes)
    (st' : Store) (out : LineOut) (n : Nat) (hwf : st.Wf)
    (h : decodeOneField hd st bs = .ok (st', out, n)) : st'.Wf := by
  unfold decodeOneField at h
  repeat' split at h
  all_goals try exact decodeLiteralField_wf _ _ _ _ _ _ _ _ hwf h
  all_goals cases h
  all_goals exact emitField_wf _ _ _ _ _ hwf (by assumption)

/-- One field never touches the main arena. -/
theorem decodeOneField_main (hd : HuffmanDecoder) (st : Store) (bs : Bytes)
    (st' : Store) (out : LineOut) (n : Nat)
    (h : decodeOneField hd st bs = .ok (st', out, n)) :
    st'.main = st.main := by
  unfold decodeOneField at h
  repeat' split at h
  all_goals try exact decodeLiteralField_main _ _ _ _ _ _ _ _ h
  all_goals cases h
  all_goals exact emitField_main _ _ _ _ _ (by assumption)

/-! ## The field loop (a whole header block) -/

set_option linter.unusedVariables false in
/-- Decode all field representations of a header block. Termination is
`decodeOneField_consumed` (every field eats at least one byte; the discriminant
name `h` is used only by `decreasing_by`). -/
def decodeBlock (hd : HuffmanDecoder) (st : Store) (bs : Bytes)
    (pseudo : Pseudo) (acc : List FieldLine) :
    Except Err (Store × Pseudo × List FieldLine) :=
  match bs with
  | [] => .ok (st, pseudo, acc.reverse)
  | b :: rest =>
    match h : decodeOneField hd st (b :: rest) with
    | .error e => .error e
    | .ok (st', out, n) =>
      decodeBlock hd st' ((b :: rest).drop n)
        (match out with
         | .pseudo k ve => pseudo.set k ve
         | .field _ => pseudo)
        (match out with
         | .pseudo _ _ => acc
         | .field fl => fl :: acc)
termination_by bs.length
decreasing_by
  all_goals
    have := decodeOneField_consumed hd st (b :: rest) st' out n h
    simp only [List.length_drop, List.length_cons]
    omega

/-- The loop preserves well-formedness. -/
theorem decodeBlock_wf (hd : HuffmanDecoder) (st : Store) (bs : Bytes)
    (pseudo : Pseudo) (acc : List FieldLine) :
    ∀ r : Store × Pseudo × List FieldLine, st.Wf →
      decodeBlock hd st bs pseudo acc = .ok r → r.1.Wf := by
  induction st, bs, pseudo, acc using decodeBlock.induct hd with
  | case1 st pseudo acc =>
    intro r hwf h
    simp only [decodeBlock] at h
    cases h
    exact hwf
  | case2 st pseudo acc b rest e hline =>
    intro r hwf h
    simp only [decodeBlock] at h
    split at h
    · cases h
    · rename_i st' out n heq
      rw [hline] at heq
      cases heq
  | case3 st pseudo acc b rest st' out n hline ih =>
    intro r hwf h
    simp only [decodeBlock] at h
    split at h
    · rename_i e heq
      rw [hline] at heq
      cases heq
    · rename_i st'' out'' n'' heq
      rw [hline] at heq
      cases heq
      exact ih r (decodeOneField_wf _ _ _ _ _ _ hwf hline) h

/-- The loop never touches the main arena. -/
theorem decodeBlock_main (hd : HuffmanDecoder) (st : Store) (bs : Bytes)
    (pseudo : Pseudo) (acc : List FieldLine) :
    ∀ r : Store × Pseudo × List FieldLine,
      decodeBlock hd st bs pseudo acc = .ok r → r.1.main = st.main := by
  induction st, bs, pseudo, acc using decodeBlock.induct hd with
  | case1 st pseudo acc =>
    intro r h
    simp only [decodeBlock] at h
    cases h
    rfl
  | case2 st pseudo acc b rest e hline =>
    intro r h
    simp only [decodeBlock] at h
    split at h
    · cases h
    · rename_i st' out n heq
      rw [hline] at heq
      cases heq
  | case3 st pseudo acc b rest st' out n hline ih =>
    intro r h
    simp only [decodeBlock] at h
    split at h
    · rename_i e heq
      rw [hline] at heq
      cases heq
    · rename_i st'' out'' n'' heq
      rw [hline] at heq
      cases heq
      rw [ih r h, decodeOneField_main _ _ _ _ _ _ hline]

/-- A decoded header block: the grown store, the routed pseudo-headers, and the
regular fields in wire order. -/
structure Decoded where
  store : Store
  pseudo : Pseudo
  fields : List FieldLine

/-- Decode a whole HPACK header block into the store. -/
def decodeHeaderBlock (hd : HuffmanDecoder) (st : Store) (bs : Bytes) :
    Except Err Decoded :=
  match decodeBlock hd st bs {} [] with
  | .error e => .error e
  | .ok (st', pseudo, fields) => .ok ⟨st', pseudo, fields⟩

/-- **The headline theorem — Wf preservation** (the H2 analogue of the QPACK
`Wf` discharge): decoding a header block into a well-formed store yields a
well-formed store, for every Huffman-decoder behavior and every input. -/
theorem decodeHeaderBlock_wf (hd : HuffmanDecoder) (st : Store) (bs : Bytes)
    (r : Decoded) (hwf : st.Wf) (h : decodeHeaderBlock hd st bs = .ok r) :
    r.store.Wf := by
  unfold decodeHeaderBlock at h
  split at h
  · exact absurd h (by simp)
  · rename_i st' pseudo fields hblk
    cases h
    exact decodeBlock_wf _ _ _ _ _ _ hwf hblk

/-- Corollary, in emitted-entry form: **every view entry of the decoded store —
the emitted ones included — is in-bounds of the arena it addresses.** -/
theorem decodeHeaderBlock_entries_inBounds (hd : HuffmanDecoder) (st : Store)
    (bs : Bytes) (r : Decoded) (hwf : st.Wf)
    (h : decodeHeaderBlock hd st bs = .ok r) :
    ∀ e ∈ r.store.entries, r.store.InBounds e :=
  decodeHeaderBlock_wf hd st bs r hwf h

/-- The decode only appends to the sidecar: the main arena — the wire bytes —
is preserved byte-for-byte. -/
theorem decodeHeaderBlock_main (hd : HuffmanDecoder) (st : Store) (bs : Bytes)
    (r : Decoded) (h : decodeHeaderBlock hd st bs = .ok r) :
    r.store.main = st.main := by
  unfold decodeHeaderBlock at h
  split at h
  · exact absurd h (by simp)
  · rename_i st' pseudo fields hblk
    cases h
    exact decodeBlock_main _ _ _ _ _ _ hblk

/-! ## Wire vectors, checker-verified at build time (through `#guard`:
well-founded definitions do not kernel-reduce). All with the empty store and a
Huffman decoder that rejects everything — none of these vectors sets the
Huffman bit, so the decoder is never consulted. -/

private def rejectAllHuffman : HuffmanDecoder := ⟨fun _ => none⟩

private def emptyStore : Store := { main := #[], sidecar := #[], entries := [] }

/-- `0x82` = indexed static 2 (`:method: GET`): routed to the pseudo record,
value entry emitted, store well-formed. -/
private def vecIndexedStatic : Bool :=
  match decodeHeaderBlock rejectAllHuffman emptyStore [0x82] with
  | .ok r => r.pseudo.method.isSome && r.fields.isEmpty && r.store.wfCheck
  | .error _ => false
#guard vecIndexedStatic

/-- `0x84` = indexed static 4 (`:path: /`). -/
private def vecIndexedPath : Bool :=
  match decodeHeaderBlock rejectAllHuffman emptyStore [0x84] with
  | .ok r => r.pseudo.path.isSome && r.store.wfCheck
  | .error _ => false
#guard vecIndexedPath

/-- `0x44` = literal with incremental indexing, static name index 4 (`:path`),
then the value literal `/idx` (raw, 7-bit length prefix). -/
private def vecPathLiteral : Bool :=
  match decodeHeaderBlock rejectAllHuffman emptyStore
      ([0x44, 0x04] ++ strBytes "/idx") with
  | .ok r => r.pseudo.path.isSome && r.fields.isEmpty && r.store.wfCheck
  | .error _ => false
#guard vecPathLiteral

/-- `0x40` = literal with incremental indexing, literal name (index 0): name
`x-seven` (7-byte raw literal), then value `ok`: one regular field, name +
value entries, store well-formed. -/
private def vecLiteralLiteral : Bool :=
  match decodeHeaderBlock rejectAllHuffman emptyStore
      ([0x40, 0x07] ++ strBytes "x-seven" ++ [0x02] ++ strBytes "ok") with
  | .ok r =>
    r.fields.length == 1 && r.store.entries.length == 2 && r.store.wfCheck
  | .error _ => false
#guard vecLiteralLiteral

/-- `0x00` = literal without indexing, literal name `x-a` then value `b`. -/
private def vecLiteralNoIndex : Bool :=
  match decodeHeaderBlock rejectAllHuffman emptyStore
      ([0x00, 0x03] ++ strBytes "x-a" ++ [0x01] ++ strBytes "b") with
  | .ok r => r.fields.length == 1 && r.store.wfCheck
  | .error _ => false
#guard vecLiteralNoIndex

/-- `0xbe` = indexed field, index 62: the first dynamic-table slot — must hit
the explicit stub. -/
private def vecDynamicStub : Bool :=
  match decodeHeaderBlock rejectAllHuffman emptyStore [0xbe] with
  | .error .dynamicUnsupported => true
  | _ => false
#guard vecDynamicStub

/-- `0x3f 0x00` = dynamic table size update (`001` prefix): dynamic-table
state, must hit the stub. -/
private def vecSizeUpdateStub : Bool :=
  match decodeHeaderBlock rejectAllHuffman emptyStore [0x3f, 0x00] with
  | .error .dynamicUnsupported => true
  | _ => false
#guard vecSizeUpdateStub

/-- `0x80` = indexed field, index 0: invalid (RFC 7541 §6.1). -/
private def vecIndexZero : Bool :=
  match decodeHeaderBlock rejectAllHuffman emptyStore [0x80] with
  | .error .invalidIndex => true
  | _ => false
#guard vecIndexZero

end Hpack
end H2
