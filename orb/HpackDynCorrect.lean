/-
HPACK dynamic table — the CORRECTNESS theory (RFC 7541 §2.3, §4).

`H2/Hpack.lean` decodes literal and static-table header fields into the arena
`Store` and proves well-formedness (every emitted view entry is in-bounds).
Its treatment of the *dynamic* table is a stub: an indexed reference into the
dynamic table (absolute index ≥ 62) is rejected, and the incremental-indexing
insertion side effect performs no table update, because no table state exists to
consult.

This file supplies the missing state: a real dynamic table with insertion,
eviction, and indexed lookup per RFC 7541, together with a CORRECTNESS spec and
a refinement proof.

The table is modeled as a list of (name, value) octet-string pairs held
NEWEST-FIRST: the head is the most recently inserted entry. RFC 7541 §2.3.3
numbers dynamic entries so that the newest has the lowest index, and the first
dynamic index is 62 (the static table occupies 1–61); hence absolute index `i`
(with `i ≥ 62`) names the `(i - 62)`-th entry from the head. Insertion prepends
the new entry and evicts the OLDEST entries — a suffix of the list — until the
table fits its maximum size (RFC 7541 §4.1, §4.4). An entry larger than the
maximum empties the table.

Two headline theorems:

* `hpack_dyntable_indexed_correct` — the insert-then-index round trip: after
  inserting `(n, v)` (which fits the maximum), an indexed reference at absolute
  index 62 decodes to EXACTLY `(n, v)`. The `H2/Hpack.lean` stub returns *no*
  entry for index ≥ 62, so it FAILS this theorem (`stub_decoder_refuted`).
* `hpack_dyntable_evict_correct` — when the incoming entry cannot coexist with
  everything already stored, the insert evicts strictly from the OLD end: the
  surviving old entries are a proper prefix (the newest ones), and the table is
  back within its maximum size.

The CORRECTNESS spec itself is `AddSpec`, a declarative, storage-independent
statement of what an RFC-conformant insertion must produce (newest at the head,
only oldest entries removed, size within the maximum, oversize empties). The
refinement theorem `hpack_dyntable_add_refines_spec` proves the operational
`DynTable.add` satisfies it. `AddSpec` is phrased in terms of `head?`,
`IsPrefix`, and a size bound — not the `keepFit` recursion that `add` computes —
so it is a genuine specification, not the implementation renamed.
-/
import H2.Hpack

namespace H2
namespace Hpack

/-- A dynamic-table entry: a (name, value) pair of octet strings. -/
abbrev Pair := Bytes × Bytes

/-! ## Entry and table size (RFC 7541 §4.1) -/

/-- RFC 7541 §4.1: the size of an entry is its name length in octets plus its
value length in octets plus 32. -/
def entrySize (p : Pair) : Nat := p.1.length + p.2.length + 32

/-- RFC 7541 §4.1: the size of the dynamic table is the sum of the sizes of its
entries. -/
def tableSize : List Pair → Nat
  | [] => 0
  | p :: rest => entrySize p + tableSize rest

@[simp] theorem tableSize_nil : tableSize [] = 0 := rfl

theorem tableSize_cons (p : Pair) (es : List Pair) :
    tableSize (p :: es) = entrySize p + tableSize es := rfl

/-! ## The dynamic table and its operations -/

/-- The dynamic table: entries NEWEST-FIRST (head = most recently inserted) and
a maximum size in octets (RFC 7541 §4.2). -/
structure DynTable where
  entries : List Pair
  maxSize : Nat

/-- RFC 7541 §2.3.3 / §6.1: resolve an indexed reference. The dynamic table
begins at absolute index 62 (the static table occupies 1–61); absolute index
`i ≥ 62` names the `(i - 62)`-th entry from the head (newest first). Indices
below 62 are not the dynamic table's responsibility. -/
def DynTable.resolve (t : DynTable) (i : Nat) : Option Pair :=
  if 62 ≤ i then t.entries[i - 62]? else none

/-- Keep the newest entries (a prefix, scanning from the head) whose cumulative
size fits within `budget`, dropping the first entry that would overflow it and
every older entry after it. This realizes RFC 7541 §4.4 eviction: to make room
for an incoming entry of size `s` under maximum `max`, the retained old entries
are exactly the longest newest-first prefix with cumulative size `≤ max - s`;
all older entries are evicted from the end. -/
def keepFit : List Pair → Nat → List Pair
  | [], _ => []
  | e :: rest, budget =>
    if entrySize e ≤ budget then e :: keepFit rest (budget - entrySize e) else []

/-- RFC 7541 §2.3.3, §4.4: insert `(n, v)` as the new newest entry. If it fits
the maximum, evict the oldest entries so the retained old entries plus the new
one stay within the maximum, and prepend the new entry. If it is larger than the
maximum, the table is emptied (and the entry is not stored). -/
def DynTable.add (t : DynTable) (n v : Bytes) : DynTable :=
  if entrySize (n, v) ≤ t.maxSize then
    { t with entries := (n, v) :: keepFit t.entries (t.maxSize - entrySize (n, v)) }
  else
    { t with entries := [] }

/-! ## `keepFit` — eviction facts -/

/-- Eviction only removes entries from the OLD end: the retained entries are a
prefix of the original list (with an explicit evicted suffix). -/
theorem keepFit_prefix : ∀ (es : List Pair) (budget : Nat),
    ∃ suf, keepFit es budget ++ suf = es
  | [], _ => ⟨[], rfl⟩
  | e :: rest, budget => by
    simp only [keepFit]
    by_cases h : entrySize e ≤ budget
    · simp only [h, if_true]
      obtain ⟨suf, hsuf⟩ := keepFit_prefix rest (budget - entrySize e)
      exact ⟨suf, by rw [List.cons_append, hsuf]⟩
    · simp only [h, if_false]
      exact ⟨e :: rest, rfl⟩

/-- Eviction keeps the retained entries within the budget: the cumulative size
of the kept prefix never exceeds `budget`. -/
theorem keepFit_size : ∀ (es : List Pair) (budget : Nat),
    tableSize (keepFit es budget) ≤ budget
  | [], budget => by simp [keepFit]
  | e :: rest, budget => by
    simp only [keepFit]
    by_cases h : entrySize e ≤ budget
    · simp only [h, if_true, tableSize_cons]
      have ih := keepFit_size rest (budget - entrySize e)
      omega
    · simp only [h, if_false, tableSize_nil]
      exact Nat.zero_le _

/-! ## The CORRECTNESS specification (RFC 7541 §2.3.3, §4.1, §4.4) -/

/-- **The RFC-conformant insertion specification.** Given a dynamic table listed
newest-first as `pre` with maximum size `max`, inserting `(n, v)` must produce a
list `post` satisfying, declaratively:

* `newest` (§2.3.3): when the entry fits the maximum, it becomes the newest
  entry — the head of `post` — so an indexed reference at absolute index 62
  resolves to it.
* `onlyOldestEvicted` (§4.4): when the entry fits, the entries surviving from
  `pre` are a PREFIX of `pre` (the newest ones); eviction only ever removes
  entries from the old end.
* `withinMax` (§4.1, §4.4): when the entry fits, the resulting table size does
  not exceed the maximum.
* `oversizeEmpties` (§4.4): an entry larger than the maximum empties the table.

This is a specification, not the implementation: it constrains `post` through
`head?`, `IsPrefix`, and a size bound, never mentioning how eviction is
computed. A decoder that dropped the new entry (or reordered, or kept the old
entries and overflowed the maximum) fails one of these clauses. -/
structure AddSpec (pre : List Pair) (max : Nat) (n v : Bytes) (post : List Pair) :
    Prop where
  newest : entrySize (n, v) ≤ max → post.head? = some (n, v)
  onlyOldestEvicted : entrySize (n, v) ≤ max → ∃ suf, post.tail ++ suf = pre
  withinMax : entrySize (n, v) ≤ max → tableSize post ≤ max
  oversizeEmpties : max < entrySize (n, v) → post = []

/-- **The refinement theorem.** The operational `DynTable.add` satisfies the
declarative `AddSpec` on every table and every entry: it is a faithful
realization of the RFC 7541 §2.3.3/§4.1/§4.4 insertion semantics. -/
theorem hpack_dyntable_add_refines_spec (t : DynTable) (n v : Bytes) :
    AddSpec t.entries t.maxSize n v (t.add n v).entries := by
  by_cases hs : entrySize (n, v) ≤ t.maxSize
  · -- the entry fits: add prepends and evicts oldest
    have hadd : (t.add n v).entries
        = (n, v) :: keepFit t.entries (t.maxSize - entrySize (n, v)) := by
      unfold DynTable.add; simp only [hs, if_true]
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun hover => ?_⟩
    · rw [hadd]; rfl
    · rw [hadd]; simpa using keepFit_prefix t.entries (t.maxSize - entrySize (n, v))
    · rw [hadd, tableSize_cons]
      have := keepFit_size t.entries (t.maxSize - entrySize (n, v))
      omega
    · omega
  · -- the entry is larger than the maximum: table emptied
    have hadd : (t.add n v).entries = [] := by
      unfold DynTable.add; simp only [hs, if_false]
    refine ⟨fun h => absurd h hs, fun h => absurd h hs, fun h => absurd h hs,
      fun _ => hadd⟩

/-! ## Headline theorem 1 — indexed decode of the just-inserted entry -/

/-- **`hpack_dyntable_indexed_correct` (RFC 7541 §2.3.3, §6.1).** The
insert-then-index round trip: after inserting `(n, v)` into a dynamic table whose
maximum accommodates it, an indexed reference at absolute index 62 — the first
dynamic index — decodes to EXACTLY `(n, v)`.

This is what the `H2/Hpack.lean` dynamic-table stub cannot do: the stub returns
no entry (an error) for any index ≥ 62. See `stub_decoder_refuted`. -/
theorem hpack_dyntable_indexed_correct (t : DynTable) (n v : Bytes)
    (hs : entrySize (n, v) ≤ t.maxSize) :
    (t.add n v).resolve 62 = some (n, v) := by
  have hadd : (t.add n v).entries
      = (n, v) :: keepFit t.entries (t.maxSize - entrySize (n, v)) := by
    unfold DynTable.add; simp only [hs, if_true]
  unfold DynTable.resolve
  rw [hadd]
  simp

/-- **Non-vacuity — the stub is refuted.** Any decoder that resolves index 62 to
`none` (the `H2/Hpack.lean` behavior — index ≥ 62 yields no entry) violates
`hpack_dyntable_indexed_correct`: the correct answer is `some (n, v) ≠ none`. So
the correctness theorem is not satisfied by the stub; a real, populated table is
required. -/
theorem stub_decoder_refuted (t : DynTable) (n v : Bytes)
    (hs : entrySize (n, v) ≤ t.maxSize) :
    (t.add n v).resolve 62 ≠ none := by
  rw [hpack_dyntable_indexed_correct t n v hs]
  exact Option.some_ne_none _

/-! ## Headline theorem 2 — eviction removes the oldest first -/

/-- **`hpack_dyntable_evict_correct` (RFC 7541 §4.4).** When the incoming entry
`(n, v)` fits the maximum but cannot coexist with everything already stored
(`max < entrySize (n,v) + tableSize pre`), the insert evicts STRICTLY from the
OLD end:

* the surviving old entries are a prefix of the pre-insert table (`<+:`), so only
  the oldest entries are removed;
* strictly fewer old entries survive than were present (at least the oldest is
  gone); and
* the table is back within its maximum size.

Together these say eviction is oldest-first and bounded — the §4.4 requirement. -/
theorem hpack_dyntable_evict_correct (t : DynTable) (n v : Bytes)
    (hs : entrySize (n, v) ≤ t.maxSize)
    (hfull : t.maxSize < entrySize (n, v) + tableSize t.entries) :
    (t.add n v).entries.tail <+: t.entries ∧
      (t.add n v).entries.tail.length < t.entries.length ∧
      tableSize (t.add n v).entries ≤ t.maxSize := by
  have hadd : (t.add n v).entries
      = (n, v) :: keepFit t.entries (t.maxSize - entrySize (n, v)) := by
    unfold DynTable.add; simp only [hs, if_true]
  have htail : (t.add n v).entries.tail
      = keepFit t.entries (t.maxSize - entrySize (n, v)) := by
    rw [hadd]; rfl
  obtain ⟨suf, hsuf⟩ := keepFit_prefix t.entries (t.maxSize - entrySize (n, v))
  have hks := keepFit_size t.entries (t.maxSize - entrySize (n, v))
  -- the kept prefix is strictly smaller: it fits within max - s, the whole does not
  have hsuf_ne : suf ≠ [] := by
    intro hnil
    rw [hnil, List.append_nil] at hsuf
    -- then keepFit = t.entries, so tableSize t.entries ≤ max - s, contradicting hfull
    rw [hsuf] at hks
    omega
  have hlen : (keepFit t.entries (t.maxSize - entrySize (n, v))).length
      < t.entries.length := by
    have := congrArg List.length hsuf
    rw [List.length_append] at this
    have hsuflen : 0 < suf.length := List.length_pos.mpr hsuf_ne
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [htail]; exact ⟨suf, hsuf⟩
  · rw [htail]; exact hlen
  · rw [hadd, tableSize_cons]; omega

/-! ## Runtime wire vectors (structural definitions, kernel-reducible) -/

-- Entry sizes: e0 = 32 (empty name/value), e1 = e2 = 33 (one-byte name).
private def e0 : Pair := ([], [])          -- size 32
private def e1 : Pair := ([1], [])         -- size 33
private def e2 : Pair := ([2], [])         -- size 33

-- A 70-octet table. e0 then e1 total 32 + 33 = 65 ≤ 70 (both fit); adding e2
-- (size 33) would make 98 > 70, so the oldest, e0, is evicted.
private def t0 : DynTable := ⟨[], 70⟩

private def afterTwo : DynTable := (t0.add e0.1 e0.2).add e1.1 e1.2
private def afterThree : DynTable := afterTwo.add e2.1 e2.2

-- The newest entry after three inserts is e2, at absolute index 62.
#guard afterThree.resolve 62 == some e2

-- e1 (second newest) is at index 63.
#guard afterThree.resolve 63 == some e1

-- e0 was evicted — index 64 is empty (only two entries remain).
#guard afterThree.resolve 64 == none

-- The table is within its maximum after eviction.
#guard decide (tableSize afterThree.entries ≤ afterThree.maxSize)

-- Two entries fit before eviction.
#guard afterTwo.entries.length == 2

-- Three-insert table holds exactly two entries (one evicted).
#guard afterThree.entries.length == 2

end Hpack
end H2
