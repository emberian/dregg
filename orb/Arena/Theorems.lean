/-
Arena — the well-formedness theory.

The four headline results:

* `Store.resolve_total` — on a well-formed store, `resolve` succeeds for every
  stored entry (totality of the view).
* `Store.resolve_length` — a successful `resolve` returns exactly `len` bytes
  (so under `Wf`, every stored entry denotes exactly its declared length:
  `resolve_length_of_wf`).
* `Store.wf_pushEntry` — well-formedness is preserved by inserting an
  in-bounds entry (plus `wf_appendSidecar`: growing the sidecar never
  invalidates existing entries).
* `isMainAddr`/`isSidecarAddr` disjointness + coverage, and the high-bit
  characterization `isSidecarAddr_iff_testBit`: the two address spaces are
  discriminated exactly by bit 31 of the offset.
-/
import Arena.Basic

namespace Arena

/-! ## Address-space discrimination -/

/-- The main and sidecar address spaces are disjoint. -/
theorem addr_disjoint (off : Nat) : ¬(isMainAddr off ∧ isSidecarAddr off) := by
  unfold isMainAddr isSidecarAddr
  omega

/-- The main and sidecar address spaces cover every offset. -/
theorem addr_cover (off : Nat) : isMainAddr off ∨ isSidecarAddr off := by
  unfold isMainAddr isSidecarAddr
  omega

/-- No offset value is shared between the two address spaces. -/
theorem addr_spaces_disjoint {o₁ o₂ : Nat}
    (h₁ : isMainAddr o₁) (h₂ : isSidecarAddr o₂) : o₁ ≠ o₂ := by
  unfold isMainAddr isSidecarAddr at *
  omega

/-- For 32-bit offsets the discriminant is exactly the high bit: an offset
addresses the sidecar iff bit 31 is set. -/
theorem isSidecarAddr_iff_testBit {off : Nat} (h32 : off < 2 ^ 32) :
    isSidecarAddr off ↔ off.testBit 31 = true := by
  rw [Nat.testBit_to_div_mod]
  unfold isSidecarAddr sidecarBaseNat
  simp only [decide_eq_true_eq]
  omega

/-- The `UInt32` corollary: an entry is a sidecar entry iff the high bit of
its offset is set. -/
theorem Entry.inSidecar_iff_testBit (e : Entry) :
    e.inSidecar = true ↔ e.off.toNat.testBit 31 = true := by
  unfold Entry.inSidecar
  have h32 : e.off.toNat < 2 ^ 32 := e.off.toBitVec.isLt
  rw [decide_eq_true_eq, isSidecarAddr_iff_testBit h32]

/-- A main-arena entry reads the main arena. -/
theorem Store.arenaOf_main (s : Store) {e : Entry} (h : e.inSidecar = false) :
    s.arenaOf e = s.main := by
  unfold Store.arenaOf
  simp [h]

/-- A sidecar entry reads the sidecar arena. -/
theorem Store.arenaOf_sidecar (s : Store) {e : Entry} (h : e.inSidecar = true) :
    s.arenaOf e = s.sidecar := by
  unfold Store.arenaOf
  simp [h]

/-! ## The executable checker is exactly `Wf` -/

theorem Store.wfCheck_iff_Wf (s : Store) : s.wfCheck = true ↔ s.Wf := by
  unfold Store.wfCheck Store.Wf
  simp

/-! ## Totality of resolve -/

/-- `resolve` succeeds on any in-bounds entry. -/
theorem Store.resolve_isSome_of_inBounds (s : Store) {e : Entry}
    (h : s.InBounds e) : (s.resolve e).isSome := by
  unfold Store.resolve
  unfold Store.InBounds at h
  simp [h]

/-- **Totality**: on a well-formed store, `resolve` succeeds for every stored
entry. -/
theorem Store.resolve_total (s : Store) (hwf : s.Wf) :
    ∀ e ∈ s.entries, (s.resolve e).isSome :=
  fun e he => s.resolve_isSome_of_inBounds (hwf e he)

/-! ## Resolve returns exactly `len` bytes -/

/-- A successful `resolve` returns exactly `len` bytes. (No well-formedness
needed: success itself implies the bounds check passed.) -/
theorem Store.resolve_length (s : Store) {e : Entry} {b : Array UInt8}
    (hr : s.resolve e = some b) : b.size = e.len.toNat := by
  unfold Store.resolve at hr
  by_cases h : e.physOff + e.len.toNat ≤ (s.arenaOf e).size
  · simp only [h, if_pos] at hr
    cases hr
    simp [Array.size_extract]
    omega
  · simp [h] at hr

/-- Under `Wf`, every stored entry denotes exactly its declared length. -/
theorem Store.resolve_length_of_wf (s : Store) (hwf : s.Wf) :
    ∀ e ∈ s.entries, ∃ b, s.resolve e = some b ∧ b.size = e.len.toNat := by
  intro e he
  have hs := s.resolve_total hwf e he
  match hb : s.resolve e with
  | some b => exact ⟨b, rfl, s.resolve_length hb⟩
  | none => rw [hb] at hs; simp at hs

/-! ## Preservation of well-formedness -/

/-- `InBounds` only reads the arenas, so registering entries never changes
it. -/
theorem Store.inBounds_pushEntry (s : Store) (e e' : Entry) :
    (s.pushEntry e).InBounds e' ↔ s.InBounds e' := by
  unfold Store.pushEntry Store.InBounds Store.arenaOf
  rfl

/-- **Preservation**: inserting an in-bounds entry preserves
well-formedness. -/
theorem Store.wf_pushEntry (s : Store) (hwf : s.Wf) {e : Entry}
    (hb : s.InBounds e) : (s.pushEntry e).Wf := by
  intro e' he'
  rw [s.inBounds_pushEntry e e']
  rcases List.mem_cons.mp he' with h | h
  · exact h ▸ hb
  · exact hwf e' h

/-- Growing the sidecar arena never invalidates an existing in-bounds
entry. -/
theorem Store.inBounds_appendSidecar (s : Store) (bs : Array UInt8) {e : Entry}
    (h : s.InBounds e) : (s.appendSidecar bs).InBounds e := by
  unfold Store.InBounds Store.arenaOf Store.appendSidecar at *
  by_cases hside : e.inSidecar
  · simp only [hside, if_pos] at *
    simp only [Array.size_append]
    omega
  · simp only [hside, if_neg, Bool.false_eq_true, not_false_iff] at *
    exact h

/-- Appending to the sidecar preserves well-formedness. -/
theorem Store.wf_appendSidecar (s : Store) (hwf : s.Wf) (bs : Array UInt8) :
    (s.appendSidecar bs).Wf :=
  fun e he => s.inBounds_appendSidecar bs (hwf e he)

end Arena
