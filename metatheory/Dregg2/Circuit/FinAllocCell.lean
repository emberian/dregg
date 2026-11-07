/-
# Dregg2.Circuit.FinAllocCell — DEBT-B step 3A: UNBLOCK `allocCell` (the predicate-erase primitive).

`FinInterp` (step 3, committed) closes 18 of the 19 `RecStmt` constructors against the finite-map model,
and classifies the ONE it cannot: `RecStmt.allocCell`. The obstacle it measured, verbatim:

  `interp (.allocCell n) k = some (createCellIntoAsset k (n k))`, which is `bornEmptyCellSlots k (n k)`
  (reset the fresh id's per-cell slots) with `accounts := insert (n k) k.accounts`. Seven of the resets are
  a POINT default-write at one key; the `bal` reset `fun c a => if c = newCell then 0 else k.bal c a` zeroes
  the ENTIRE `(newCell, ·)` COLUMN across every asset `a` — a PREDICATE-ERASE over the sparse `bal` map, not
  a bounded touched-`Finset` write. The current `CanonMap` writer API (`set`/`insertNZ`/`setOver`) cannot
  express it, so `createCellStmt`/`createCellFromFactoryStmt` were blocked.

This file builds the missing primitive `filterErase` (drop every entry whose key satisfies a `Bool` predicate),
its `lookup`/`get` laws, the per-field DENOTATION BRIDGE, the finite step `finAllocCell` mirroring the `interp`
arm EXACTLY, and the headline square `denote_finAllocCell`. It builds ON committed R1/R3 (`FinKernelState`,
`FinKernelStep`, `FinInterp`, Argus `Stmt`) and edits NOTHING committed. Sorry-free; no carrier.

## THE FRESH-CELL RESET IS AN ERASE (the `cell` default is aligned to the kernel default)
`bornEmptyCellSlots` resets `cell := fun c => if c = newCell then default …`, and `(default : Value) =
Value.int 0` (`Exec/Value.lean:69`, `instance : Inhabited Value := ⟨.int 0⟩`). Since `FinKernelState.cell` is
now a `CanonMap CellId Value (Value.int 0)` (the default ALIGNED to the kernel default), the born value
`Value.int 0` IS the map's default — so the sparse-faithful `cell` reset is an ERASE (storing a default would
break the Canonical invariant). Every other reset (caps/delegate/delegations/slotCaveats/lifecycle/deathCert =
their field default; `bal` column = `0`) is likewise a default-write, so `erase`/`filterErase`.
`denote_finAllocCell` is therefore UNCONDITIONAL — no side condition — mirroring `createCellIntoAsset`'s
unconditionality.
-/
import Dregg2.Circuit.FinInterp
import Dregg2.Exec.ConcreteKernel

namespace Dregg2.Circuit.FinKernelState.SortedMap

open Dregg2.Circuit.FinKernelState

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u v

variable {K : Type u} {V : Type v} [LinearOrder K]

/-! ## §1 — `SortedMap.filterErase`: drop every entry whose key satisfies a `Bool` predicate.

The predicate-erase the `bal`-column reset needs. `erase` (committed) drops one key; `filterErase` drops a
whole predicate-defined set of keys — a bounded operation on the SPARSE map (it removes only the finitely-many
stored entries that match), yet it denotes to a PREDICATE-erase over the total-function model. The invariant
survives because filtering only removes entries (a sublist), exactly as `erase`. -/

/-- Raw-list predicate-erase: drop every entry whose key satisfies `p`. -/
def filterEraseList (p : K → Bool) : List (K × V) → List (K × V)
  | [] => []
  | (k, v) :: rest => if p k then filterEraseList p rest else (k, v) :: filterEraseList p rest

/-- `filterEraseList` is a sublist of the input (it only drops entries). -/
theorem filterEraseList_sublist (p : K → Bool) :
    ∀ l : List (K × V), List.Sublist (filterEraseList p l) l
  | [] => List.Sublist.refl _
  | (k, v) :: rest => by
      unfold filterEraseList
      by_cases h : p k
      · rw [if_pos h]; exact (filterEraseList_sublist p rest).cons _
      · rw [if_neg h]; exact (filterEraseList_sublist p rest).cons_cons _

/-- Membership in a predicate-erase implies membership in the input (via the sublist). -/
theorem mem_filterEraseList {p : K → Bool} {q : K × V} {l : List (K × V)}
    (h : q ∈ filterEraseList p l) : q ∈ l :=
  (filterEraseList_sublist p l).mem h

/-- **The lookup-after-`filterErase` law.** `none` at a key satisfying `p`, unchanged elsewhere. Holds with
NO nodup hypothesis: a satisfying key has ALL its entries dropped (so `lookupList` finds nothing), and a
non-satisfying key keeps all of them (so the first match is unchanged). -/
theorem lookupList_filterEraseList (p : K → Bool) (x : K) (l : List (K × V)) :
    lookupList x (filterEraseList p l) = if p x then none else lookupList x l := by
  induction l with
  | nil => simp [filterEraseList, lookupList]
  | cons hd tl ih =>
      obtain ⟨k, v⟩ := hd
      simp only [filterEraseList]
      by_cases hpk : p k
      · -- the head entry is DROPPED
        simp only [if_pos hpk, ih]
        by_cases hpx : p x
        · simp [hpx]
        · -- `p x = false`, `p k = true` ⇒ `k ≠ x`, so `lookupList x ((k,v)::tl) = lookupList x tl`
          have hkx : ¬ k = x := by intro h; rw [h] at hpk; exact absurd hpk (by simp [hpx])
          simp only [if_neg hpx, lookupList, if_neg hkx]
      · -- the head entry is KEPT
        simp only [if_neg hpk, lookupList]
        by_cases hkx : k = x
        · -- `k = x` ⇒ `p x = p k = false`
          have hpx : ¬ p x := by rw [← hkx]; exact hpk
          simp [hkx, hpx]
        · simp only [if_neg hkx, ih]

/-- **`SortedMap.filterErase`** — drop every entry whose key satisfies `p`, preserving the strictly-increasing
key invariant (a sublist of the entries has a sublist of the keys, hence stays `Pairwise (· < ·)`). -/
def filterErase (p : K → Bool) (m : SortedMap K V) : SortedMap K V :=
  ⟨filterEraseList p m.entries,
   m.sortedKeys.sublist ((filterEraseList_sublist p m.entries).map Prod.fst)⟩

/-- **`lookup_filterErase`.** `none` at a key satisfying `p`, unchanged otherwise. -/
@[simp] theorem lookup_filterErase (p : K → Bool) (m : SortedMap K V) (k : K) :
    (m.filterErase p).lookup k = if p k then none else m.lookup k :=
  lookupList_filterEraseList p k m.entries

end Dregg2.Circuit.FinKernelState.SortedMap

/-! ## §2 — `CanonMap.filterErase` (lifting) + `CanonMap.erase` (the single-key default-write, no `DecidableEq`).

`filterErase` lifts to `CanonMap` because filtering only removes entries (Canonical preserved). `CanonMap.erase`
is the single-key default-write (`get x = if x = k then d else …`) with NO `DecidableEq V` — needed for the
`cell` slot whose `Value` has no `DecidableEq` (the committed `set` needs one). The seven point-resets in
`bornEmptyCellSlots` write the field DEFAULT, so they are all erases (including `cell`, whose born value
`Value.int 0` is now the map's aligned default). -/

namespace Dregg2.Circuit.FinKernelState.CanonMap

open Dregg2.Circuit.FinKernelState

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v

variable {K : Type u} {V : Type v} [LinearOrder K] {d : V}

/-- Filtering only removes entries, so the "no entry stores the default" invariant survives. -/
theorem canon_filterErase {m : SortedMap K V} (hc : SortedMap.Canonical d m) (p : K → Bool) :
    SortedMap.Canonical d (m.filterErase p) :=
  fun q hq => hc q (SortedMap.mem_filterEraseList hq)

/-- **`CanonMap.filterErase`** — predicate-erase on a canonical map. -/
def filterErase (cm : CanonMap K V d) (p : K → Bool) : CanonMap K V d :=
  ⟨cm.toMap.filterErase p, canon_filterErase cm.canon p⟩

/-- **`CanonMap.get_filterErase`.** The total read after a predicate-erase: the field default `d` at any key
satisfying `p`, the old read elsewhere — a PREDICATE-erase reproduced by the bounded sparse filtering. -/
@[simp] theorem get_filterErase (cm : CanonMap K V d) (p : K → Bool) (x : K) :
    (cm.filterErase p).get x = if p x then d else cm.get x := by
  unfold CanonMap.filterErase CanonMap.get SortedMap.get
  simp only [SortedMap.lookup_filterErase]
  by_cases hp : p x <;> simp [hp]

/-- **`CanonMap.erase`** — single-key default-write, `DecidableEq V`-free (the `cell`-slot-safe erase). -/
def erase (cm : CanonMap K V d) (k : K) : CanonMap K V d :=
  ⟨cm.toMap.erase k, canon_erase cm.canon k⟩

/-- **`CanonMap.get_erase`.** `get x = if x = k then d else cm.get x` — the single-key reset-to-default. -/
@[simp] theorem get_erase (cm : CanonMap K V d) (k x : K) :
    (cm.erase k).get x = if x = k then d else cm.get x := by
  unfold CanonMap.erase CanonMap.get SortedMap.get
  simp only [SortedMap.lookup_erase]
  by_cases hx : x = k <;> simp [hx]

end Dregg2.Circuit.FinKernelState.CanonMap

namespace Dregg2.Circuit.FinAllocCell

open Dregg2.Exec Dregg2.Authority
open Dregg2.Circuit.FinKernelState
open Dregg2.Circuit.FinInterp
open Dregg2.Circuit.Argus (RecStmt interp)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §3 — the small facts the resets need. -/

/-- `Value.int 0 ≠ Value.record []` — retained for downstream teeth (`FinCreateCellSquares`) that contrast the
kernel born value with an empty-record value. The `cell` reset itself no longer uses this (it is an ERASE now
that the `cell` default is aligned to `Value.int 0`). -/
theorem valInt0_ne_record : (Value.int 0) ≠ Value.record [] := by simp

/-- `(default : Value) = Value.int 0` — pinned so the `cell` reset in `bornEmptyCellSlots` matches the stored
value. Definitional (`Exec/Value.lean:69`). -/
theorem default_value : (default : Value) = Value.int 0 := rfl

/-! ## §4 — THE DENOTATION BRIDGE for the `bal`-column predicate-erase.

The load-bearing per-field naturality: erasing the `(newCell, ·)` column in the finite `bal` map denotes to
the total-function predicate-erase `fun c a => if c = newCell then 0 else (denote f).bal c a`. This is the
step the current `setOver` machinery could not take (it writes a bounded `Finset`, not a predicate-set). -/

/-- **`denote_filterErase_bal` — THE BRIDGE.** Predicate-erasing the `(newCell, ·)` column commutes with
`denote`, yielding the exact column-zeroing the kernel allocator performs. -/
theorem denote_filterErase_bal (f : FinKernelState) (newCell : CellId) :
    denote { f with bal := f.bal.filterErase (fun key => decide ((ofLex key).1 = newCell)) }
      = { denote f with bal := fun c a => if c = newCell then 0 else (denote f).bal c a } := by
  rw [denote_with_bal]
  apply RecordKernelState.ext <;> try rfl
  funext c a
  show (f.bal.filterErase (fun key => decide ((ofLex key).1 = newCell))).get (toLex (c, a))
      = if c = newCell then 0 else (denote f).bal c a
  rw [CanonMap.get_filterErase]
  show (if decide (c = newCell) then (0 : ℤ) else f.bal.get (toLex (c, a)))
      = if c = newCell then 0 else (denote f).bal c a
  by_cases hc : c = newCell <;> simp [hc, denote]

/-! ## §5 — `finAllocCell`: the finite step mirroring `interp`'s allocCell arm EXACTLY.

`interp (.allocCell n) k = some (createCellIntoAsset k (n k))` = `some (bornEmptyCellSlots k (n k)` with
`accounts := insert (n k) k.accounts)`. The mirror, over the finite maps, at `newCell = n (denote f)`:

  * `accounts` — `insert newCell f.accounts` (verbatim, `accounts` is carried as a `Finset`);
  * `cell`     — `erase newCell`: the fresh cell is born at the kernel default `Value.int 0`, which is now the
    `cell` `CanonMap`'s OWN default (aligned), so the sparse-faithful write is an ERASE (§Correction);
  * `caps`/`delegations`/`slotCaveats`/`lifecycle`/`deathCert` — `erase newCell` (each writes its field default);
  * `delegate` — `SortedMap.erase newCell` (absence = `none`, the field default);
  * `bal`      — `filterErase` the `(newCell, ·)` column (writes the ledger default `0`);
  * every other field (`delegationEpoch`/`delegationEpochAt`/`heaps`/roots/list side-tables) — untouched, EXACTLY
    as `bornEmptyCellSlots` leaves them.

`n` is applied to `denote f` (the record-model view the reference `interp` reads). -/
noncomputable def finAllocCell (n : RecordKernelState → CellId) (f : FinKernelState) : FinKernelState :=
  let newCell := n (denote f)
  { f with
    accounts := insert newCell f.accounts
    cell := f.cell.erase newCell
    caps := f.caps.erase newCell
    delegate := f.delegate.erase newCell
    delegations := f.delegations.erase newCell
    slotCaveats := f.slotCaveats.erase newCell
    lifecycle := f.lifecycle.erase newCell
    deathCert := f.deathCert.erase newCell
    bal := f.bal.filterErase (fun key => decide ((ofLex key).1 = newCell)) }

/-! ## §6 — THE HEADLINE: `denote_finAllocCell`.

`some (denote (finAllocCell n f)) = interp (.allocCell n) (denote f)` — UNCONDITIONAL (no FiniteDiff, no
sparsity, no freshness side condition), mirroring `createCellIntoAsset`'s unconditionality. This DISCHARGES
R1's `hpres` gate for the `allocCell` constructor, closing the last of the 19 `RecStmt` constructors. -/
theorem denote_finAllocCell (n : RecordKernelState → CellId) (f : FinKernelState) :
    some (denote (finAllocCell n f)) = interp (.allocCell n) (denote f) := by
  simp only [interp]
  congr 1
  -- `denote (finAllocCell n f) = createCellIntoAsset (denote f) (n (denote f))`
  apply RecordKernelState.ext
  case cell =>
    funext c
    rw [show (denote (finAllocCell n f)).cell c = (f.cell.erase (n (denote f))).get c from rfl,
       CanonMap.get_erase]
    by_cases hc : c = n (denote f) <;>
      simp [hc, createCellIntoAsset, bornEmptyCellSlots, denote, default_value]
  case caps =>
    funext l
    rw [show (denote (finAllocCell n f)).caps l = (f.caps.erase (n (denote f))).get l from rfl,
       CanonMap.get_erase]
    rfl
  case delegate =>
    funext c
    rw [show (denote (finAllocCell n f)).delegate c = (f.delegate.erase (n (denote f))).lookup c from rfl,
       SortedMap.lookup_erase]
    rfl
  case delegations =>
    funext c
    rw [show (denote (finAllocCell n f)).delegations c = (f.delegations.erase (n (denote f))).get c from rfl,
       CanonMap.get_erase]
    rfl
  case slotCaveats =>
    funext c
    rw [show (denote (finAllocCell n f)).slotCaveats c = (f.slotCaveats.erase (n (denote f))).get c from rfl,
       CanonMap.get_erase]
    rfl
  case lifecycle =>
    funext c
    rw [show (denote (finAllocCell n f)).lifecycle c = (f.lifecycle.erase (n (denote f))).get c from rfl,
       CanonMap.get_erase]
    rfl
  case deathCert =>
    funext c
    rw [show (denote (finAllocCell n f)).deathCert c = (f.deathCert.erase (n (denote f))).get c from rfl,
       CanonMap.get_erase]
    rfl
  case bal =>
    funext c a
    rw [show (denote (finAllocCell n f)).bal c a
          = (f.bal.filterErase (fun key => decide ((ofLex key).1 = n (denote f)))).get (toLex (c, a)) from rfl,
       CanonMap.get_filterErase]
    show (if decide (c = n (denote f)) then (0 : ℤ) else f.bal.get (toLex (c, a)))
        = (createCellIntoAsset (denote f) (n (denote f))).bal c a
    by_cases hc : c = n (denote f)
    · simp [hc, createCellIntoAsset, bornEmptyCellSlots, denote]
    · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte, createCellIntoAsset,
        bornEmptyCellSlots] <;> rfl
  all_goals rfl

/-! ## §7 — coverage note (extends `FinInterp`'s `Pure`/`denote_finInterp` classification).

`FinInterp.Pure` excludes `allocCell` and `denote_finInterp` discharges it with `absurd h`. With
`denote_finAllocCell` proved here, `allocCell` is now REPRESENTABLE (like the §3/§3′/§6 whole-function writers
and `setCell`): it enters the `RecStmt` language as a `seq`-leaf whose square is `denote_finAllocCell`, and a
full `createCell`/`createCellFromFactory` program is the `seq` composition of a `guard` and this leaf (via the
committed `denote_seq_compose`). CRUCIALLY, unlike the seven whole-function writers (which each need a
FiniteDiff side condition) and `setCell` (a non-default sparsity side condition), `allocCell`'s square is
UNCONDITIONAL — matching `createCellIntoAsset`'s unconditionality. So the last open constructor closes with NO
new obligation, and `createCellStmt`/`createCellFromFactoryStmt` (Argus `Effects/CreateCell.lean`,
`Effects/CreateCellFromFactory.lean`, each a `seq (guard …) (allocCell …)`) are now UNBLOCKED. -/

/-- **`allocCell_representable`** — the `allocCell` square holds for EVERY `n` and `f`, with no side condition.
The precise statement of "`allocCell` is now representable" that `FinInterp`'s classification deferred. -/
theorem allocCell_representable (n : RecordKernelState → CellId) (f : FinKernelState) :
    some (denote (finAllocCell n f)) = interp (.allocCell n) (denote f) :=
  denote_finAllocCell n f

/-- **The full-program square** `seq (guard φ) (allocCell n)` — the exact `createCell`/`createCellFromFactory`
shape (privileged-creation `guard`, then the `allocCell` allocator) — assembled by the committed §4
`denote_seq_compose` from the `guard` leaf (via `finInterp`) and the `allocCell` leaf (via §6). This is R1's
`hpres` for the deployed account-allocation effect term. -/
theorem guardThenAlloc_square (φ : RecordKernelState → Bool) (n : RecordKernelState → CellId)
    (f : FinKernelState) :
    ((finInterp (.guard φ) f).bind (fun f => some (finAllocCell n f))).map denote
      = interp (.seq (.guard φ) (.allocCell n)) (denote f) :=
  denote_seq_compose
    (s := .guard φ) (t := .allocCell n)
    (sf := finInterp (.guard φ))
    (tf := fun f => some (finAllocCell n f))
    (fun g => denote_finInterp (.guard φ) trivial g)
    (fun g => by rw [Option.map_some]; exact denote_finAllocCell n g)
    f

/-! ## §8 — TEETH (`#guard`, both polarities). -/

section Teeth

/-- A concrete `bal` ledger: cell `1` holds asset `0 ↦ 5` and `1 ↦ 7`; cell `2` holds asset `0 ↦ 9`. Keys are
the lexicographic `BalKey`s, strictly increasing; no value is the default `0` (Canonical). -/
private def demoBal : CanonMap BalKey ℤ 0 :=
  ⟨⟨[(toLex (1, 0), 5), (toLex (1, 1), 7), (toLex (2, 0), 9)], by decide⟩, by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> decide⟩

/-- Predicate-erase the `(1, ·)` column. -/
private def demoBalErased : CanonMap BalKey ℤ 0 :=
  demoBal.filterErase (fun key => decide ((ofLex key).1 = (1 : CellId)))

-- The `(newCell = 1, ·)` COLUMN reads `0` after the erase (BOTH of cell 1's assets), while cell `2`'s balance
-- is UNTOUCHED — `filterErase` removes exactly the matching keys and preserves the others:
#guard demoBalErased.get (toLex (1, 0)) == 0    -- erased (cell 1, asset 0)
#guard demoBalErased.get (toLex (1, 1)) == 0    -- erased (cell 1, asset 1)
#guard demoBalErased.get (toLex (2, 0)) == 9    -- UNTOUCHED (cell 2)
#guard demoBal.get (toLex (1, 0)) == 5          -- before: cell 1 asset 0 was present
-- `filterErase` drops exactly the matching entries (only the single cell-2 entry survives):
#guard demoBalErased.toMap.entries.length == 1

-- A `filterErase` whose predicate matches NOTHING is the IDENTITY (opposite polarity):
#guard (demoBal.filterErase (fun _ => false)).toMap.entries.length == 3
#guard (demoBal.filterErase (fun _ => false)).get (toLex (1, 0)) == 5
#guard (demoBal.filterErase (fun _ => false)).get (toLex (1, 1)) == 7

/-- **The bal-column bridge bites (theorem form, both polarities).** After the predicate-erase the erased
column reads the default `0`, and an untouched cell keeps its value — the `get_filterErase` law, on the
concrete ledger, in both the match and non-match cases. -/
theorem demoBal_column_zeroed_others_kept :
    demoBalErased.get (toLex (1, 0)) = 0
    ∧ demoBalErased.get (toLex (1, 1)) = 0
    ∧ demoBalErased.get (toLex (2, 0)) = 9 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end Teeth

end Dregg2.Circuit.FinAllocCell
