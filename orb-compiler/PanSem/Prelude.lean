/-
  P3 bridge: the TRUSTED half of the HOL4 -> Lean 4 definitional translator
  for the Pancake semantics.  Together with `prim_const_tbl` and `pty` in
  DreggNet docs/engine/probes/p3-bridge/exporter/export2leanScript.sml this
  file is the cross-logic trust base (the CR-2 ledger row).  Every definition
  here is a model of a HOL4 concept; every one has a convention-splitting
  witness pair, proved on the HOL side by `EVAL` (DreggNet
  p3-bridge/audit/hol_eval_vectors.txt) and on the Lean side in
  GenVectors.lean against the same printed statement.  The rows that also
  carry a proved contract are in PanSem/Contracts.lean (generated: each
  contract is a HOL4 theorem printed by the row printer and re-proved here).

  Rows inherited from P2 (bool ↦ Prop classical, num ↦ Nat, char ↦ UInt8,
  string ↦ List UInt8, list/option/prod/sum) keep P2's soundness arguments.
  New rows:

  * `α |-> β` ↦ `FMap α β := α → Option β`.  The map φ f := FLOOKUP f is
    injective (HOL `fmap_EXT`/`FLOOKUP_EXT`) and commutes with FEMPTY,
    FUPDATE, DOMSUB and FUPDATE_LIST (the definitions below are the HOL
    lookup equations FLOOKUP_UPDATE, DOMSUB_FLOOKUP_THM, FLOOKUP_EMPTY and
    FUPDATE_LIST_THM read as definitions).  The Lean carrier is LARGER
    (infinite-domain maps); a universally quantified Lean theorem therefore
    specialises to HOL finite maps, an existential one need not.  No
    `FDOM`/`FCARD` row exists, so finiteness is never observable.
  * `MOD`, `DIV` ↦ Lean `%`, `/` (HOL4 defines `k MOD 0 = k`, `k DIV 0 = 0`:
    arithmetic `MOD_0`, `DIV_0`; Lean's Nat agrees; witnessed both sides).
  * `word_slice h l w` (HOL `(h '' l) w`, bits l..h INCLUSIVE) and
    `word_slice_alt h l w` (bits l ≤ i < h, EXCLUSIVE): the one-bit
    difference is the witness pair.
  * `combin$UPDATE a b f` (`(a =+ b) f`): later-applied (outer) update wins.
  * `list$ZIP`: HOL4's ZIP_def is TOTAL and truncates (ZIP ([],l) = [] and
    ZIP (l,[]) = []), so it is `List.zip` on the uncurried pair.
-/
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

namespace P3.Pan

/-- HOL4 `char`: exactly the 256 8-bit characters. -/
abbrev HolChar := UInt8

-- HOL4 string literals are emitted as explicit byte lists (no hstr row).


/-- HOL4 `ARB` at an inhabited type. -/
noncomputable opaque holARB {α : Type} [Inhabited α] : α

/-- HOL4 `α |-> β` (finite maps), modelled by their lookup function. -/
abbrev FMap (α β : Type) := α → Option β

/-- `FEMPTY`: FLOOKUP_EMPTY. -/
def FEMPTY {α β : Type} : FMap α β := fun _ => none

/-- `f |+ (k,v)`: FLOOKUP_UPDATE, `FLOOKUP (f |+ (k,v)) x = if x = k then SOME v else FLOOKUP f x`. -/
noncomputable def FUPDATE {α β : Type} (f : FMap α β) (p : α × β) : FMap α β :=
  fun x => if x = p.1 then some p.2 else f x

/-- `f \\ k`: DOMSUB_FLOOKUP_THM. -/
noncomputable def DOMSUB {α β : Type} (f : FMap α β) (k : α) : FMap α β :=
  fun x => if x = k then none else f x

/-- `f |++ l`: FUPDATE_LIST_THM, `f |++ (h::t) = (f |+ h) |++ t` (a left fold:
the LAST binding of a key wins). -/
noncomputable def FUPDATE_LIST {α β : Type} (f : FMap α β) (l : List (α × β)) : FMap α β :=
  l.foldl FUPDATE f

/-- `(a =+ b) f` (combin `UPDATE_def`: `UPDATE a b = λf c. if a = c then b else f c`). -/
noncomputable def UPDATE {α β : Type} (a : α) (b : β) (f : α → β) : α → β :=
  fun c => if a = c then b else f c

/-- HOL4 `(h '' l) w` (`word_slice_def`: `FCP i. l ≤ i ∧ i ≤ h ∧ w ' i`). -/
def word_slice {n : Nat} (h l : Nat) (w : BitVec n) : BitVec n :=
  BitVec.ofNat n (((w.toNat >>> l) % 2 ^ (h + 1 - l)) <<< l)

/-- HOL4 `word_slice_alt h l w` (`FCP i. l ≤ i ∧ i < h ∧ w ' i`). -/
def word_slice_alt {n : Nat} (h l : Nat) (w : BitVec n) : BitVec n :=
  BitVec.ofNat n (((w.toNat >>> l) % 2 ^ (h - l)) <<< l)

/-- HOL4 `list$EVERY` (bool reflected as Prop), same equations. -/
def EVERY {α : Type} (P : α → Prop) : List α → Prop
  | [] => True
  | x :: xs => P x ∧ EVERY P xs

/-- HOL4 `ZIP (l1,l2)` (total, truncating; ZIP_def). -/
def ZIP {α β : Type} (p : List α × List β) : List (α × β) := List.zip p.1 p.2

end P3.Pan
