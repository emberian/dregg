/-
# Dregg2.Circuit.Emit.KimchiTyp — a PUBLIC-INPUT LAYOUT DERIVED FROM A TYPE

## ⚑ WHAT THIS REPLACES

`KimchiPreimageCircuit` hand-wrote `preimagePublic : List Int` and hand-chose that the one public
word sits at `external 0`. `MinaWrapPublicInput.publicInputWords` is a hand-written slot list.
`PicklesRecursion.wrapStatementLayout : List (String × Nat)` is a hand-written census of names and
widths. **Nothing in the tree derived a layout from a type, and nothing refused a wrong one.**

The bug that costs the most is the one that shape cannot see. `MinaWrapPublicInput.lean:187-195`
records it in its own words: *"Slots 5-7 used to read `alpha, beta, gamma`. `Wrap.Statement.to_data`
(`composition_types.ml:826-880`) lays the `challenge` bucket down before the `scalar_challenge` one,
so they are **`beta, gamma, alpha`**."* (Slot 8, ζ, did not move.) And on the instruments: *"the
round trip in §3 is definitional … `publicInputWords_reads_every_field` is permutation-blind by
construction, and all three are 128-bit challenges so the width signature cannot separate them."*
The emitted object was right by luck of the transcript's squeeze order.

The sibling, from `KimchiWrapMainPins09.lean:216-218`: *"twenty exposed words carried the 255-bit
endo lift where `spec.ml:374-392` packs the raw 128-bit prechallenge, and the only word with a
different width was the only correct one, which is why nothing caught it."* — so "the outlier is the
bug" pointed at the one slot that was right.

## ⚑ WHAT MAKES THOSE IMPOSSIBLE HERE, AND WHAT DOES NOT

A layout that is *recorded* beside the emission repeats the bug in a new place. So there is exactly
**one** order in this file, and every consumer reads it off the same recursion:

    layout t          the slots, in emitted order, with their widths
    store t x         the field elements, in the SAME order
    read  t xs        the inverse, in the SAME order
    claims t base     the arena claims, in the SAME order

`layout`/`store`/`read`/`claims` are four recursions over one `Typ` constructor list. There is no
second place to disagree with. §4's `only_the_derived_layout_is_accepted` is the theorem that a
declaration which is not *literally* the derived layout is REFUSED — not "different", refused.

⚑ And §6 makes the reordering **derived rather than authored**: `structOf` takes the fields in the
**record's** order, each tagged with its `to_data` bucket, and computes the emitted order. The
author of `plonkFields` writes `alpha, beta, gamma, zeta` — the OCaml record's order — and the
layout comes out `beta, gamma, alpha, zeta`. Nobody writes the emitted order at all, which is why
nobody can write it wrong.

⚠ **Where the type stops carrying the width, say so.** `Typ.word w` denotes `Fin (2 ^ w)`: a raw
128-bit prechallenge and a 255-bit endo lift are *different types*, so substituting one for the
other does not typecheck, and if it is declared it is refused by width. `Typ.felt w` denotes `Nat` —
the host's canonical representative, whose range is the field's business (`PastaField`) and not the
layout's. `felt` buys the layout check only, **not** the type check. Slots that carry a challenge
must use `word`; `KimchiPreimageCircuit`'s digest slot uses `felt` because its canonicity is a
fact about `PastaPoseidon.Ref.perm` that nothing in this file proves.

## ⚑ THE CIRCUIT IS STILL A VALUE

`El` is a `Typ → Type` recursion and every operation is a pure fold; there is no `Typ` monad, no
`run`, no runtime configuration. `KimchiArena`'s note applies verbatim — a state monad would put the
layout behind a `run` and `decide` does not reach through one usefully. The array combinator is
`Typ.arr`, which **derives** an iterated product rather than adding a function-typed constructor, so
`decide` computes through an array layout the same way it computes through a pair. The `Fin n`
indexing is still there: `arrOfFn` / `arrGet`, with `arrGet_arrOfFn` as the law.

## ⚑ WHAT THIS DOES NOT DO

It does not know what a field element *is*, it does not constrain a value, and it emits no row. It
decides which slot a value occupies and how wide that slot is, and it refuses a declaration that
disagrees. The gate that the emitted circuit READS every public word is `KimchiPlacement`'s H2; the
gate that two slots never share a variable is `KimchiArena.alloc_injective`; §5 hands this layer's
slots to that allocator and §5's `derived_layouts_always_allocate` proves the handoff never refuses.
-/
import Dregg2.Tactics
import Dregg2.Circuit.Emit.KimchiPlacement
import Dregg2.Circuit.Emit.KimchiArena
import Dregg2.Circuit.Emit.KimchiAssertEqual

namespace Dregg2.Circuit.Emit.KimchiTyp

open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.KimchiArena

set_option autoImplicit false

/-! ## §1 — the universe: a `Typ` is a code, and `El` is what it denotes. -/

/-- One step of a path into a value. `fst`/`snd` come from `prod` and are what makes every leaf's
path DISTINCT (§5's `layout_paths_nodup`); `lbl`/`idx` are the author's names and are what makes a
refusal legible. -/
inductive Step where
  | fst
  | snd
  | lbl : String → Step
  | idx : Nat → Step
  deriving DecidableEq, Repr, Inhabited

/-- A path from the root of a value to one leaf. -/
abbrev Path := List Step

/-- **One public-input slot**: where it lives in the value, and how wide it is. Both are DERIVED;
neither is written by an author. -/
structure Slot where
  path : Path
  bits : Nat
  deriving DecidableEq, Repr, Inhabited

/-- **THE TYPE.** A closed code; `El` below is its denotation.

* `felt w` — a field element, `w` bits wide, denoted by `Nat`. The width is part of the type; the
  RANGE is not (see the header).
* `word w` — a `w`-bit word, denoted by `Fin (2 ^ w)`. ⚑ The width IS the type: a `word 128` is not
  a `word 255` and no coercion relates them.
* `bnd n` — a bounded scalar, denoted by `Fin n`, whose width is COMPUTED (`bitWidth n`).
* `prod` — the product combinator.
* `tag` — a name on a sub-tree; changes no denotation, only the derived path. -/
inductive Typ where
  | unit
  | felt : Nat → Typ
  | word : Nat → Typ
  | bnd  : Nat → Typ
  | prod : Typ → Typ → Typ
  | tag  : Step → Typ → Typ
  deriving DecidableEq, Repr, Inhabited

/-- The host type a `Typ` denotes. -/
@[reducible] def El : Typ → Type
  | .unit => Unit
  | .felt _ => Nat
  | .word w => Fin (2 ^ w)
  | .bnd n => Fin n
  | .prod a b => El a × El b
  | .tag _ t => El t

/-- Bits needed to hold every value `< n`, structurally (fuel = `n`), so it reduces in the kernel at
the small `n` a `bnd` is written with. ⚠ It is `O(n)` to reduce, so `bnd` is for small bounded
scalars — a full field element is `felt`, whose width is an argument. -/
def bitsAux : Nat → Nat → Nat
  | 0, _ => 0
  | _ + 1, 0 => 0
  | f + 1, n + 1 => 1 + bitsAux f ((n + 1) / 2)

/-- The derived width of `Fin n`. -/
def bitWidth (n : Nat) : Nat := bitsAux n (n - 1)

/-- The derived widths, exhibited: `Fin 1` needs no bit, `Fin 2` one, `Fin 3` and `Fin 4` two, and a
power of two needs its exponent. -/
theorem bitWidth_table :
    bitWidth 1 = 0 ∧ bitWidth 2 = 1 ∧ bitWidth 3 = 2 ∧ bitWidth 4 = 2 ∧ bitWidth 5 = 3
      ∧ bitWidth 16 = 4 ∧ bitWidth 256 = 8 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### §1a — the ARRAY combinator, derived.

⚑ `arr` is a `def` on `Typ`, not a constructor: an `n`-element array IS an `n`-fold product whose
elements carry `idx` tags. Nothing about `store`/`read`/`layout` changes, `decide` computes through
an array exactly as it computes through a pair, and the round trip in §3 covers arrays without a
single extra case. The `Fin n` interface is `arrOfFn`/`arrGet` and its law is `arrGet_arrOfFn`. -/

/-- `n` elements of `t`, tagged `idx i, idx (i+1), …`. -/
def Typ.arrFrom : Nat → Nat → Typ → Typ
  | _, 0, _ => .unit
  | i, n + 1, t => .prod (.tag (.idx i) t) (Typ.arrFrom (i + 1) n t)

/-- **THE ARRAY COMBINATOR.** -/
def Typ.arr (n : Nat) (t : Typ) : Typ := Typ.arrFrom 0 n t

/-- Build an array value from a `Fin n`-indexed function. ⚑ **The index is `Fin n`**, so an
out-of-range element is an elaboration error and not a runtime miss. -/
def arrOfFn (t : Typ) : (i n : Nat) → (Fin n → El t) → El (Typ.arrFrom i n t)
  | _, 0, _ => ()
  | i, n + 1, f => (f 0, arrOfFn t (i + 1) n (fun j => f j.succ))

/-- Read element `j` of an array value. -/
def arrGet (t : Typ) : (i n : Nat) → El (Typ.arrFrom i n t) → Fin n → El t
  | _, 0, _, j => j.elim0
  | i, n + 1, v, j => Fin.cases (motive := fun _ => El t) v.1 (fun k => arrGet t (i + 1) n v.2 k) j

/-- **THE `Fin n` LAW.** Building an array from a function and reading index `j` back gives `f j`,
for every `n`, every `i` and every `j` — general, not an instance. -/
theorem arrGet_arrOfFn (t : Typ) :
    ∀ (i n : Nat) (f : Fin n → El t) (j : Fin n), arrGet t i n (arrOfFn t i n f) j = f j
  | _, 0, _, j => j.elim0
  | i, n + 1, f, j => by
      refine Fin.cases ?_ ?_ j
      · rfl
      · intro k; exact arrGet_arrOfFn t (i + 1) n (fun j => f j.succ) k

/-! ## §2 — ⚑ THE LAYOUT, DERIVED.

One recursion. `store`, `read` and `claims` below are three more recursions over the SAME
constructor list in the SAME order, which is the entire reason a slot cannot end up in two places. -/

/-- The slots of `t`, in emitted order, under path prefix `pre`. -/
def layoutFrom : Path → Typ → List Slot
  | _, .unit => []
  | pre, .felt w => [⟨pre, w⟩]
  | pre, .word w => [⟨pre, w⟩]
  | pre, .bnd n => [⟨pre, bitWidth n⟩]
  | pre, .prod a b => layoutFrom (pre ++ [.fst]) a ++ layoutFrom (pre ++ [.snd]) b
  | pre, .tag s t => layoutFrom (pre ++ [s]) t

/-- **THE LAYOUT.** -/
def layout (t : Typ) : List Slot := layoutFrom [] t

/-- The number of public words a `Typ` occupies — the `pubSize` a circuit is placed at, derived
instead of written. -/
def pubSize (t : Typ) : Nat := (layout t).length

/-- The width signature — the instrument `MinaWrapPublicInput` had, kept here only so §6 can exhibit
what it is BLIND to. -/
def widths (t : Typ) : List Nat := (layout t).map (·.bits)

/-! ## §3 — `store` / `read`, and ⚑ THE ROUND TRIP, general over the type. -/

/-- **`store`** — a value to its field elements, in the derived order. -/
def store : (t : Typ) → El t → List Int
  | .unit, _ => []
  | .felt _, (x : Nat) => [(x : Int)]
  | .word _, x => [(x.val : Int)]
  | .bnd _, x => [(x.val : Int)]
  | .prod a b, x => store a x.1 ++ store b x.2
  | .tag _ t, x => store t x

/-- **`read`** — the inverse, consuming a prefix. ⚠ Every leaf REFUSES rather than truncating: a
short vector, a negative entry and an out-of-range word are all `none`, never a clamped value. -/
def read : (t : Typ) → List Int → Option (El t × List Int)
  | .unit, xs => some ((), xs)
  | .felt _, [] => none
  | .felt _, x :: rest => if 0 ≤ x then some (x.toNat, rest) else none
  | .word _, [] => none
  | .word w, x :: rest =>
      if h : x.toNat < 2 ^ w ∧ 0 ≤ x then some (⟨x.toNat, h.1⟩, rest) else none
  | .bnd _, [] => none
  | .bnd n, x :: rest =>
      if h : x.toNat < n ∧ 0 ≤ x then some (⟨x.toNat, h.1⟩, rest) else none
  | .prod a b, xs =>
      match read a xs with
      | none => none
      | some (u, xs') =>
        match read b xs' with
        | none => none
        | some (v, xs'') => some ((u, v), xs'')
  | .tag _ t, xs => read t xs

/-- **`readAll`** — the whole vector, with nothing left over. -/
def readAll (t : Typ) (xs : List Int) : Option (El t) :=
  match read t xs with
  | some (v, []) => some v
  | _ => none

/-- ⚑ **THE ROUND TRIP, GENERAL OVER THE TYPE.** `read` of `store` is the identity, for every `Typ`,
every value and every trailing remainder — proved by induction on the code, not decided at an
instance. -/
theorem read_store : ∀ (t : Typ) (x : El t) (rest : List Int),
    read t (store t x ++ rest) = some (x, rest) := by
  intro t
  induction t with
  | unit => intro x rest; cases x; rfl
  | felt w =>
      intro x rest
      simp only [store, List.singleton_append]
      rw [read, if_pos (Int.natCast_nonneg _)]
      simp
  | word w =>
      intro x rest
      simp only [store, List.singleton_append]
      rw [read, dif_pos (by simp)]
      simp
  | bnd n =>
      intro x rest
      simp only [store, List.singleton_append]
      rw [read, dif_pos (by simp [x.isLt])]
      simp
  | prod a b iha ihb =>
      intro x rest
      show read (.prod a b) (store a x.1 ++ store b x.2 ++ rest) = _
      rw [List.append_assoc, read, iha]
      dsimp only
      rw [ihb]
  | tag s t ih => intro x rest; exact ih x rest

/-- The whole-vector corollary. -/
theorem readAll_store (t : Typ) (x : El t) : readAll t (store t x) = some x := by
  have h := read_store t x []
  rw [List.append_nil] at h
  simp only [readAll, h]

/-- ⚑ **AND THE OTHER DIRECTION: WHATEVER `read` ACCEPTS, `store` RE-EMITS IDENTICALLY.** Nothing
the layout accepts can carry a byte the layout would not have produced — which is what makes a
vector of the wrong length or shape a REFUSAL rather than a silent truncation. -/
theorem store_read : ∀ (t : Typ) (xs : List Int) (v : El t) (rest : List Int),
    read t xs = some (v, rest) → xs = store t v ++ rest := by
  intro t
  induction t with
  | unit =>
      intro xs v rest h
      cases v
      simp only [read, Option.some.injEq, Prod.mk.injEq] at h
      simp [store, h.2]
  | felt w =>
      intro xs v rest h
      cases xs with
      | nil => simp [read] at h
      | cons x xs =>
          rw [read] at h
          split at h
          · rename_i hx
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            simp only [store, List.singleton_append, ← h.1, ← h.2, Int.toNat_of_nonneg hx]
          · exact absurd h (by simp)
  | word w =>
      intro xs v rest h
      cases xs with
      | nil => simp [read] at h
      | cons x xs =>
          rw [read] at h
          split at h
          · rename_i hx
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            simp only [store, List.singleton_append, ← h.2]
            rw [← h.1]
            simp [Int.toNat_of_nonneg hx.2]
          · exact absurd h (by simp)
  | bnd n =>
      intro xs v rest h
      cases xs with
      | nil => simp [read] at h
      | cons x xs =>
          rw [read] at h
          split at h
          · rename_i hx
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            simp only [store, List.singleton_append, ← h.2]
            rw [← h.1]
            simp [Int.toNat_of_nonneg hx.2]
          · exact absurd h (by simp)
  | prod a b iha ihb =>
      intro xs v rest h
      rw [read] at h
      split at h
      · exact absurd h (by simp)
      · rename_i u xs' hu
        split at h
        · exact absurd h (by simp)
        · rename_i w xs'' hw
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hv, hr⟩ := h
          subst hv
          subst hr
          rw [iha xs u xs' hu, ihb xs' w xs'' hw]
          show store a u ++ (store b w ++ xs'') = store (Typ.prod a b) (u, w) ++ xs''
          simp [store, List.append_assoc]
  | tag s t ih => intro xs v rest h; exact ih xs v rest h

/-- ⚑ **`store` FILLS EXACTLY THE DERIVED SLOTS** — one field element per slot, for every type and
every value. This is the count side of "alloc then store fills exactly the allocated slots"; §5
supplies the variable side. -/
theorem store_length : ∀ (t : Typ) (x : El t), (store t x).length = (layout t).length := by
  have key : ∀ (t : Typ) (x : El t) (pre : Path),
      (store t x).length = (layoutFrom pre t).length := by
    intro t
    induction t with
    | unit => intro x pre; rfl
    | felt w => intro x pre; rfl
    | word w => intro x pre; rfl
    | bnd n => intro x pre; rfl
    | prod a b iha ihb =>
        intro x pre
        show (store a x.1 ++ store b x.2).length = _
        simp only [layoutFrom, List.length_append]
        rw [iha x.1 (pre ++ [Step.fst]), ihb x.2 (pre ++ [Step.snd])]
    | tag s t ih => intro x pre; exact ih x (pre ++ [s])
  intro t x; exact key t x []

/-! ## §4 — ⚑ `check`: a WRONG LAYOUT IS REFUSED, NOT MERELY DIFFERENT. -/

/-- Why a declared layout was REFUSED. -/
inductive Refusal where
  /-- The declaration has a different number of slots than the type. -/
  | arity (declared derived : Nat)
  /-- ⚑ **The `alpha β γ ζ` refusal.** Slot `pos` names a different leaf than the type puts there.
  Widths cannot see this when the reordered slots are the same width, which is exactly why
  `MinaWrapPublicInput` shipped it. -/
  | order (pos : Nat) (declared derived : Path)
  /-- ⚑ **The endo-lift refusal.** Right leaf, wrong width. -/
  | width (pos : Nat) (path : Path) (declared derived : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Walk the two layouts together, reporting the FIRST divergence and its position. -/
def checkAt : Nat → List Slot → List Slot → Except Refusal Unit
  | _, [], [] => .ok ()
  | pos, d :: ds, e :: es =>
      if d.path ≠ e.path then .error (.order pos d.path e.path)
      else if d.bits ≠ e.bits then .error (.width pos e.path d.bits e.bits)
      else checkAt (pos + 1) ds es
  | _, ds, es => .error (.arity ds.length es.length)

/-- **THE CHECK.** A declared layout against the one the type derives. -/
def check (declared : List Slot) (t : Typ) : Except Refusal Unit :=
  if declared.length ≠ (layout t).length then
    .error (.arity declared.length (layout t).length)
  else checkAt 0 declared (layout t)

theorem checkAt_nil_cons (pos : Nat) (e : Slot) (es : List Slot) :
    checkAt pos [] (e :: es) = .error (.arity 0 (e :: es).length) := rfl

theorem checkAt_cons_nil (pos : Nat) (d : Slot) (ds : List Slot) :
    checkAt pos (d :: ds) [] = .error (.arity (d :: ds).length 0) := rfl

theorem checkAt_ok_iff : ∀ (pos : Nat) (ds es : List Slot),
    checkAt pos ds es = .ok () ↔ ds = es := by
  intro pos ds
  induction ds generalizing pos with
  | nil =>
      intro es
      cases es with
      | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
      | cons e es =>
          refine ⟨fun h => ?_, fun h => by simp at h⟩
          rw [checkAt_nil_cons] at h
          simp at h
  | cons d ds ih =>
      intro es
      cases es with
      | nil =>
          refine ⟨fun h => ?_, fun h => by simp at h⟩
          rw [checkAt_cons_nil] at h
          simp at h
      | cons e es =>
          rw [checkAt]
          by_cases hp : d.path ≠ e.path
          · rw [if_pos hp]
            refine ⟨fun h => by simp at h, fun h => ?_⟩
            exact absurd (congrArg Slot.path (List.cons.inj h).1) hp
          · rw [if_neg hp]
            by_cases hb : d.bits ≠ e.bits
            · rw [if_pos hb]
              refine ⟨fun h => by simp at h, fun h => ?_⟩
              exact absurd (congrArg Slot.bits (List.cons.inj h).1) hb
            · rw [if_neg hb, ih (pos + 1) es]
              have hd : d = e := by
                cases d; cases e
                simp only [Slot.mk.injEq]
                exact ⟨not_not.mp hp, not_not.mp hb⟩
              simp [hd]

/-- ⚑ **ONLY THE DERIVED LAYOUT IS ACCEPTED.** Not "the check passes on the right one" — the check
passes on the right one **and on nothing else**, for every type and every declaration. This is the
theorem `wrapStatementLayout : List (String × Nat)` cannot have: a hand-written census is not
compared against anything. -/
theorem only_the_derived_layout_is_accepted (declared : List Slot) (t : Typ) :
    check declared t = .ok () ↔ declared = layout t := by
  unfold check
  by_cases h : declared.length ≠ (layout t).length
  · rw [if_pos h]
    refine ⟨fun hc => by simp at hc, fun hd => absurd (by rw [hd]) h⟩
  · rw [if_neg h]
    exact checkAt_ok_iff 0 declared (layout t)

/-- The contrapositive, as the sentence the campaign asked for. -/
theorem a_wrong_layout_is_refused (declared : List Slot) (t : Typ)
    (h : declared ≠ layout t) : (check declared t).isOk = false := by
  cases hc : check declared t with
  | error e => rfl
  | ok u =>
      cases u
      exact absurd ((only_the_derived_layout_is_accepted declared t).1 hc) h

/-! ## §5 — `alloc`: the layout's slots, handed to `KimchiArena`.

The slot type is `Path` — DERIVED from the code, so a misnamed slot is not a possible input.
`KimchiArena.alloc_injective` then says two distinct slots never share a `PVar`, and
`derived_layouts_always_allocate` says the handoff never refuses. -/

/-- The claims a layout makes: slot `i` takes `external (base + i)`. Written by recursion rather
than by `zipIdx` so the fold in `allocFrom_claimsFrom` is structural. -/
def claimsFrom : Nat → List Slot → List (Claim Path)
  | _, [] => []
  | base, s :: ss => .extAt s.path base :: claimsFrom (base + 1) ss

/-- **THE CLAIM LIST**, derived. -/
def claims (t : Typ) (base : Nat) : List (Claim Path) := claimsFrom base (layout t)

/-- The bindings those claims make, as a value: slot `i` ↦ `external (base + i)`. -/
def bindingsFrom : Nat → List Slot → List (Path × PVar)
  | _, [] => []
  | base, s :: ss => (s.path, .external base) :: bindingsFrom (base + 1) ss

theorem claimsFrom_length : ∀ (base : Nat) (ss : List Slot),
    (claimsFrom base ss).length = ss.length
  | _, [] => rfl
  | base, _ :: ss => by simp [claimsFrom, claimsFrom_length (base + 1) ss]

/-- ⚑ **ONE CLAIM PER SLOT, ONE FIELD ELEMENT PER CLAIM.** "alloc then store fills exactly the
allocated slots", as a count, general over the type and the value. -/
theorem alloc_and_store_agree (t : Typ) (base : Nat) (x : El t) :
    (claims t base).length = (layout t).length
      ∧ (claims t base).length = (store t x).length := by
  refine ⟨claimsFrom_length base (layout t), ?_⟩
  rw [claims, claimsFrom_length, store_length]

/-! ### §5a — every derived layout has DISTINCT slots. -/

/-- Every slot of `layoutFrom pre t` sits under `pre`. -/
theorem layoutFrom_prefix : ∀ (t : Typ) (pre : Path) (s : Slot),
    s ∈ layoutFrom pre t → ∃ tl, s.path = pre ++ tl := by
  intro t
  induction t with
  | unit => intro pre s hs; simp [layoutFrom] at hs
  | felt w => intro pre s hs; simp only [layoutFrom, List.mem_singleton] at hs; exact ⟨[], by simp [hs]⟩
  | word w => intro pre s hs; simp only [layoutFrom, List.mem_singleton] at hs; exact ⟨[], by simp [hs]⟩
  | bnd n => intro pre s hs; simp only [layoutFrom, List.mem_singleton] at hs; exact ⟨[], by simp [hs]⟩
  | prod a b iha ihb =>
      intro pre s hs
      rw [layoutFrom, List.mem_append] at hs
      rcases hs with hs | hs
      · obtain ⟨tl, htl⟩ := iha (pre ++ [.fst]) s hs
        exact ⟨Step.fst :: tl, by simp [htl]⟩
      · obtain ⟨tl, htl⟩ := ihb (pre ++ [.snd]) s hs
        exact ⟨Step.snd :: tl, by simp [htl]⟩
  | tag st t ih =>
      intro pre s hs
      obtain ⟨tl, htl⟩ := ih (pre ++ [st]) s hs
      exact ⟨st :: tl, by simp [htl]⟩

/-- ⚑ **A DERIVED LAYOUT NEVER REPEATS A SLOT** — for every type, without a side condition. The
`prod` combinator separates its two halves by a `fst`/`snd` step, so two leaves of one value cannot
share a path however the author tags them. -/
theorem layout_paths_nodup : ∀ (t : Typ) (pre : Path),
    ((layoutFrom pre t).map (·.path)).Nodup := by
  intro t
  induction t with
  | unit => intro pre; simp [layoutFrom]
  | felt w => intro pre; simp [layoutFrom]
  | word w => intro pre; simp [layoutFrom]
  | bnd n => intro pre; simp [layoutFrom]
  | prod a b iha ihb =>
      intro pre
      rw [layoutFrom, List.map_append]
      refine List.Nodup.append (iha _) (ihb _) ?_
      intro p hp hq
      simp only [List.mem_map] at hp hq
      obtain ⟨s1, hs1, he1⟩ := hp
      obtain ⟨s2, hs2, he2⟩ := hq
      obtain ⟨tl, htl⟩ := layoutFrom_prefix a (pre ++ [Step.fst]) s1 hs1
      obtain ⟨tl', htl'⟩ := layoutFrom_prefix b (pre ++ [Step.snd]) s2 hs2
      have hcl : (pre ++ [Step.fst]) ++ tl = (pre ++ [Step.snd]) ++ tl' := by
        rw [← htl, ← htl', he1, he2]
      simp at hcl
  | tag st t ih => intro pre; exact ih (pre ++ [st])

/-! ### §5b — the allocation itself. -/

theorem allocFrom_claimsFrom : ∀ (ss : List Slot) (base : Nat) (a : Arena Path),
    (ss.map (·.path)).Nodup →
    (∀ s ∈ ss, a.hasName s.path = false) →
    (∀ i, PVar.external i ∈ a.vars → i < base) →
    ∃ b : Arena Path,
      allocFrom a (claimsFrom base ss) = .ok b
        ∧ b.bind = (bindingsFrom base ss).reverse ++ a.bind := by
  intro ss
  induction ss with
  | nil => intro base a _ _ _; exact ⟨a, rfl, by simp [bindingsFrom]⟩
  | cons s ss ih =>
      intro base a hnd hfresh hvar
      have hname : a.hasName s.path = false := hfresh s (by simp)
      have hvarf : a.hasVar (PVar.external base) = false := by
        by_contra hc
        rw [Bool.not_eq_false] at hc
        exact absurd (hvar base ((hasVar_iff a _).1 hc)) (by omega)
      have hstep : step a (Claim.extAt s.path base)
          = .ok { bind := (s.path, PVar.external base) :: a.bind
                , nExt := max a.nExt (base + 1), nInt := a.nInt } := by
        simp only [step, Arena.bindAt, hname, hvarf, Bool.false_eq_true, if_false]
      set a' : Arena Path :=
        { bind := (s.path, PVar.external base) :: a.bind
        , nExt := max a.nExt (base + 1), nInt := a.nInt } with ha'
      have hnd2 : (∀ x ∈ ss, x.path ≠ s.path) ∧ ((ss.map (·.path)).Nodup) := by simpa using hnd
      have hnd' : (ss.map (·.path)).Nodup := hnd2.2
      have hfresh' : ∀ s' ∈ ss, a'.hasName s'.path = false := by
        intro s' hs'
        have hne : s'.path ≠ s.path := hnd2.1 s' hs'
        have hbase : a.hasName s'.path = false := hfresh s' (List.mem_cons_of_mem s hs')
        by_contra hc
        rw [Bool.not_eq_false] at hc
        have hm := (hasName_iff a' s'.path).1 hc
        simp only [ha', Arena.names, List.map_cons, List.mem_cons] at hm
        rcases hm with hm | hm
        · exact hne hm
        · rw [(hasName_iff a s'.path).2 hm] at hbase; exact Bool.noConfusion hbase
      have hvar' : ∀ i, PVar.external i ∈ a'.vars → i < base + 1 := by
        intro i hi
        simp only [ha', Arena.vars, List.map_cons, List.mem_cons] at hi
        rcases hi with hi | hi
        · injection hi with hi; omega
        · have := hvar i hi; omega
      obtain ⟨b, hb, hbind⟩ := ih (base + 1) a' hnd' hfresh' hvar'
      refine ⟨b, ?_, ?_⟩
      · simp only [claimsFrom, allocFrom, hstep, Except.bind]
        exact hb
      · rw [hbind, ha', bindingsFrom, List.reverse_cons, List.append_assoc]
        rfl

/-- ⚑ **A DERIVED LAYOUT ALWAYS ALLOCATES** — for every type and every base. The allocator's
refusals (`nameTaken`, `varTaken`) exist for HAND-PICKED ids; a layout that came out of a type can
never trip them, and that is the whole difference between the two authoring styles. -/
theorem derived_layouts_always_allocate (t : Typ) (base : Nat) :
    ∃ a : Arena Path,
      alloc (claims t base) = .ok a
        ∧ a.bind = (bindingsFrom base (layout t)).reverse := by
  obtain ⟨a, ha, hbind⟩ :=
    allocFrom_claimsFrom (layout t) base {}
      (layout_paths_nodup t []) (fun _ _ => by simp [Arena.hasName, Arena.names])
      (fun _ h => by simp [Arena.vars] at h)
  exact ⟨a, ha, by rw [hbind]; simp⟩

/-- Slot `i` of a derived layout denotes `external (base + i)`. -/
theorem bindingsFrom_mem : ∀ (ss : List Slot) (base i : Nat) (h : i < ss.length),
    ((ss[i]'h).path, PVar.external (base + i)) ∈ bindingsFrom base ss := by
  intro ss
  induction ss with
  | nil => intro base i h; simp at h
  | cons s ss ih =>
      intro base i h
      cases i with
      | zero => simp [bindingsFrom]
      | succ i =>
          have hi : i < ss.length := by simpa using h
          have := ih (base + 1) i hi
          simp only [bindingsFrom, List.mem_cons]
          right
          have hb : base + 1 + i = base + (i + 1) := by omega
          rw [hb] at this
          simpa using this

/-! ### §5c — ⚑ WIRING A GATE BY NAME.

A gate list writes `List (Option PVar)`. `varOf` is what it should write instead of a typed-in id:
the variable a slot occupies, looked up by PATH. ⚑ The `Option` is not an inconvenience, it is the
refusal — a path that is not a leaf of the type resolves to `none`, an UNWIRED cell, and a public
word no gate wires is what `KimchiPlacement`'s H2 (`inertPublicWord`) already refuses. A misspelled
wire therefore cannot reach an artifact, and it needs no new check to stop it. -/

def varOfFrom : Nat → List Slot → Path → Option PVar
  | _, [], _ => none
  | base, s :: ss, p => if s.path = p then some (.external base) else varOfFrom (base + 1) ss p

/-- **THE VARIABLE OF A SLOT, BY NAME.** -/
def varOf (t : Typ) (base : Nat) (p : Path) : Option PVar := varOfFrom base (layout t) p

theorem varOfFrom_mem_bindings : ∀ (ss : List Slot) (base : Nat) (p : Path) (v : PVar),
    varOfFrom base ss p = some v → (p, v) ∈ bindingsFrom base ss := by
  intro ss
  induction ss with
  | nil => intro base p v h; exact absurd h (by simp [varOfFrom])
  | cons s ss ih =>
      intro base p v h
      rw [varOfFrom] at h
      by_cases hp : s.path = p
      · rw [if_pos hp] at h
        rw [← Option.some.inj h, ← hp]
        simp [bindingsFrom]
      · rw [if_neg hp] at h
        exact List.mem_cons_of_mem _ (ih (base + 1) p v h)

/-- ⚑ **THE VARIABLE A GATE WRITES IS THE VARIABLE THE ARENA HANDED OUT.** Not "the same number by
convention" — the same binding, in the arena `alloc` produced, where `alloc_injective` says no other
slot can hold it and `alloc_functional` says this slot holds nothing else. -/
theorem the_wired_variable_is_the_allocated_one (t : Typ) (base : Nat) (p : Path) (v : PVar)
    (h : varOf t base p = some v) {a : Arena Path} (ha : alloc (claims t base) = .ok a) :
    (p, v) ∈ a.bind := by
  obtain ⟨a', ha', hbind⟩ := derived_layouts_always_allocate t base
  rw [ha] at ha'
  have haa : a = a' := Except.ok.inj ha'
  rw [haa, hbind, List.mem_reverse]
  exact varOfFrom_mem_bindings (layout t) base p v h

/-- ⚑ **AND A PATH THAT IS NOT A LEAF RESOLVES TO NOTHING** — general: `varOf` only ever returns a
variable for a path the layout actually contains. -/
theorem varOfFrom_some_implies_mem : ∀ (ss : List Slot) (base : Nat) (p : Path) (v : PVar),
    varOfFrom base ss p = some v → p ∈ ss.map (·.path) := by
  intro ss
  induction ss with
  | nil => intro base p v h; exact absurd h (by simp [varOfFrom])
  | cons s ss ih =>
      intro base p v h
      rw [varOfFrom] at h
      by_cases hp : s.path = p
      · simp [hp]
      · rw [if_neg hp] at h
        exact List.mem_cons_of_mem _ (ih (base + 1) p v h)

theorem varOf_none_of_not_a_leaf (t : Typ) (base : Nat) (p : Path)
    (h : p ∉ (layout t).map (·.path)) : varOf t base p = none := by
  cases hv : varOf t base p with
  | none => rfl
  | some v => exact absurd (varOfFrom_some_implies_mem (layout t) base p v hv) h

/-- ⚑ **AND THE VARIABLE SIDE OF "ALLOC THEN STORE FILLS EXACTLY THE ALLOCATED SLOTS":** slot `i` of
the derived layout — the slot the `i`-th field element of `store` lands in — is bound by the arena
to `external (base + i)`. `KimchiArena.alloc_functional` makes that binding the only one for that
slot, and `alloc_injective` makes it the only slot for that variable. -/
theorem the_ith_slot_is_the_ith_variable (t : Typ) (base i : Nat) (h : i < (layout t).length)
    {a : Arena Path} (ha : alloc (claims t base) = .ok a) :
    (((layout t)[i]'h).path, PVar.external (base + i)) ∈ a.bind := by
  obtain ⟨a', ha', hbind⟩ := derived_layouts_always_allocate t base
  rw [ha] at ha'
  have : a = a' := Except.ok.inj ha'
  rw [this, hbind, List.mem_reverse]
  exact bindingsFrom_mem (layout t) base i h

/-! ### §5d — ⚑ THE HOST↔CIRCUIT INTERFACE, DERIVED.

`WitnessBuilder.lean:202` is `abbrev VarEnv := List (PVar × Int)` — the assignment a host hands the
circuit, written by hand today. It is `claims` and `store` zipped, and because both come off the
same `layout` recursion the pairing cannot slip. -/

def varEnvFrom : Nat → List Slot → List Int → List (PVar × Int)
  | _, [], _ => []
  | _, _ :: _, [] => []
  | base, _ :: ss, v :: vs => (PVar.external base, v) :: varEnvFrom (base + 1) ss vs

/-- **THE ASSIGNMENT**, from a value. -/
def varEnv (t : Typ) (base : Nat) (x : El t) : List (PVar × Int) :=
  varEnvFrom base (layout t) (store t x)

theorem varEnvFrom_length : ∀ (ss : List Slot) (vs : List Int) (base : Nat),
    ss.length = vs.length → (varEnvFrom base ss vs).length = ss.length := by
  intro ss
  induction ss with
  | nil => intro vs base _; rfl
  | cons s ss ih =>
      intro vs base hlen
      cases vs with
      | nil => exact absurd hlen (by simp)
      | cons v vs =>
          simp only [varEnvFrom, List.length_cons]
          rw [ih vs (base + 1) (by simpa using hlen)]

/-- One assignment per public word. -/
theorem varEnv_length (t : Typ) (base : Nat) (x : El t) :
    (varEnv t base x).length = pubSize t :=
  varEnvFrom_length (layout t) (store t x) base (store_length t x).symm

theorem varEnvFrom_map_fst : ∀ (ss : List Slot) (vs : List Int) (base : Nat),
    ss.length = vs.length →
    (varEnvFrom base ss vs).map Prod.fst = (bindingsFrom base ss).map Prod.snd := by
  intro ss
  induction ss with
  | nil => intro vs base _; rfl
  | cons s ss ih =>
      intro vs base hlen
      cases vs with
      | nil => exact absurd hlen (by simp)
      | cons v vs =>
          simp only [varEnvFrom, bindingsFrom, List.map_cons]
          rw [ih vs (base + 1) (by simpa using hlen)]

/-- ⚑ **THE VARIABLES THE HOST ASSIGNS ARE THE VARIABLES THE ARENA ALLOCATED, IN ORDER.** Not "the
same numbers by convention" — the same list, off the same layout. A host that fed values positionally
into a hand-written variable list is the shape `MinaWrapPublicInput` had; this is what replaces it. -/
theorem the_assignment_is_the_allocation (t : Typ) (base : Nat) (x : El t) :
    (varEnv t base x).map Prod.fst = (bindingsFrom base (layout t)).map Prod.snd :=
  varEnvFrom_map_fst (layout t) (store t x) base (store_length t x).symm

/-! ## §6 — ⚑ THE TWO BUGS, REFUSED.

`MinaWrapPublicInput` and `PicklesRecursion` are NOT imported: nothing here re-authors those files,
and nothing here is evidence about the objects they emit. What is reconstructed is the SHAPE of the
two defects, so the refusal can be exhibited on it. -/

/-- `Wrap.Statement.to_data`'s buckets (`composition_types.ml:814-943`, `Spec.T.Struct`). A field
declares WHICH bucket it is in; it never declares WHERE it lands. -/
inductive Bucket where
  | fp | challenge | scalarChallenge | digest | bulletproof | branchData | featureFlag
  deriving DecidableEq, Repr, Inhabited

/-- The bucket order `to_data` lays down. -/
def bucketOrder : List Bucket :=
  [.fp, .challenge, .scalarChallenge, .digest, .bulletproof, .branchData, .featureFlag]

/-- One field of a statement: the RECORD's name, its bucket, its type. -/
structure Field where
  name : String
  bucket : Bucket
  typ : Typ
  deriving Repr, Inhabited

/-- ⚑ **`to_data`, AS A FUNCTION.** A stable partition into `bucketOrder`, folded into a product.
The author supplies the fields in the RECORD's order; the emitted order comes out of here. **Nobody
writes the emitted order**, which is why nobody can write it wrong. -/
def structOf (fs : List Field) : Typ :=
  (bucketOrder.flatMap (fun b => fs.filter (fun f => decide (f.bucket = b)))).foldr
    (fun f acc => .prod (.tag (.lbl f.name) f.typ) acc) .unit

/-- The four `plonk` challenges of a Wrap statement, **in the OCaml record's order** — `alpha`
first, exactly as `MinaWrapPublicInput`'s census read them. All four are 128-bit
`ScalarChallenge`/`Challenge`s. -/
def plonkFields : List Field :=
  [ ⟨"alpha", .scalarChallenge, .word 128⟩
  , ⟨"beta",  .challenge,       .word 128⟩
  , ⟨"gamma", .challenge,       .word 128⟩
  , ⟨"zeta",  .scalarChallenge, .word 128⟩ ]

def plonkTyp : Typ := structOf plonkFields

/-- The layout an author would WRITE from the record — `alpha, beta, gamma, zeta`. This is the
census `MinaWrapPublicInput` carried before its 2026-07-30 correction, in this layer's shape. -/
def plonkCensusAsWritten : List Slot :=
  [ ⟨[.fst, .lbl "alpha"], 128⟩
  , ⟨[.snd, .fst, .lbl "beta"], 128⟩
  , ⟨[.snd, .snd, .fst, .lbl "gamma"], 128⟩
  , ⟨[.snd, .snd, .snd, .fst, .lbl "zeta"], 128⟩ ]

/-- ⚑ **THE EMITTED ORDER IS DERIVED, AND IT IS NOT THE RECORD'S.** `plonkFields` says
`alpha, beta, gamma, zeta`; `to_data` lays the `challenge` bucket down before the
`scalar_challenge` one, so the slots come out **`beta, gamma, alpha, zeta`**. -/
theorem the_emitted_order_is_beta_gamma_alpha_zeta :
    (layout plonkTyp).map (fun s => s.path.getLast? ) =
      [some (.lbl "beta"), some (.lbl "gamma"), some (.lbl "alpha"), some (.lbl "zeta")] := by
  decide

/-- ⚑ **AND THE WIDTH SIGNATURE IS BLIND TO IT.** The census-as-written and the derived layout have
IDENTICAL widths — four 128-bit slots — which is `MinaWrapPublicInput`'s own account of why every
instrument it had missed this: *"all three are 128-bit challenges so the width signature cannot
separate them."* -/
theorem the_width_signature_cannot_separate_them :
    plonkCensusAsWritten.map (·.bits) = widths plonkTyp := by decide

/-- ⚑ **AND THE LAYOUT CHECK REFUSES IT AT SLOT 0**, naming the leaf that was claimed and the leaf
the type puts there. This is the instrument that did not exist. -/
theorem the_record_order_census_is_refused :
    check plonkCensusAsWritten plonkTyp
      = .error (.order 0 [.fst, .lbl "alpha"] [.fst, .lbl "beta"]) := by decide

/-- …and the derived layout is accepted, so the check is discriminating and not a refusal of
everything. -/
theorem the_derived_plonk_layout_is_accepted :
    check (layout plonkTyp) plonkTyp = .ok () := by decide

/-! ### §6a — the ENDO-LIFT bug: right leaf, wrong width. -/

/-- Sixteen deferred bulletproof challenges. `spec.ml:374-392` packs `Bulletproof_challenge` at
`Challenge.length = 128` — the RAW prechallenge. (The historical defect was twenty words wide; the
sixteen here are the same shape and the same refusal.) -/
def bpChallenges : Typ := Typ.arr 16 (.word 128)

/-- The same sixteen slots as they were once carried: the ENDO LIFT, a full 255-bit field element.
⚑ In this layer that is a different TYPE — `El (.word 128) = Fin (2^128)` and
`El (.word 255) = Fin (2^255)` — so the substitution does not typecheck at `store`. Declared, it is
refused. -/
def bpChallengesEndoLifted : Typ := Typ.arr 16 (.word 255)

theorem the_endo_lift_is_a_different_layout : layout bpChallengesEndoLifted ≠ layout bpChallenges :=
  by decide

/-- ⚑ **THE WIDTH REFUSAL**, at slot 0, naming the leaf and both widths. -/
theorem the_endo_lift_is_refused_by_width :
    check (layout bpChallengesEndoLifted) bpChallenges
      = .error (.width 0 [.fst, .idx 0] 255 128) := by decide

/-- ⚑ **AND THE "ODD ONE OUT" HEURISTIC POINTED AT THE WORD THAT WAS RIGHT.** The historical shape,
at sixteen: fifteen slots endo-lifted and ONE left raw. The unique width in the declaration is the
128 — the only correct slot — so an instrument that flags the outlier flags slot 15 and clears slots
0-14. The derived check refuses at slot 0, which is where the defect actually starts. -/
def bpChallengesAllButOneLifted : List Slot :=
  (layout bpChallengesEndoLifted).set 15 (((layout bpChallenges)[15]!))

theorem the_outlier_is_the_only_correct_slot :
    (bpChallengesAllButOneLifted.map (·.bits)).count 128 = 1
      ∧ (bpChallengesAllButOneLifted.map (·.bits)).count 255 = 15
      ∧ bpChallengesAllButOneLifted[15]! = (layout bpChallenges)[15]! := by
  refine ⟨by decide, by decide, by decide⟩

theorem the_derived_check_refuses_at_slot_zero_not_at_the_outlier :
    check bpChallengesAllButOneLifted bpChallenges
      = .error (.width 0 [.fst, .idx 0] 255 128) := by decide

/-! ### §6b — a whole statement, derived end to end. -/

/-- A Wrap-shaped statement in the RECORD's order, every field tagged with its bucket. -/
def wrapShapedFields : List Field :=
  [ ⟨"alpha", .scalarChallenge, .word 128⟩
  , ⟨"beta",  .challenge,       .word 128⟩
  , ⟨"gamma", .challenge,       .word 128⟩
  , ⟨"zeta",  .scalarChallenge, .word 128⟩
  , ⟨"combined_inner_product", .fp, .felt 255⟩
  , ⟨"b", .fp, .felt 255⟩
  , ⟨"branch_data", .branchData, .bnd 1024⟩
  , ⟨"bulletproof_challenges", .bulletproof, bpChallenges⟩
  , ⟨"sponge_digest", .digest, .felt 255⟩ ]

def wrapShapedTyp : Typ := structOf wrapShapedFields

/-- ⚑ **THE WHOLE LAYOUT IS ONE NUMBER AND ONE ORDER, BOTH DERIVED.** Two `fp` words, then the two
`challenge`s, then the two `scalar_challenge`s, then the digest, then sixteen bulletproof
challenges, then the branch-data word: 24 slots, in an order no author wrote. -/
theorem the_wrap_shaped_layout_is_derived :
    pubSize wrapShapedTyp = 24
      ∧ (layout wrapShapedTyp).map (fun s => s.path.getLast?) =
          [ some (.lbl "combined_inner_product"), some (.lbl "b")
          , some (.lbl "beta"), some (.lbl "gamma")
          , some (.lbl "alpha"), some (.lbl "zeta")
          , some (.lbl "sponge_digest")
          , some (.idx 0), some (.idx 1), some (.idx 2), some (.idx 3)
          , some (.idx 4), some (.idx 5), some (.idx 6), some (.idx 7)
          , some (.idx 8), some (.idx 9), some (.idx 10), some (.idx 11)
          , some (.idx 12), some (.idx 13), some (.idx 14), some (.idx 15)
          , some (.lbl "branch_data") ] := by
  refine ⟨by decide, by decide⟩

/-- The widths come out of the leaves: `felt 255` for the three field words, `word 128` for the
twenty challenges, and `bitWidth 1024 = 10` for the packed branch data — a width nobody typed. -/
theorem the_wrap_shaped_widths_are_derived :
    widths wrapShapedTyp = [255, 255, 128, 128, 128, 128, 255] ++ List.replicate 16 128 ++ [10] := by
  decide

/-- Reordering ONE field of the record changes nothing about the emission — the bucket decides. ⚑
This is the property the hand-written census could not have: it is insensitive to exactly the edit
that used to break it. -/
theorem the_record_order_does_not_reach_the_emission :
    layout (structOf (wrapShapedFields.set 0 ⟨"alpha", .scalarChallenge, .word 128⟩))
      = layout wrapShapedTyp
    ∧ layout (structOf [wrapShapedFields[1]!, wrapShapedFields[2]!, wrapShapedFields[0]!,
        wrapShapedFields[3]!]) = layout plonkTyp := by
  refine ⟨by decide, by decide⟩

/-! ## §7 — ⚑ CLOSING `publicWordDemoted`'s RESIDUAL AT THE ALLOCATOR.

`KimchiAssertEqual`'s §8 refuses a merge that demotes a public word, and its docblock names the
reason: *"`varIx` interleaves the two namespaces (`internal n ↦ 2n+1`), so an `internal` id below
the public range CAN outrank a public word."* That is a hazard **only because ids were hand-picked**.
A `Typ`-driven interface fixes the public words at `external 0 .. pubSize-1` and can reserve the low
ids on the aux side too; this section proves that when it does, the refusal cannot fire. -/

open Dregg2.Circuit.Emit.KimchiAssertEqual

/-- The union-find forest with the first `B` indices RESERVED: none of them is anybody's parent, and
nothing at or above `B` points below it. -/
structure Reserved (B : Nat) (par : Array Nat) : Prop where
  low : ∀ k, k < B → par.getD k k = k
  high : ∀ k, B ≤ k → B ≤ par.getD k k

theorem ufRootFuel_fixed_below {B : Nat} {par : Array Nat} (h : Reserved B par) :
    ∀ (f k : Nat), k < B → ufRootFuel par f k = k := by
  intro f k hk
  cases f with
  | zero => rfl
  | succ f => simp only [ufRootFuel, h.low k hk, Nat.lt_irrefl, if_false]

theorem ufRootFuel_ge {B : Nat} {par : Array Nat} (h : Reserved B par) :
    ∀ (f k : Nat), B ≤ k → B ≤ ufRootFuel par f k := by
  intro f
  induction f with
  | zero => intro k hk; exact hk
  | succ f ih =>
      intro k hk
      simp only [ufRootFuel]
      by_cases hj : par.getD k k < k
      · simp only [hj, if_true]; exact ih _ (h.high k hk)
      · simp only [hj, if_false]; exact hk

/-- ⚑ A RESERVED index is its own root, whatever was merged above it. -/
theorem ufRoot_fixed_below {B : Nat} {par : Array Nat} (h : Reserved B par) {k : Nat}
    (hk : k < B) : ufRoot par k = k := ufRootFuel_fixed_below h _ k hk

theorem ufRoot_ge {B : Nat} {par : Array Nat} (h : Reserved B par) {k : Nat}
    (hk : B ≤ k) : B ≤ ufRoot par k := ufRootFuel_ge h _ k hk

theorem ufInit_getD (n k : Nat) : (ufInit n).getD k k = k := by
  rw [Array.getD_eq_getD_getElem?]
  by_cases hk : k < n
  · rw [Array.getElem?_eq_getElem (by simpa [ufInit] using hk)]
    simp [ufInit]
  · rw [Array.getElem?_eq_none (by simpa [ufInit] using Nat.le_of_not_lt hk)]
    rfl

theorem reserved_ufInit (B n : Nat) : Reserved B (ufInit n) where
  low := fun k _ => ufInit_getD n k
  high := fun k hk => by rw [ufInit_getD]; exact hk

theorem getD_modify_ne (par : Array Nat) (i j v : Nat) (h : i ≠ j) :
    (par.modify i (fun _ => v)).getD j j = par.getD j j := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    Array.getElem?_modify, if_neg h]

theorem getD_modify_self (par : Array Nat) (i v : Nat) :
    (par.modify i (fun _ => v)).getD i i = if i < par.size then v else i := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_modify, if_pos rfl]
  by_cases hi : i < par.size
  · rw [Array.getElem?_eq_getElem hi, if_pos hi]
    rfl
  · rw [Array.getElem?_eq_none (Nat.le_of_not_lt hi), if_neg hi]
    rfl

/-- ⚑ **A UNION BETWEEN TWO NON-RESERVED INDICES PRESERVES THE RESERVATION.** -/
theorem reserved_ufUnion {B : Nat} {par : Array Nat} (h : Reserved B par) {a b : Nat}
    (ha : B ≤ a) (hb : B ≤ b) : Reserved B (ufUnion par a b) := by
  have hra : B ≤ ufRoot par a := ufRoot_ge h ha
  have hrb : B ≤ ufRoot par b := ufRoot_ge h hb
  simp only [ufUnion]
  split
  · refine ⟨?_, ?_⟩
    · intro k hk
      rw [getD_modify_ne _ _ _ _ (by omega)]
      exact h.low k hk
    · intro k hk
      by_cases hkr : ufRoot par b = k
      · rw [hkr] at *; rw [getD_modify_self]; split <;> omega
      · rw [getD_modify_ne _ _ _ _ hkr]; exact h.high k hk
  · split
    · refine ⟨?_, ?_⟩
      · intro k hk
        rw [getD_modify_ne _ _ _ _ (by omega)]
        exact h.low k hk
      · intro k hk
        by_cases hkr : ufRoot par a = k
        · rw [hkr] at *; rw [getD_modify_self]; split <;> omega
        · rw [getD_modify_ne _ _ _ _ hkr]; exact h.high k hk
    · exact h

/-- A merge list whose every endpoint sits at or above `B`. ⚑ For `B = 2 * pubSize` this says
"no equality names a public word or anything the interleaved `varIx` could slip beneath one". -/
def endpointsAbove (B : Nat) (ms : Merges) : Prop :=
  ∀ ab ∈ ms, B ≤ varIx ab.1 ∧ B ≤ varIx ab.2

theorem reserved_mergeParents {B : Nat} : ∀ (ms : Merges) (par : Array Nat),
    Reserved B par → endpointsAbove B ms →
    Reserved B (ms.foldl (fun p ab => ufUnion p (varIx ab.1) (varIx ab.2)) par) := by
  intro ms
  induction ms with
  | nil => intro par h _; exact h
  | cons ab ms ih =>
      intro par h hab
      simp only [List.foldl_cons]
      refine ih _ (reserved_ufUnion h (hab ab (by simp)).1 (hab ab (by simp)).2) ?_
      intro cd hcd
      exact hab cd (by simp [hcd])

/-- ⚑ **NO PUBLIC WORD IS DEMOTED**, for every merge list drawn from variables the layout put above
the public range — general over the merge list, not decided at an instance. This is the hypothesis
`placeCheckedMerged`'s `publicWordDemoted` branch tests at runtime, discharged statically. -/
theorem no_public_word_is_demoted (pub : Nat) (ms : Merges)
    (h : endpointsAbove (2 * pub) ms) (i : Nat) (hi : i < pub) :
    rootVar ms (.external i) = .external i := by
  have hres : Reserved (2 * pub) (mergeParents ms) :=
    reserved_mergeParents ms _ (reserved_ufInit _ _) h
  have hlt : varIx (PVar.external i) < 2 * pub := by simp only [varIx]; omega
  simp only [rootVar, ufRoot_fixed_below hres hlt, ixVar_varIx]

/-- ⚑ **AND THE ENTRY'S DEMOTION BRANCH IS THEREFORE UNREACHABLE**: the `find?` that produces
`publicWordDemoted` finds nothing. -/
theorem the_demotion_branch_is_dead (pub : Nat) (ms : Merges) (h : endpointsAbove (2 * pub) ms) :
    (List.range pub).find? (fun i => !decide (rootVar ms (.external i) = .external i)) = none := by
  refine List.find?_eq_none.2 ?_
  intro i hi
  simp [no_public_word_is_demoted pub ms h i (List.mem_range.1 hi)]

/-- The floor a `Typ`-driven allocator must clear on the aux side so `endpointsAbove` holds: aux
`external` ids at or above `pubSize`, aux `internal` ids at or above `pubSize`. ⚑ It is the
`internal` half that is the point — `internal k` has `varIx (2k+1)`, so the reserved region on the
internal side is `k < pubSize`, and that is exactly the region a hand-picked `internal 0` walks
into. -/
def auxFloor (pub : Nat) : PVar → Prop
  | .external j => pub ≤ j
  | .internal k => pub ≤ k

/-- ⚑ **THE PLACEMENT CONTRACT, DERIVED.** `KimchiPlacement.Contract` is `(pubSize, auxBase)` — the
two numbers H1 and the dead-gap refusal read, and both are hand-written today (`preimageContract`
is `⟨PUB, 1⟩`, typed in). The layout fixes the first; the aux floor fixes the second. -/
def contractOf (t : Typ) : Contract := ⟨pubSize t, pubSize t⟩

/-- ⚑ **NO DEAD GAP, BY CONSTRUCTION.** `placeChecked` refuses a reference into
`pubSize ≤ i < auxBase`; the derived contract makes that range EMPTY, so a circuit placed under it
cannot produce a `referenceInGap` refusal at all. -/
theorem the_derived_contract_has_no_dead_gap (t : Typ) :
    (contractOf t).pubSize = (contractOf t).auxBase := rfl

theorem auxFloor_is_above (pub : Nat) (v : PVar) (h : auxFloor pub v) : 2 * pub ≤ varIx v := by
  cases v with
  | external j => simp only [auxFloor] at h; simp only [varIx]; omega
  | internal k => simp only [auxFloor] at h; simp only [varIx]; omega

/-- ⚑ **AND THE DERIVED CONTRACT MAKES THE FLOOR TRUE RATHER THAN PROMISED.** Every `external` id
the contract lets a circuit allocate for itself clears the floor — so `endpointsAbove` is a
consequence of placing under `contractOf`, not a side condition a caller has to remember. -/
theorem contractOf_external_clears_the_floor (t : Typ) (j : Nat)
    (hj : (contractOf t).auxBase ≤ j) : auxFloor (pubSize t) (.external j) := hj

/-- …and the `internal` half, which `varIx`'s interleaving makes the non-obvious one: an aux
`internal k` clears the floor exactly when `k` is at or above `pubSize`, because `internal k` sits
at `varIx (2k+1)` and the reserved region on that side is `k < pubSize`. -/
theorem contractOf_internal_clears_the_floor (t : Typ) (k : Nat)
    (hk : (contractOf t).auxBase ≤ k) : auxFloor (pubSize t) (.internal k) := hk

/-- ⚑ **THE ALLOCATOR'S OBLIGATION, AND ITS PAYOFF, IN ONE STATEMENT.** If every variable a merge
names clears the aux floor, no public word can be demoted. The residual `KimchiAssertEqual` named —
"an `internal` id below the public range CAN outrank a public word" — is closed by the allocator
declining to hand those ids out. -/
theorem the_aux_floor_closes_the_demotion_residual (pub : Nat) (ms : Merges)
    (h : ∀ ab ∈ ms, auxFloor pub ab.1 ∧ auxFloor pub ab.2) (i : Nat) (hi : i < pub) :
    rootVar ms (.external i) = .external i :=
  no_public_word_is_demoted pub ms
    (fun ab hab => ⟨auxFloor_is_above pub _ (h ab hab).1, auxFloor_is_above pub _ (h ab hab).2⟩) i hi

/-! ### §7a — the merge that BINDS a public word, which `endpointsAbove` cannot cover.

`preimageMerges` is `(external 0, internal 2)`: the public word IS an endpoint, so §7's hypothesis
is false by construction and its theorems say nothing. What is true there — generally, with no
hypothesis at all — is that a class root never OUTRANKS its member. That is enough to place the only
possible demotion inside the range the allocator reserves. -/

/-- The bounded chase never increases the index. General, for every forest. -/
theorem ufRootFuel_le (par : Array Nat) : ∀ (f k : Nat), ufRootFuel par f k ≤ k := by
  intro f
  induction f with
  | zero => intro k; exact Nat.le_refl k
  | succ f ih =>
      intro k
      simp only [ufRootFuel]
      by_cases hj : par.getD k k < k
      · rw [if_pos hj]
        exact Nat.le_trans (ih _) (Nat.le_of_lt hj)
      · rw [if_neg hj]

theorem ufRoot_le (par : Array Nat) (k : Nat) : ufRoot par k ≤ k := ufRootFuel_le par _ k

theorem varIx_ixVar (n : Nat) : varIx (ixVar n) = n := by
  simp only [ixVar]
  by_cases h : n % 2 == 0
  · simp only [h, if_true]
    simp only [beq_iff_eq] at h
    show 2 * (n / 2) = n
    omega
  · simp only [h]
    simp only [beq_iff_eq] at h
    show 2 * (n / 2) + 1 = n
    omega

/-- ⚑ **A CLASS ROOT NEVER OUTRANKS ITS MEMBER** — general over every merge list and every variable,
no reservation required. -/
theorem rootVar_varIx_le (ms : Merges) (v : PVar) : varIx (rootVar ms v) ≤ varIx v := by
  simp only [rootVar, varIx_ixVar]
  exact ufRoot_le _ _

/-- ⚑ **SO THE ONLY DEMOTION THE ALLOCATOR CANNOT RULE OUT LANDS INSIDE THE RANGE IT RESERVES.**
Whatever the merge list, `rootVar ms (external i)` is an `external j` with `j ≤ i` or an
`internal j` with `j < i` — both strictly inside `0 .. pubSize-1` on their own side. Under the aux
floor no circuit variable lives there, so a demotion cannot be TO a variable the circuit uses; the
first case with `j < i` is two public words in one class, which `placeCheckedMerged` refuses ahead
of the demotion check as `publicWordsAliased`.

⚠ **AND HERE IS WHAT IS STILL OPEN.** This does not prove the root IS `external i`. Closing that
needs the union-find's root-is-class-minimum property, which `KimchiAssertEqual` §2 states as a
maintained invariant and does not prove — it is that file's obligation, not this layer's, and its
`publicWordDemoted` check is the decidable stand-in that still runs on every emission. What the
allocator owns is closed: §7's aux-only case outright, and the mixed case narrowed to the reserved
range. -/
theorem the_demotion_root_is_inside_the_reserved_range (i : Nat) (ms : Merges) :
    (∃ j, j ≤ i ∧ rootVar ms (.external i) = .external j)
      ∨ (∃ j, j < i ∧ rootVar ms (.external i) = .internal j) := by
  have hle : varIx (rootVar ms (.external i)) ≤ 2 * i := rootVar_varIx_le ms (.external i)
  cases hr : rootVar ms (PVar.external i) with
  | external j =>
      refine Or.inl ⟨j, ?_, rfl⟩
      rw [hr] at hle
      simp only [varIx] at hle
      omega
  | internal j =>
      refine Or.inr ⟨j, ?_, rfl⟩
      rw [hr] at hle
      simp only [varIx] at hle
      omega

/-- The ordering the missing union-find lemma would consume: under the floor the public word's
`varIx` is strictly below every aux endpoint's, so it is the minimum of any class it joins. -/
theorem the_public_word_is_the_minimum_of_a_bound_class (pub : Nat) (i : Nat) (hi : i < pub)
    (w : PVar) (hw : auxFloor pub w) : varIx (PVar.external i) < varIx w := by
  have h1 : 2 * pub ≤ varIx w := auxFloor_is_above pub w hw
  have h2 : varIx (PVar.external i) = 2 * i := rfl
  omega

#assert_axioms arrGet_arrOfFn
#assert_axioms read_store
#assert_axioms readAll_store
#assert_axioms store_read
#assert_axioms store_length
#assert_axioms checkAt_ok_iff
#assert_axioms only_the_derived_layout_is_accepted
#assert_axioms a_wrong_layout_is_refused
#assert_axioms layout_paths_nodup
#assert_axioms derived_layouts_always_allocate
#assert_axioms the_ith_slot_is_the_ith_variable
#assert_axioms the_wired_variable_is_the_allocated_one
#assert_axioms varOf_none_of_not_a_leaf
#assert_axioms varEnv_length
#assert_axioms the_assignment_is_the_allocation
#assert_axioms alloc_and_store_agree
#assert_axioms the_emitted_order_is_beta_gamma_alpha_zeta
#assert_axioms the_width_signature_cannot_separate_them
#assert_axioms the_record_order_census_is_refused
#assert_axioms the_endo_lift_is_refused_by_width
#assert_axioms the_derived_check_refuses_at_slot_zero_not_at_the_outlier
#assert_axioms the_wrap_shaped_layout_is_derived
#assert_axioms the_wrap_shaped_widths_are_derived
#assert_axioms the_record_order_does_not_reach_the_emission
#assert_axioms no_public_word_is_demoted
#assert_axioms the_demotion_branch_is_dead
#assert_axioms the_aux_floor_closes_the_demotion_residual
#assert_axioms the_derived_contract_has_no_dead_gap
#assert_axioms contractOf_external_clears_the_floor
#assert_axioms contractOf_internal_clears_the_floor
#assert_axioms rootVar_varIx_le
#assert_axioms the_demotion_root_is_inside_the_reserved_range
#assert_axioms the_public_word_is_the_minimum_of_a_bound_class

end Dregg2.Circuit.Emit.KimchiTyp
