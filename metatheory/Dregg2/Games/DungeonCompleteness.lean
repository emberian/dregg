/-
# Dregg2.Games.DungeonCompleteness — uniform capability and completeness laws.

This file closes two named seams between the native Lean model (`Dungeon`) and its
Lean-authored `Exec.RecordProgram` model (`DungeonProgram`):

* the key-exhibition inversion is uniform over every deployed keyed way (2, 3, 4),
  rather than a theorem specialized to way 2;
* the exact boundary of honest model-to-program completeness is formalized: the
  coarse `Inv` is insufficient, while every actually replay-reachable state
  preserves the stronger per-relic provenance relation the program requires.

⚑ **REBUILT AGAINST `custodyHops`, NOT `custody_ratchet`.** The model retired
`Dungeon.custody_ratchet` AS FALSE: `unlock` now hangs the key in the door it opened
(`CARRIED → HUNG + depth`) and `take` lifts it back out (`HUNG + depth → CARRIED`), so
custody codes go up and then DOWN and no monotonicity survives. This file used to lean on
that retired predicate in exactly one place (`custody_getD_mono`, feeding the deployed
`.monotonic` custody atom). Both are gone. What replaces them is strictly more
informative and matches the deployed teeth one-for-one:

* `custody_hop_of_step` — every legal step moves every relic along one of the hops the
  deployed `allowedTransitions (relic_i) (custodyHops i)` tooth enumerates: `stay`,
  `(home, CARRIED)` (loot), `(CARRIED, BANKED)` (flee), and — keys only —
  `(CARRIED, HUNG + d)` (unlock) and `(HUNG + d, CARRIED)` (take). The hop enumeration is
  what closed a real hole: `monotonic ∧ memberOf {home, CARRIED, BANKED}` ADMITTED
  `home → BANKED`, a relic teleporting out of a hoard straight into the bank without ever
  passing through the pack and therefore never paying the capacity commons. That
  transition is in no arm of `Dungeon.step`, and it is in no hop of `custodyHops`.
* `CustodyHomeWF` — widened from three codes to the deployed `custodyAlphabet`: a KEY
  relic may additionally hang in any door (`HUNG + 1 … HUNG + FLOORS`); the prize and the
  treasures may not, because `unlock` writes slot `keyFor w = w − 1` with `2 ≤ w` and
  nothing else ever writes a `HUNG` code.
* the zone partition is TEN-wide (`pack`, `bank`, four hoards, four doors), because a key
  hanging in a door is in none of the other six and `Σ zones = RELICS` is otherwise FALSE
  on every turn after the first `unlock`.

Honest scope: every theorem here is about the name-keyed, signed-`Int`
`Exec.RecordProgram` model.  It does not claim refinement to the deployed unsigned
evaluator; `DungeonProgram.lean` records that separate substrate seam.
-/
import Dregg2.Games.DungeonProgram

namespace Dregg2.Games.Dungeon.Prog

open Dregg2.Exec (Value)

/-! ⚑ Every law below is stated over the DAY'S WORLD (`Dungeon.WorldParam`): the map is
drawn from the committed day-seed, so `homeCode` and `guardHp` are parameters, not
constants. The completeness boundary (`ModelProgramInv`) is therefore uniform over the
whole drawn family, not a fact about one shipped layout. -/
variable [WorldParam]

-- The world parameter is blanket-scoped over the file (every rule and law is stated over
-- the day's drawn map); a handful of pure list/count helpers legitimately do not mention
-- it, and the section-variable linter would otherwise report each one.
set_option linter.unusedSectionVars false

/-! ## 1. Every deployed way exercises its corresponding key capability. -/

open Dregg2.Exec in
/-- Negative tooth: changing any deployed keyed way while mutating/omitting its
required carried-key exhibit is refused.

⚑ **THE EXHIBIT MOVED TO THE PRE-STATE, AND SO DOES THIS REFUSAL.** It used to demand
`n.relic ≠ CARRIED` — the POST-state read. That is now FALSE of the rulebook: a lawful
`unlock` leaves the key HANGING (`HUNG + depth`), so the old statement would have said
every legal way-flip is refused, which is the "a tooth that refuses everything" failure
mode. The honest form is the one `way_flip_exhibits_key` actually proves: the capability
had to be OWNED GOING IN. That is strictly stronger than the old reading ever was — an
attacker who acquires the key ON the flipping turn satisfied the post-state form and does
not satisfy this one. -/
theorem way_flip_key_mutation_refused (w : Nat) (hwLo : 2 ≤ w) (hwHi : w ≤ FLOORS)
    {m : Nat} (hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8)
    {o n : Value}
    (hflip : (o.scalar (wayName w) == n.scalar (wayName w)) = false)
    (hmut : o.scalar (relicName (keyFor w)) ≠ some (CARRIED : Int)) :
    RecordProgram.admits dungeonExec m o n = false := by
  cases hadm : RecordProgram.admits dungeonExec m o n with
  | false => rfl
  | true =>
    have hwHi' : w ≤ 4 := hwHi
    have hw : w = 2 ∨ w = 3 ∨ w = 4 := by omega
    exact False.elim (hmut ((way_flip_exhibits_key w hw hm hadm hflip).1))

-- The generic theorem bites away from the old way-2-only canary: way 3 cannot be
-- opened from genesis while its key relic remains in the deep — driven on EVERY day of
-- the drawn family, not just the shipped map.
#guard (List.range dayCount).all (fun k =>
  (Dregg2.Exec.RecordProgram.admits (@dungeonExec (instAt k)) 2
      (encode (@genesisState (instAt k)))
      (setF (setF (encode (@genesisState (instAt k))) (wayName 3) 1) "spent" 1)) == false)

/-! ## 2. The exact model-to-program completeness boundary. -/

-- `Nat.repr` is opaque to the ordinary simplifier.  These tiny byte-level pins let
-- the proofs below reduce lookups in the fixed, deployed 4-floor/8-relic schema.
@[simp] private theorem wayName_2 : wayName 2 = "way_2" := by decide
@[simp] private theorem wayName_3 : wayName 3 = "way_3" := by decide
@[simp] private theorem wayName_4 : wayName 4 = "way_4" := by decide
@[simp] private theorem hoardName_1 : hoardName 1 = "hoard_1" := by decide
@[simp] private theorem hoardName_2 : hoardName 2 = "hoard_2" := by decide
@[simp] private theorem hoardName_3 : hoardName 3 = "hoard_3" := by decide
@[simp] private theorem hoardName_4 : hoardName 4 = "hoard_4" := by decide
-- ⚑ THE DOORS. `hangFloors` is `List.range' 1 FLOORS`, which is opaque to `simp` until
-- it is a literal; without this pin nothing below can reduce a lookup past the door
-- residue that `encode` carries.
@[simp] private theorem hangFloors_eq : hangFloors = [1, 2, 3, 4] := by decide
@[simp] private theorem hungName_eq : hungName = "hung" := by decide
@[simp] private theorem relicName_0 : relicName 0 = "relic_0" := by decide
@[simp] private theorem relicName_1 : relicName 1 = "relic_1" := by decide
@[simp] private theorem relicName_2 : relicName 2 = "relic_2" := by decide
@[simp] private theorem relicName_3 : relicName 3 = "relic_3" := by decide
@[simp] private theorem relicName_4 : relicName 4 = "relic_4" := by decide
@[simp] private theorem relicName_5 : relicName 5 = "relic_5" := by decide
@[simp] private theorem relicName_6 : relicName 6 = "relic_6" := by decide
@[simp] private theorem relicName_7 : relicName 7 = "relic_7" := by decide
@[simp] private theorem range_relics :
    List.range RELICS = [0, 1, 2, 3, 4, 5, 6, 7] := by decide

open Dregg2.Exec in
private theorem encode_scalar_depth (s : DState) :
    (encode s).scalar "depth" = some (s.depth : Int) := by
  simp [encode, Value.scalar, Value.field]

open Dregg2.Exec in
private theorem encode_scalar_spent (s : DState) :
    (encode s).scalar "spent" = some (s.spent : Int) := by
  simp [encode, Value.scalar, Value.field]

open Dregg2.Exec in
private theorem encode_scalar_wounds (s : DState) :
    (encode s).scalar "wounds" = some (s.wounds : Int) := by
  simp [encode, Value.scalar, Value.field]

open Dregg2.Exec in
private theorem encode_scalar_harm (s : DState) :
    (encode s).scalar "harm" = some (s.harm : Int) := by
  simp [encode, Value.scalar, Value.field]

open Dregg2.Exec in
private theorem encode_scalar_fate (s : DState) :
    (encode s).scalar "fate" = some (s.fate : Int) := by
  simp [encode, Value.scalar, Value.field]

open Dregg2.Exec in
private theorem encode_scalar_pack (s : DState) :
    (encode s).scalar "pack" = some (pack s : Int) := by
  simp [encode, Value.scalar, Value.field]

open Dregg2.Exec in
private theorem encode_scalar_bank (s : DState) :
    (encode s).scalar "bank" = some (bank s : Int) := by
  simp [encode, Value.scalar, Value.field]

open Dregg2.Exec in
private theorem encode_scalar_way (s : DState) (w : Nat) (hwLo : 2 ≤ w)
    (hwHi : w ≤ FLOORS) :
    (encode s).scalar (wayName w) = some (s.ways.getD (w - 2) 0 : Int) := by
  have hwHi' : w ≤ 4 := hwHi
  have hw : w = 2 ∨ w = 3 ∨ w = 4 := by omega
  rcases hw with rfl | rfl | rfl <;>
    simp [encode, Value.scalar, Value.field]

open Dregg2.Exec in
private theorem encode_scalar_hoard (s : DState) (d : Nat) (hdLo : 1 ≤ d)
    (hdHi : d ≤ FLOORS) :
    (encode s).scalar (hoardName d) = some (hoardAt s d : Int) := by
  have hdHi' : d ≤ 4 := hdHi
  have hd : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 := by omega
  rcases hd with rfl | rfl | rfl | rfl <;>
    simp [encode, Value.scalar, Value.field]

open Dregg2.Exec in
/-- ⚑ The door census, read off the encoding. `hungTotal` is a sum of the model's own
`hungAt` projections (`countP (· == HUNG + d)`), so the register cannot disagree with
custody about how many keys hang in doors — the same reason the hoard readings cannot.
The per-FLOOR fact the four old registers carried did not evaporate: it moved onto the
relic (`doorArrivalTooth` / `doorDepartureTooth` / `keyHangsHereTooth`). -/
private theorem encode_scalar_hung (s : DState) :
    (encode s).scalar hungName = some (hungTotal s : Int) := by
  simp [encode, Value.scalar, Value.field]

open Dregg2.Exec in
private theorem encode_scalar_relic (s : DState) (i : Nat) (hi : i < RELICS) :
    (encode s).scalar (relicName i) = some (s.custody.getD i 0 : Int) := by
  have hi' : i < 8 := hi
  have hiCases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
    omega
  rcases hiCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [encode, Value.scalar, Value.field]

attribute [simp] encode_scalar_depth encode_scalar_spent encode_scalar_wounds
  encode_scalar_harm encode_scalar_fate encode_scalar_pack encode_scalar_bank

open Dregg2.Exec in
@[simp] private theorem encode_scalar_way2 (s : DState) :
    (encode s).scalar "way_2" = some (s.ways.getD 0 0 : Int) := by
  simpa using encode_scalar_way s 2 (by decide) (by decide)
open Dregg2.Exec in
@[simp] private theorem encode_scalar_way3 (s : DState) :
    (encode s).scalar "way_3" = some (s.ways.getD 1 0 : Int) := by
  simpa using encode_scalar_way s 3 (by decide) (by decide)
open Dregg2.Exec in
@[simp] private theorem encode_scalar_way4 (s : DState) :
    (encode s).scalar "way_4" = some (s.ways.getD 2 0 : Int) := by
  simpa using encode_scalar_way s 4 (by decide) (by decide)

open Dregg2.Exec in
@[simp] private theorem encode_scalar_hoard1 (s : DState) :
    (encode s).scalar "hoard_1" = some (hoardAt s 1 : Int) := by
  simpa using encode_scalar_hoard s 1 (by decide) (by decide)
open Dregg2.Exec in
@[simp] private theorem encode_scalar_hoard2 (s : DState) :
    (encode s).scalar "hoard_2" = some (hoardAt s 2 : Int) := by
  simpa using encode_scalar_hoard s 2 (by decide) (by decide)
open Dregg2.Exec in
@[simp] private theorem encode_scalar_hoard3 (s : DState) :
    (encode s).scalar "hoard_3" = some (hoardAt s 3 : Int) := by
  simpa using encode_scalar_hoard s 3 (by decide) (by decide)
open Dregg2.Exec in
@[simp] private theorem encode_scalar_hoard4 (s : DState) :
    (encode s).scalar "hoard_4" = some (hoardAt s 4 : Int) := by
  simpa using encode_scalar_hoard s 4 (by decide) (by decide)

open Dregg2.Exec in
@[simp] private theorem encode_scalar_hungLit (s : DState) :
    (encode s).scalar "hung" = some (hungTotal s : Int) := by
  simpa using encode_scalar_hung s

/-- The door residue as the four per-floor censuses, for the arithmetic below. -/
private theorem hungTotal_split (s : DState) :
    hungTotal s = hungAt s 1 + hungAt s 2 + hungAt s 3 + hungAt s 4 := by
  simp [hungTotal, hangFloors_eq]; omega

/-- ⚑ Every door fact about a turn reduces to the four per-floor censuses. `j`/`k` carry
the ±1 a verb posts: `j = k = 0` freezes the residue, `k = 1` is `unlock`'s hang, `j = 1`
is `take`'s lift. One register standing for four censuses is exactly this identity. -/
private theorem hungTotal_eq_of {s s' : DState} {j k : Nat}
    (h : hungAt s' 1 + hungAt s' 2 + hungAt s' 3 + hungAt s' 4 + j
       = hungAt s 1 + hungAt s 2 + hungAt s 3 + hungAt s 4 + k) :
    hungTotal s' + j = hungTotal s + k := by
  rw [hungTotal_split, hungTotal_split]; omega

/-- The `flee` promotion, at an arbitrary predicate: the map moves `CARRIED` to `BANKED`
and nothing else, so a census blind to BOTH codes rides through the bank untouched. This
generalizes `countP_flee_floor_local` (below) from a value to a predicate, which is what
the whole-door-family readings need. -/
private theorem countP_flee_pred_local (l : List Nat) (p : Nat → Bool)
    (hC : p CARRIED = false) (hB : p BANKED = false) :
    (l.map (fun c => if c = CARRIED then BANKED else c)).countP p = l.countP p := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.map_cons, List.countP_cons, List.countP_cons, ih]
    by_cases h : hd = CARRIED
    · subst hd; simp [hC, hB]
    · simp [h]

open Dregg2.Exec in
@[simp] private theorem encode_scalar_relic0 (s : DState) :
    (encode s).scalar "relic_0" = some (s.custody.getD 0 0 : Int) := by
  simpa using encode_scalar_relic s 0 (by decide)
open Dregg2.Exec in
@[simp] private theorem encode_scalar_relic1 (s : DState) :
    (encode s).scalar "relic_1" = some (s.custody.getD 1 0 : Int) := by
  simpa using encode_scalar_relic s 1 (by decide)
open Dregg2.Exec in
@[simp] private theorem encode_scalar_relic2 (s : DState) :
    (encode s).scalar "relic_2" = some (s.custody.getD 2 0 : Int) := by
  simpa using encode_scalar_relic s 2 (by decide)
open Dregg2.Exec in
@[simp] private theorem encode_scalar_relic3 (s : DState) :
    (encode s).scalar "relic_3" = some (s.custody.getD 3 0 : Int) := by
  simpa using encode_scalar_relic s 3 (by decide)
open Dregg2.Exec in
@[simp] private theorem encode_scalar_relic4 (s : DState) :
    (encode s).scalar "relic_4" = some (s.custody.getD 4 0 : Int) := by
  simpa using encode_scalar_relic s 4 (by decide)
open Dregg2.Exec in
@[simp] private theorem encode_scalar_relic5 (s : DState) :
    (encode s).scalar "relic_5" = some (s.custody.getD 5 0 : Int) := by
  simpa using encode_scalar_relic s 5 (by decide)
open Dregg2.Exec in
@[simp] private theorem encode_scalar_relic6 (s : DState) :
    (encode s).scalar "relic_6" = some (s.custody.getD 6 0 : Int) := by
  simpa using encode_scalar_relic s 6 (by decide)
open Dregg2.Exec in
@[simp] private theorem encode_scalar_relic7 (s : DState) :
    (encode s).scalar "relic_7" = some (s.custody.getD 7 0 : Int) := by
  simpa using encode_scalar_relic s 7 (by decide)

/-- Every relic's minted home is a real floor — now a consequence of the DAY'S world law
(`Dungeon.wf_home_floor`), where it used to be a `decide` on a hard-wired list. -/
private theorem homeCode_le_floors (i : Nat) (hi : i < RELICS) :
    homeCode i ≤ FLOORS := by
  have hlen : homeFloors.length = RELICS := wf_homes_length
  have hi' : i < homeFloors.length := by rw [hlen]; exact hi
  show homeFloors.getD i 0 ≤ FLOORS
  rw [← List.getElem_eq_getD (l := homeFloors) (i := i) (h := hi') 0]
  exact (wf_home_floor (List.getElem_mem hi')).2

/-- The extra relation the authored program enforces beyond `Dungeon.Inv`: each relic may
occupy its own minted home, be carried, be banked — or, IF IT IS A KEY, hang in a door on
a real floor.  `Dungeon.Inv` intentionally says only "some floor" and is therefore too
weak for universal model-to-program completeness (counterexample below).

⚑ **THE FOURTH DISJUNCT IS THE DOOR, AND IT IS KEYS ONLY.** This is exactly the deployed
`custodyAlphabet i` — `[homeCode i, CARRIED, BANKED] ++ (if isKeyRelic i then HUNG+1 …
HUNG+FLOORS else [])`. Giving every relic the HUNG alphabet would have been the easy
widening and a strictly weaker tooth: `unlock w` writes slot `keyFor w = w − 1` with
`2 ≤ w ≤ FLOORS`, so relic 0 (THE PRIZE) and relics `FLOORS…` (the treasures) can never
take a `HUNG` code, and the deployed `memberOf` says so per relic. -/
def CustodyHomeWF (s : DState) : Prop :=
  ∀ i, i < RELICS →
    s.custody[i]? = some (homeCode i) ∨
    s.custody[i]? = some CARRIED ∨
    s.custody[i]? = some BANKED ∨
    (isKeyRelic i = true ∧ ∃ d, 1 ≤ d ∧ d ≤ FLOORS ∧ s.custody[i]? = some (HUNG + d))

/-- The exact model-side invariant needed by the current authored program. -/
def ModelProgramInv (s : DState) : Prop := Inv s ∧ CustodyHomeWF s

theorem modelProgramInv_genesis : ModelProgramInv genesisState := by
  refine ⟨inv_genesis, ?_⟩
  intro i hi
  left
  have hlen : homeFloors.length = RELICS := wf_homes_length
  have hi' : i < homeFloors.length := by rw [hlen]; exact hi
  show homeFloors[i]? = some (homeFloors.getD i 0)
  rw [List.getElem?_eq_getElem hi', List.getElem_eq_getD (0 : Nat)]

/-- `keyFor w` is a key relic for every deployed keyed way — the index `unlock` writes. -/
private theorem isKeyRelic_keyFor {w : Nat} (hlo : 2 ≤ w) (hhi : w ≤ FLOORS) :
    isKeyRelic (keyFor w) = true := by
  have hhi' : w ≤ 4 := hhi
  have hw : w = 2 ∨ w = 3 ∨ w = 4 := by omega
  rcases hw with rfl | rfl | rfl <;> decide

/-- The home-specific custody alphabet is preserved by every legal model move. -/
theorem modelProgramInv_step {s s' : DState} {m : Move}
    (hInv : ModelProgramInv s) (hstep : step s m = some s') :
    ModelProgramInv s' := by
  refine ⟨inv_step hInv.1 hstep, ?_⟩
  intro i hi
  have hhome := hInv.2 i hi
  cases m with
  | delve =>
    simp only [step] at hstep
    split at hstep
    · cases hstep; exact hhome
    · exact absurd hstep (by simp)
  | ascend =>
    simp only [step] at hstep
    split at hstep
    · cases hstep; exact hhome
    · exact absurd hstep (by simp)
  | unlock w =>
    -- ⚑ `unlock` NOW WRITES CUSTODY: the key it exercises leaves the pack and hangs in
    -- the door, on the floor the run was standing on. That floor is real (`1 ≤ depth` is
    -- this verb's own guard, `depth ≤ FLOORS` is the invariant coming in), and the slot
    -- it writes is a KEY slot, so the fourth disjunct is available to it and to nothing
    -- else.
    simp only [step] at hstep
    split at hstep
    · rename_i hlegal
      have hdLo : 1 ≤ s.depth := hlegal.2.2.2.1
      have hwLo : 2 ≤ w := hlegal.2.2.2.2.1
      have hwHi : w ≤ FLOORS := hlegal.2.2.2.2.2.1
      have hdHi : s.depth ≤ FLOORS := hInv.1.2.2.1
      cases hstep
      by_cases hik : i = keyFor w
      · have hlen : i < s.custody.length := by
          have := hInv.1.1.1
          omega
        refine Or.inr (Or.inr (Or.inr ⟨?_, s.depth, hdLo, hdHi, ?_⟩))
        · rw [hik]; exact isKeyRelic_keyFor hwLo hwHi
        · rw [hik, List.getElem?_set_self (by rw [← hik]; exact hlen)]
      · rw [List.getElem?_set_ne (by omega)]
        exact hhome
    · exact absurd hstep (by simp)
  | smite =>
    simp only [step] at hstep
    split at hstep
    · cases hstep; exact hhome
    · exact absurd hstep (by simp)
  | lunge =>
    simp only [step] at hstep
    split at hstep
    · cases hstep; exact hhome
    · exact absurd hstep (by simp)
  | loot r =>
    simp only [step] at hstep
    split at hstep
    · cases hstep
      by_cases hir : i = r
      · subst r
        have hlen : i < s.custody.length := by
          have := hInv.1.1.1
          omega
        rw [List.getElem?_set_self hlen]
        exact Or.inr (Or.inl rfl)
      · rw [List.getElem?_set_ne (by omega)]
        exact hhome
    · exact absurd hstep (by simp)
  | take r =>
    -- ⚑ THE ONE LOWERING HOP: the key comes back out of the door and into the pack.
    simp only [step] at hstep
    split at hstep
    · cases hstep
      by_cases hir : i = r
      · subst r
        have hlen : i < s.custody.length := by
          have := hInv.1.1.1
          omega
        rw [List.getElem?_set_self hlen]
        exact Or.inr (Or.inl rfl)
      · rw [List.getElem?_set_ne (by omega)]
        exact hhome
    · exact absurd hstep (by simp)
  | flee =>
    simp only [step] at hstep
    split at hstep
    · cases hstep
      rcases hhome with hh | hc | hb | ⟨hkey, d, hdLo, hdHi, hh⟩
      · rw [List.getElem?_map, hh]
        left
        have hHomeLt : homeCode i < CARRIED := by
          have := homeCode_le_floors i hi
          have hFloorNum : FLOORS < CARRIED := by decide
          omega
        simp [show homeCode i ≠ CARRIED by omega]
      · rw [List.getElem?_map, hc]
        right; right; left; rfl
      · rw [List.getElem?_map, hb]
        right; right; left
        simp [show BANKED ≠ CARRIED by decide]
      · -- ⚑ A HUNG KEY IS NOT YOURS: `fleeMap` promotes `CARRIED` and only `CARRIED`, so
        -- the key stays in its door across the bank.
        rw [List.getElem?_map, hh]
        refine Or.inr (Or.inr (Or.inr ⟨hkey, d, hdLo, hdHi, ?_⟩))
        have hHC : HUNG + d ≠ CARRIED := by
          have hH : (HUNG : Nat) = 12 := rfl
          have hC : (CARRIED : Nat) = 8 := rfl
          omega
        simp [hHC]
    · exact absurd hstep (by simp)

/-! ### Why `Inv` alone cannot imply completeness. -/

/-- An `Inv` state in which relic 1 sits at floor 2 rather than its minted home 1.
The model's coarse custody alphabet permits this state; the authored program's
provenance tooth deliberately does not. -/
def wrongHomeState : DState :=
  { depth := 0, spent := 0, wounds := 0, harm := 0, fate := 0, ways := [0, 0, 0],
    custody := [4, 2, 2, 3, 1, 1, 2, 3] }

theorem wrongHomeState_inv : Inv wrongHomeState := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    first
      | (intro d hlo hhi; exact absurd hhi (by simp [wrongHomeState]; omega))
      | simp [wrongHomeState, CustodyWF, pack, bank, FLOORS, RELICS,
              CAP, CARRIED, BANKED]

/-- The obstruction is exhibited on DAY 0's map (`instAt 0`, the shipped layout): a
concrete counterexample needs a concrete world. Nothing about it is special to day 0 —
`Inv` is world-blind, while the provenance tooth is minted per-relic on whatever map the
day drew. -/
theorem wrongHomeState_delve_legal :
    @step (instAt 0) wrongHomeState .delve = some { wrongHomeState with
      depth := 1, wounds := 0, spent := 1 } := by decide

theorem wrongHomeState_delve_refused :
    Dregg2.Exec.RecordProgram.admits (@dungeonExec (instAt 0)) (moveIdx .delve)
      (encode wrongHomeState)
      (encode { wrongHomeState with depth := 1, wounds := 0, spent := 1 }) = false := by
  decide

/-! ### Count/custody bridge used by every honest verb. -/

/-- ⚑ **THE PARTITION IS TEN-WIDE.** A relic is in the pack, in the bank, lying in one of
the four hoards, or HANGING IN ONE OF THE FOUR DOORS — and the ten counters are exactly a
partition of the custody list, so `Σ zones = RELICS` is an identity rather than a hope.
The door family is not optional bookkeeping: after the first `unlock` a key is in none of
the other six zones (it left the pack, and `fleeMap` promotes `CARRIED` and only
`CARRIED`, so it never reaches the bank), and the six-zone sum this used to state is
simply FALSE from that turn on. -/
private theorem custody_count_partition (l : List Nat)
    (hcodes : ∀ c ∈ l, (1 ≤ c ∧ c ≤ FLOORS) ∨ c = CARRIED ∨ c = BANKED
      ∨ (HUNG + 1 ≤ c ∧ c ≤ HUNG + FLOORS)) :
    l.countP (· == CARRIED) + l.countP (· == BANKED) +
      l.countP (· == 1) + l.countP (· == 2) +
      l.countP (· == 3) + l.countP (· == 4) +
      l.countP (· == HUNG + 1) + l.countP (· == HUNG + 2) +
      l.countP (· == HUNG + 3) + l.countP (· == HUNG + 4) = l.length := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    have ha := hcodes a (by simp)
    have hrest : ∀ c ∈ rest,
        (1 ≤ c ∧ c ≤ FLOORS) ∨ c = CARRIED ∨ c = BANKED
          ∨ (HUNG + 1 ≤ c ∧ c ≤ HUNG + FLOORS) := by
      intro c hc
      exact hcodes c (by simp [hc])
    have hpart := ih hrest
    have haCases : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = CARRIED ∨ a = BANKED
        ∨ a = HUNG + 1 ∨ a = HUNG + 2 ∨ a = HUNG + 3 ∨ a = HUNG + 4 := by
      have hH : (HUNG : Nat) = 12 := rfl
      have hF : (FLOORS : Nat) = 4 := rfl
      rcases ha with hfloor | hcarried | hbanked | hhung
      · have hFloor : a ≤ 4 := hfloor.2
        omega
      · omega
      · omega
      · omega
    rcases haCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [CARRIED, BANKED, HUNG] at hpart ⊢ <;> omega

private theorem zones_total_of_inv {s : DState} (hInv : Inv s) :
    pack s + bank s + hoardAt s 1 + hoardAt s 2 + hoardAt s 3 + hoardAt s 4
      + hungAt s 1 + hungAt s 2 + hungAt s 3 + hungAt s 4 = RELICS := by
  have hpart := custody_count_partition s.custody hInv.1.2
  have hlen : s.custody.length = RELICS := hInv.1.1
  simp only [pack, bank, hoardAt, hungAt] at *
  omega

/-- ⚑ The door residue is bounded by the PARTITION it belongs to, not by a `countP` of its
own: it is one register standing for four censuses, and `zones_total_of_inv` says the
seven zones partition the eight relics. -/
theorem hungTotal_le_relics {s : DState} (hInv : Inv s) : hungTotal s ≤ RELICS := by
  have hpart := zones_total_of_inv hInv
  have hsplit := hungTotal_split s
  omega

open Dregg2.Exec in
private theorem encode_sum_zones_of_inv {s : DState} (hInv : Inv s) :
    sumScalars (encode s) zones = some (RELICS : Int) := by
  have htotal := zones_total_of_inv hInv
  have hht := hungTotal_split s
  have htotalN : pack s + bank s + hoardAt s 1 + hoardAt s 2 + hoardAt s 3 + hoardAt s 4
      + hungTotal s = RELICS := by omega
  have htotalZ : (pack s : Int) + (bank s : Int) + (hoardAt s 1 : Int) +
      (hoardAt s 2 : Int) + (hoardAt s 3 : Int) + (hoardAt s 4 : Int) +
      (hungTotal s : Int) = (RELICS : Int) := by exact_mod_cast htotalN
  simp [sumScalars, zones]
  simpa [RELICS, add_comm, add_left_comm, add_assoc] using htotalZ

open Dregg2.Exec in
@[simp] private theorem encode_scalar_sentinel (s : DState) :
    (encode s).scalar sentinelField = some 1 := by
  simp [encode, Value.scalar, Value.field, sentinelField]

private theorem legal_step_fate {s s' : DState} {m : Move}
    (hstep : step s m = some s') :
    s.fate = 0 ∧ (s'.fate = 0 ∨ s'.fate = 1) := by
  cases m <;> simp only [step] at hstep <;> split at hstep
  all_goals first | (cases hstep; simp_all) | exact absurd hstep (by simp)

private theorem legal_step_spent_eq {s s' : DState} {m : Move}
    (hstep : step s m = some s') : s'.spent = s.spent + price m := by
  cases m <;> simp only [step] at hstep <;> split at hstep
  all_goals first | (cases hstep; rfl) | exact absurd hstep (by simp)

open Dregg2.Exec in
private theorem coreTeeth_honest {s s' : DState} {m : Move}
    (hInv : ModelProgramInv s) (hstep : step s m = some s') :
    ∀ c ∈ coreTeeth, evalConstraint c.toExec (encode s) (encode s') = true := by
  intro c hc
  have hPost := modelProgramInv_step hInv hstep
  have hsum := encode_sum_zones_of_inv hPost.1
  have hspend := step_spends hstep
  have hfate := legal_step_fate hstep
  simp only [coreTeeth, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · simp [Constraint.toExec, evalConstraint, hsum]
  · apply (evalConstraint_affineLe_iff _ _ _ _).2
    refine ⟨(pack s' : Int) + (s'.depth : Int) + (s'.harm : Int), ?_, ?_⟩
    · simp only [affineSum, List.map_cons, List.map_nil, List.foldr_cons,
        List.foldr_nil, encode_scalar_pack, encode_scalar_depth, encode_scalar_harm,
        Option.some.injEq]
      ring
    · exact_mod_cast hPost.1.2.2.2.2.2.1
  · exact (evalSimple_strictMono_iff "spent" (encode s) (encode s')).2
      ⟨s.spent, s'.spent, by simp, by simp, by exact_mod_cast hspend⟩
  · simp only [Constraint.toExec, evalConstraint]
    unfold evalSimple
    rw [encode_scalar_spent]
    change decide ((s'.spent : Int) ≤ (BREATH : Int)) = true
    exact decide_eq_true (by exact_mod_cast hPost.1.2.1)
  · simp only [Constraint.toExec, evalConstraint, encode_scalar_fate]
    rcases hfate with ⟨ho, hn | hn⟩ <;> simp [ho, hn]

private theorem getElem?_eq_some_getD {l : List Nat} {i bound : Nat}
    (hlen : l.length = bound) (hi : i < bound) : l[i]? = some (l.getD i 0) := by
  have hil : i < l.length := by omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil]
  rfl

private theorem getD_eq_of_getElem?_eq_some {l : List Nat} {i v : Nat}
    (h : l[i]? = some v) : l.getD i 0 = v := by
  rw [List.getD_eq_getElem?_getD, h]
  rfl

private theorem getD_set_self {l : List Nat} {i v : Nat} (hi : i < l.length) :
    (l.set i v).getD i 0 = v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hi]
  rfl

private theorem getD_set_ne {l : List Nat} {i j v : Nat} (h : j ≠ i) :
    (l.set j v).getD i 0 = l.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

/-- `flee`'s write, read at one index: the map is the model's own `CARRIED ↦ BANKED`
promotion, so a slot reads as `BANKED` iff it was `CARRIED` and is otherwise untouched. -/
private theorem getD_map_flee {l : List Nat} {i : Nat} (hi : i < l.length) :
    (l.map (fun c => if c = CARRIED then BANKED else c)).getD i 0
      = (if l.getD i 0 = CARRIED then BANKED else l.getD i 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]

/-- `CustodyHomeWF`, read as membership in the DEPLOYED alphabet — the exact list the
`memberOf` tooth carries for relic `i`. -/
private theorem custody_getD_alphabet {s : DState} (hInv : ModelProgramInv s)
    (i : Nat) (hi : i < RELICS) : s.custody.getD i 0 ∈ custodyAlphabet i := by
  have hget := getElem?_eq_some_getD hInv.1.1.1 hi
  simp only [custodyAlphabet, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  rcases hInv.2 i hi with h | h | h | ⟨hkey, d, hdLo, hdHi, h⟩ <;> rw [hget] at h
  · exact Or.inl (Or.inl (Option.some.inj h))
  · exact Or.inl (Or.inr (Or.inl (Option.some.inj h)))
  · exact Or.inl (Or.inr (Or.inr (Option.some.inj h)))
  · refine Or.inr ?_
    rw [if_pos hkey]
    refine List.mem_map.mpr ⟨d, ?_, ?_⟩
    · have hdHi' : d ≤ 4 := hdHi
      have hd : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 := by omega
      rcases hd with rfl | rfl | rfl | rfl <;> decide
    · exact (Option.some.inj h).symm

/-- Every code in the alphabet is a `stay` hop — the first block of `custodyHops i`. -/
private theorem stay_mem_custodyHops {i c : Nat} (hc : c ∈ custodyAlphabet i) :
    (c, c) ∈ custodyHops i := by
  simp only [custodyHops, List.mem_append]
  exact Or.inl (Or.inl (List.mem_map_of_mem hc))

/-- The `unlock` / `take` hop pair, for a key relic and a real floor. -/
private theorem hang_mem_custodyHops {i d : Nat} (hkey : isKeyRelic i = true)
    (hdLo : 1 ≤ d) (hdHi : d ≤ FLOORS) :
    (CARRIED, HUNG + d) ∈ custodyHops i ∧ (HUNG + d, CARRIED) ∈ custodyHops i := by
  have hdHi' : d ≤ 4 := hdHi
  have hd : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 := by omega
  constructor <;>
    (simp only [custodyHops, List.mem_append, if_pos hkey]
     refine Or.inr ?_
     rcases hd with rfl | rfl | rfl | rfl <;> decide)

/-- ⚑ **THE EDGE LAW — WHICH HOP, AND ON WHICH FLOOR.** Every legal step moves every
relic along exactly one of five named edges, and the two door edges carry THE FLOOR THE
RUN IS STANDING ON.

That last clause is what the counter-side door frame could never say and is why the frame
moved onto the object: `unlock` hangs the key in the door of `s.depth` and `take` lifts one
out of the door of `s.depth`, on a turn that does not move `depth` at all. So a key can
neither enter nor leave a door on a floor the run is not standing at — which is exactly
the two `heapField` teeth `doorArrivalTooth` / `doorDepartureTooth` demand, and exactly the
remote take (attack 7b) the deployed program refuses.

`custody_hop_of_step` — the deployed `allowedTransitions (relic_i) (custodyHops i)` tooth —
is the floor-forgetting corollary below. -/
private theorem custody_edge_of_step {s s' : DState} {m : Move}
    (hInv : ModelProgramInv s) (hstep : step s m = some s')
    (i : Nat) (hi : i < RELICS) :
    s'.custody.getD i 0 = s.custody.getD i 0
      ∨ (s.custody.getD i 0 = homeCode i ∧ s'.custody.getD i 0 = CARRIED)
      ∨ (s.custody.getD i 0 = CARRIED ∧ s'.custody.getD i 0 = BANKED)
      ∨ (isKeyRelic i = true ∧ 1 ≤ s.depth ∧ s.depth ≤ FLOORS ∧ s'.depth = s.depth
          ∧ s.custody.getD i 0 = CARRIED ∧ s'.custody.getD i 0 = HUNG + s.depth)
      ∨ (isKeyRelic i = true ∧ 1 ≤ s.depth ∧ s.depth ≤ FLOORS ∧ s'.depth = s.depth
          ∧ s.custody.getD i 0 = HUNG + s.depth ∧ s'.custody.getD i 0 = CARRIED) := by
  have hlen : s.custody.length = RELICS := hInv.1.1.1
  have hilt : i < s.custody.length := by omega
  have hdHi : s.depth ≤ FLOORS := hInv.1.2.2.1
  have halpha := custody_getD_alphabet hInv i hi
  have hHnum : (HUNG : Nat) = 12 := rfl
  have hCnum : (CARRIED : Nat) = 8 := rfl
  have hBnum : (BANKED : Nat) = 9 := rfl
  have hFnum : (FLOORS : Nat) = 4 := rfl
  have hhome : homeCode i ≤ FLOORS := homeCode_le_floors i hi
  cases m with
  | delve =>
    simp only [step] at hstep
    split at hstep
    · cases hstep; exact Or.inl rfl
    · exact absurd hstep (by simp)
  | ascend =>
    simp only [step] at hstep
    split at hstep
    · cases hstep; exact Or.inl rfl
    · exact absurd hstep (by simp)
  | smite =>
    simp only [step] at hstep
    split at hstep
    · cases hstep; exact Or.inl rfl
    · exact absurd hstep (by simp)
  | lunge =>
    simp only [step] at hstep
    split at hstep
    · cases hstep; exact Or.inl rfl
    · exact absurd hstep (by simp)
  | unlock w =>
    simp only [step] at hstep
    split at hstep
    · rename_i hlegal
      have hdLo : 1 ≤ s.depth := hlegal.2.2.2.1
      have hwLo : 2 ≤ w := hlegal.2.2.2.2.1
      have hwHi : w ≤ FLOORS := hlegal.2.2.2.2.2.1
      have hkeyC : s.custody[keyFor w]? = some CARRIED := hlegal.2.2.2.2.2.2.2
      cases hstep
      by_cases hik : i = keyFor w
      · have hold : s.custody.getD i 0 = CARRIED := by
          rw [hik]; exact getD_eq_of_getElem?_eq_some hkeyC
        have hnew : (s.custody.set (keyFor w) (HUNG + s.depth)).getD i 0 = HUNG + s.depth := by
          rw [hik]; exact getD_set_self (by rw [← hik]; exact hilt)
        exact Or.inr (Or.inr (Or.inr (Or.inl
          ⟨hik ▸ isKeyRelic_keyFor hwLo hwHi, hdLo, hdHi, rfl, hold, hnew⟩)))
      · exact Or.inl (getD_set_ne (by omega))
    · exact absurd hstep (by simp)
  | loot r =>
    simp only [step] at hstep
    split at hstep
    · rename_i hlegal
      have hdLo : 1 ≤ s.depth := hlegal.2.2.2.1
      have hhere : s.custody[r]? = some s.depth := hlegal.2.2.2.2.1
      cases hstep
      by_cases hir : i = r
      · -- ⚑ THE LOOTED RELIC CAME OUT OF ITS OWN MINTED HOME. `loot` demands it lies on
        -- the standing floor; `CustodyHomeWF` says the only floor code it can carry is
        -- its home; so the hop is EXACTLY `(homeCode i, CARRIED)`.
        have hold : s.custody.getD i 0 = s.depth := by
          rw [hir]; exact getD_eq_of_getElem?_eq_some hhere
        have hhomeEq : s.custody.getD i 0 = homeCode i := by
          rcases List.mem_append.mp (by
            simpa only [custodyAlphabet] using halpha) with hmem | hmem
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
            rcases hmem with h | h | h
            · exact h
            · exfalso; rw [hold] at h; omega
            · exfalso; rw [hold] at h; omega
          · exfalso
            by_cases hkey : isKeyRelic i = true
            · rw [if_pos hkey] at hmem
              obtain ⟨d, hd, hEq⟩ := List.mem_map.mp hmem
              have : d ≤ 4 := by
                have := List.mem_range'.mp (by simpa only [hangFloors] using hd)
                omega
              rw [hold] at hEq
              omega
            · rw [if_neg hkey] at hmem; cases hmem
        have hnew : (s.custody.set r CARRIED).getD i 0 = CARRIED := by
          rw [hir]; exact getD_set_self (by rw [← hir]; exact hilt)
        exact Or.inr (Or.inl ⟨hhomeEq, hnew⟩)
      · exact Or.inl (getD_set_ne (by omega))
    · exact absurd hstep (by simp)
  | take r =>
    simp only [step] at hstep
    split at hstep
    · rename_i hlegal
      have hdLo : 1 ≤ s.depth := hlegal.2.2.2.1
      have hhangs : s.custody[r]? = some (HUNG + s.depth) := hlegal.2.2.2.2.1
      cases hstep
      by_cases hir : i = r
      · have hold : s.custody.getD i 0 = HUNG + s.depth := by
          rw [hir]; exact getD_eq_of_getElem?_eq_some hhangs
        -- Only a KEY relic can carry a `HUNG` code, and `CustodyHomeWF` is what says so.
        have hkey : isKeyRelic i = true := by
          rcases hInv.2 i hi with h | h | h | ⟨hk, _⟩
          · exfalso
            rw [getElem?_eq_some_getD hlen hi, hold] at h
            have := Option.some.inj h; omega
          · exfalso
            rw [getElem?_eq_some_getD hlen hi, hold] at h
            have := Option.some.inj h; omega
          · exfalso
            rw [getElem?_eq_some_getD hlen hi, hold] at h
            have := Option.some.inj h; omega
          · exact hk
        have hnew : (s.custody.set r CARRIED).getD i 0 = CARRIED := by
          rw [hir]; exact getD_set_self (by rw [← hir]; exact hilt)
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hkey, hdLo, hdHi, rfl, hold, hnew⟩)))
      · exact Or.inl (getD_set_ne (by omega))
    · exact absurd hstep (by simp)
  | flee =>
    simp only [step] at hstep
    split at hstep
    · cases hstep
      by_cases hC : s.custody.getD i 0 = CARRIED
      · refine Or.inr (Or.inr (Or.inl ⟨hC, ?_⟩))
        show (s.custody.map (fun c => if c = CARRIED then BANKED else c)).getD i 0 = BANKED
        rw [getD_map_flee hilt, if_pos hC]
      · refine Or.inl ?_
        show (s.custody.map (fun c => if c = CARRIED then BANKED else c)).getD i 0
          = s.custody.getD i 0
        rw [getD_map_flee hilt, if_neg hC]
    · exact absurd hstep (by simp)

/-- ⚑ **THE HOP LAW — WHAT REPLACES THE RETIRED `custody_ratchet`.** Every legal step
moves every relic along one of the hops the deployed `allowedTransitions` tooth
enumerates. This is not the ratchet weakened to survive `take`: the ratchet said only
"never decreases", which ADMITTED `home → BANKED` (a relic teleporting out of a hoard
into the bank, skipping the pack and therefore skipping the capacity commons entirely).
The enumeration refuses that transition, and it names which verb owns each edge. -/
private theorem custody_hop_of_step {s s' : DState} {m : Move}
    (hInv : ModelProgramInv s) (hstep : step s m = some s')
    (i : Nat) (hi : i < RELICS) :
    (s.custody.getD i 0, s'.custody.getD i 0) ∈ custodyHops i := by
  have halpha := custody_getD_alphabet hInv i hi
  rcases custody_edge_of_step hInv hstep i hi with
    hstay | ⟨hold, hnew⟩ | ⟨hold, hnew⟩ | ⟨hkey, hdLo, hdHi, _, hold, hnew⟩
      | ⟨hkey, hdLo, hdHi, _, hold, hnew⟩
  · rw [hstay]; exact stay_mem_custodyHops halpha
  · rw [hold, hnew]
    simp only [custodyHops, List.mem_append]
    exact Or.inl (Or.inr (by simp))
  · rw [hold, hnew]
    simp only [custodyHops, List.mem_append]
    exact Or.inl (Or.inr (by simp))
  · rw [hold, hnew]; exact (hang_mem_custodyHops hkey hdLo hdHi).1
  · rw [hold, hnew]; exact (hang_mem_custodyHops hkey hdLo hdHi).2

open Dregg2.Exec in
private theorem rangeTeeth_honest {s : DState} (hInv : Inv s) (o : Value) :
    ∀ c ∈ rangeTeeth, evalConstraint c.toExec o (encode s) = true := by
  intro c hc
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hc
  apply (evalSimple_inRangeTwoSided_iff z 0 RELICS o (encode s)).2
  have hlen := hInv.1.1
  simp only [zones, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · refine ⟨pack s, by simp, by exact_mod_cast Nat.zero_le _, ?_⟩
    simp only [pack]
    exact_mod_cast (List.countP_le_length (l := s.custody)).trans_eq hlen
  · refine ⟨bank s, by simp, by exact_mod_cast Nat.zero_le _, ?_⟩
    simp only [bank]
    exact_mod_cast (List.countP_le_length (l := s.custody)).trans_eq hlen
  · refine ⟨hoardAt s 1, by simp, by exact_mod_cast Nat.zero_le _, ?_⟩
    simp only [hoardAt]
    exact_mod_cast (List.countP_le_length (l := s.custody)).trans_eq hlen
  · refine ⟨hoardAt s 2, by simp, by exact_mod_cast Nat.zero_le _, ?_⟩
    simp only [hoardAt]
    exact_mod_cast (List.countP_le_length (l := s.custody)).trans_eq hlen
  · refine ⟨hoardAt s 3, by simp, by exact_mod_cast Nat.zero_le _, ?_⟩
    simp only [hoardAt]
    exact_mod_cast (List.countP_le_length (l := s.custody)).trans_eq hlen
  · refine ⟨hoardAt s 4, by simp, by exact_mod_cast Nat.zero_le _, ?_⟩
    simp only [hoardAt]
    exact_mod_cast (List.countP_le_length (l := s.custody)).trans_eq hlen
  -- ⚑ The door residue: bounded by the PARTITION, not by a `countP` of its own. It is
  -- one register standing for four censuses, and `zones_total_of_inv` is exactly the
  -- statement that the seven zones partition the eight relics.
  · refine ⟨hungTotal s, by simp, by exact_mod_cast Nat.zero_le _, ?_⟩
    exact_mod_cast hungTotal_le_relics hInv

open Dregg2.Exec in
/-- The hop tooth, generically — stated over the PAIR so the case analysis lands on the
enumerated table rather than inside a record projection (the twin of
`depth_transition_pin`). -/
private theorem relic_transition_pin {s s' : DState} {i : Nat} (hi : i < RELICS)
    {al : List (Nat × Nat)}
    (hmem : (s.custody.getD i 0, s'.custody.getD i 0) ∈ al) :
    evalConstraint (Constraint.allowedTransitions (relicName i) al).toExec
      (encode s) (encode s') = true := by
  simp only [Constraint.toExec, evalConstraint]
  rw [encode_scalar_relic s i hi, encode_scalar_relic s' i hi]
  apply List.any_eq_true.mpr
  refine ⟨((s.custody.getD i 0 : Int), (s'.custody.getD i 0 : Int)),
    List.mem_map_of_mem hmem, by simp⟩

open Dregg2.Exec in
/-- ⚑ The per-relic provenance teeth, discharged against the HOP ENUMERATION rather than
the retired monotone atom: the exact edge the verb took, plus membership in the deployed
alphabet. -/
private theorem custodyTeeth_honest {s s' : DState} {m : Move}
    (hInv : ModelProgramInv s) (hstep : step s m = some s') :
    ∀ c ∈ custodyTeeth, evalConstraint c.toExec (encode s) (encode s') = true := by
  intro c hc
  obtain ⟨i, hiRange, hc⟩ := List.mem_flatMap.mp hc
  have hi : i < RELICS := List.mem_range.mp hiRange
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact relic_transition_pin hi (custody_hop_of_step hInv hstep i hi)
  · apply (evalSimple_memberOf_iff (relicName i)
      ((custodyAlphabet i).map (fun v => (v : Int))) (encode s) (encode s')).2
    refine ⟨(s'.custody.getD i 0 : Int), encode_scalar_relic s' i hi, ?_⟩
    have hmem := custody_getD_alphabet (modelProgramInv_step hInv hstep) i hi
    simpa using List.mem_map_of_mem (f := fun v : Nat => (v : Int)) hmem

open Dregg2.Exec in
/-- ⚑ **THE DOOR FRAME, ARRIVAL HALF — DISCHARGED.** `depth ≠ d ⇒ relic `i` did not NEWLY
arrive in floor `d`'s door. The three innocent readings are the three disjuncts, and
`custody_edge_of_step` hands us exactly one of them: the relic did not move (delta 0), or
it landed in the pack or the bank (neither is a `HUNG` code), or `unlock` hung it — in
which case the door it entered is THE FLOOR THE RUN IS STANDING ON, and the post-state
`depth` reads `d`. -/
private theorem doorArrivalTooth_honest {s s' : DState} {m : Move}
    (hInv : ModelProgramInv s) (hstep : step s m = some s')
    (i : Nat) (hi : i < RELICS) (d : Nat) (hdLo : 1 ≤ d) (_hdHi : d ≤ FLOORS) :
    evalConstraint (doorArrivalTooth i d).toExec (encode s) (encode s') = true := by
  have hHnum : (HUNG : Nat) = 12 := rfl
  have hCnum : (CARRIED : Nat) = 8 := rfl
  have hBnum : (BANKED : Nat) = 9 := rfl
  have hFnum : (FLOORS : Nat) = 4 := rfl
  have hhome : homeCode i ≤ FLOORS := homeCode_le_floors i hi
  -- The tooth is `anyOf [depth = d, ¬(relic i = HUNG + d), Δ relic i = 0]`.
  have hstand : (encode s').scalar "depth" = some ((d : Nat) : Int) →
      evalConstraint (doorArrivalTooth i d).toExec (encode s) (encode s') = true := by
    intro h
    simp only [doorArrivalTooth, Constraint.toExec, List.map_cons, List.map_nil,
      Simple.toExec, HeapAtom.toExecSimple, HeapKeyRef.field, evalConstraint,
      List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
    refine Or.inl ?_
    simp [evalSimple, h]
  have helse : s'.custody.getD i 0 ≠ HUNG + d →
      evalConstraint (doorArrivalTooth i d).toExec (encode s) (encode s') = true := by
    intro h
    simp only [doorArrivalTooth, Constraint.toExec, List.map_cons, List.map_nil,
      Simple.toExec, HeapAtom.toExecSimple, HeapKeyRef.field, evalConstraint,
      List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
    refine Or.inr (Or.inl ?_)
    simp only [evalSimple, encode_scalar_relic s' i hi, Bool.not_eq_true']
    exact beq_eq_false_iff_ne.mpr (by
      simp only [ne_eq, Option.some.injEq, Nat.cast_inj]
      exact h)
  have hfroze : s'.custody.getD i 0 = s.custody.getD i 0 →
      evalConstraint (doorArrivalTooth i d).toExec (encode s) (encode s') = true := by
    intro h
    simp only [doorArrivalTooth, Constraint.toExec, List.map_cons, List.map_nil,
      Simple.toExec, HeapAtom.toExecSimple, HeapKeyRef.field, evalConstraint,
      List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
    refine Or.inr (Or.inr ?_)
    simp only [evalSimple, encode_scalar_relic s i hi, encode_scalar_relic s' i hi, h]
    simp
  rcases custody_edge_of_step hInv hstep i hi with
    hstay | ⟨_, hnew⟩ | ⟨_, hnew⟩ | ⟨_, hdepthLo, hdepthHi, hdepthEq, _, hnew⟩
      | ⟨_, _, _, _, _, hnew⟩
  · exact hfroze hstay
  · exact helse (by rw [hnew]; omega)
  · exact helse (by rw [hnew]; omega)
  · by_cases heq : s.depth = d
    · refine hstand ?_
      rw [encode_scalar_depth, hdepthEq, heq]
    · exact helse (by rw [hnew]; omega)
  · exact helse (by rw [hnew]; omega)

open Dregg2.Exec in
/-- ⚑ **THE DOOR FRAME, DEPARTURE HALF — DISCHARGED.** `depth ≠ d ⇒ relic `i` did not make
the `HUNG + d → CARRIED` hop. This is the half that refuses THE REMOTE TAKE, and the proof
is exactly why the delta names the hop unambiguously: `CARRIED − (HUNG + d)` is NEGATIVE
and every other edge in `custody_edge_of_step` has a non-negative delta, so the only way to
satisfy it is `take`'s lift — whose floor is `s.depth`, and `take` does not move `depth`. -/
private theorem doorDepartureTooth_honest {s s' : DState} {m : Move}
    (hInv : ModelProgramInv s) (hstep : step s m = some s')
    (i : Nat) (hi : i < RELICS) (d : Nat) (hdLo : 1 ≤ d) (hdHi : d ≤ FLOORS) :
    evalConstraint (doorDepartureTooth i d).toExec (encode s) (encode s') = true := by
  have hHnum : (HUNG : Nat) = 12 := rfl
  have hCnum : (CARRIED : Nat) = 8 := rfl
  have hBnum : (BANKED : Nat) = 9 := rfl
  have hFnum : (FLOORS : Nat) = 4 := rfl
  have hhome : homeCode i ≤ FLOORS := homeCode_le_floors i hi
  have hstand : (encode s').scalar "depth" = some ((d : Nat) : Int) →
      evalConstraint (doorDepartureTooth i d).toExec (encode s) (encode s') = true := by
    intro h
    simp only [doorDepartureTooth, Constraint.toExec, List.map_cons, List.map_nil,
      Simple.toExec, HeapAtom.toExecSimple, HeapKeyRef.field, evalConstraint,
      List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
    refine Or.inl ?_
    simp [evalSimple, h]
  have hnotlift : ((s'.custody.getD i 0 : Int)
        ≠ (s.custody.getD i 0 : Int) + ((CARRIED : Int) - ((HUNG + d : Nat) : Int))) →
      evalConstraint (doorDepartureTooth i d).toExec (encode s) (encode s') = true := by
    intro h
    simp only [doorDepartureTooth, Constraint.toExec, List.map_cons, List.map_nil,
      Simple.toExec, HeapAtom.toExecSimple, HeapKeyRef.field, evalConstraint,
      List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
    refine Or.inr ?_
    simp only [evalSimple, encode_scalar_relic s i hi, encode_scalar_relic s' i hi,
      Bool.not_eq_true']
    exact beq_eq_false_iff_ne.mpr h
  rcases custody_edge_of_step hInv hstep i hi with
    hstay | ⟨hold, hnew⟩ | ⟨hold, hnew⟩ | ⟨_, _, _, _, hold, hnew⟩
      | ⟨_, hdepthLo, hdepthHi, hdepthEq, hold, hnew⟩
  · exact hnotlift (by rw [hstay]; omega)
  · exact hnotlift (by rw [hold, hnew]; omega)
  · exact hnotlift (by rw [hold, hnew]; omega)
  · exact hnotlift (by rw [hold, hnew]; push_cast; omega)
  · by_cases heq : s.depth = d
    · refine hstand ?_
      rw [encode_scalar_depth, hdepthEq, heq]
    · exact hnotlift (by rw [hold, hnew]; push_cast; omega)

open Dregg2.Exec in
/-- ⚑ **THE OBJECT-SIDE DOOR FRAME, DISCHARGED FOR EVERY VERB.** These 24 teeth ride the
`spent` rider, so an honest turn of ANY verb pays them — which is what makes "you must be
standing where it hangs" method-independent rather than a clause of `unlock`/`take`. -/
private theorem doorFrameTeeth_honest {s s' : DState} {m : Move}
    (hInv : ModelProgramInv s) (hstep : step s m = some s') :
    ∀ c ∈ doorFrameTeeth, evalConstraint c.toExec (encode s) (encode s') = true := by
  intro c hc
  obtain ⟨i, hiKey, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨d, hdMem, hc⟩ := List.mem_flatMap.mp hc
  have hi : i < RELICS := List.mem_range.mp (List.mem_filter.mp hiKey).1
  have hd : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 := by
    simpa using (hangFloors_eq ▸ hdMem : d ∈ [1, 2, 3, 4])
  have hdLo : 1 ≤ d := by rcases hd with rfl | rfl | rfl | rfl <;> decide
  have hdHi : d ≤ FLOORS := by rcases hd with rfl | rfl | rfl | rfl <;> decide
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact doorArrivalTooth_honest hInv hstep i hi d hdLo hdHi
  · exact doorDepartureTooth_honest hInv hstep i hi d hdLo hdHi

/-- A fixed eight-relic world can be exposed elementwise without assuming
anything about the elements.  This is only plumbing for reducing the deployed
fixed-key aggregate against `List.countP`; no game rule is hidden here. -/
private theorem list_length_eight {l : List Nat} (hlen : l.length = RELICS) :
    ∃ a b c d e f g h, l = [a, b, c, d, e, f, g, h] := by
  rcases l with _ | ⟨a, l⟩
  · simp at hlen
  rcases l with _ | ⟨b, l⟩
  · simp at hlen
  rcases l with _ | ⟨c, l⟩
  · simp at hlen
  rcases l with _ | ⟨d, l⟩
  · simp at hlen
  rcases l with _ | ⟨e, l⟩
  · simp at hlen
  rcases l with _ | ⟨f, l⟩
  · simp at hlen
  rcases l with _ | ⟨g, l⟩
  · simp at hlen
  rcases l with _ | ⟨h, tail⟩
  · simp at hlen
  cases tail with
  | nil => exact ⟨a, b, c, d, e, f, g, h, rfl⟩
  | cons x xs => simp [RELICS] at hlen

/-- The executor aggregate compares signed scalars, while the native game counts
`Nat` custody codes.  `Int.ofNat` is injective, so these are exactly the same
census -- no modular or truncating representation step is present. -/
private def countNatsAsIntsEq (l : List Nat) (needle : Nat) : Nat :=
  l.foldr (fun (x : Nat) n => if (x : Int) = (needle : Int) then n + 1 else n) 0

private theorem countNatsAsIntsEq_eq_countP (l : List Nat) (needle : Nat) :
    countNatsAsIntsEq l needle = l.countP (fun x => x == needle) := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    simp only [countNatsAsIntsEq, List.foldr, List.countP_cons]
    change (if (a : Int) = (needle : Int)
      then countNatsAsIntsEq rest needle + 1
      else countNatsAsIntsEq rest needle) =
        rest.countP (fun x => x == needle) + if (a == needle) = true then 1 else 0
    rw [ih]
    by_cases h : a = needle
    · subst needle
      simp
    · have hcast : (a : Int) ≠ (needle : Int) := fun heq => h (Int.ofNat_inj.mp heq)
      simp [h, hcast]

open Dregg2.Exec in
private theorem countScalarsEq_relicKeys_encode (s : DState) (hInv : Inv s)
    (needle : Nat) :
    countScalarsEq (encode s) (relicKeys.map HeapKeyRef.field) (needle : Int) =
      some (s.custody.countP (fun x => x == needle)) := by
  obtain ⟨a, b, c, d, e, f, g, h, hcustody⟩ := list_length_eight hInv.1.1
  have hcount := congrArg some
    (countNatsAsIntsEq_eq_countP [a, b, c, d, e, f, g, h] needle)
  simpa [countScalarsEq, countNatsAsIntsEq, relicKeys, range_relics,
    HeapKeyRef.field, hcustody] using hcount

open Dregg2.Exec in
/-- ⚑ The census teeth. SIX, and the door residue is not among them BY DERIVATION rather
than by omission: `hung` is pinned by conservation (`Σ zones = RELICS`) against these six
EXACT censuses plus the per-relic custody alphabet, so a seventh tooth would restate a
consequence — and could not be stated anyway, since `countFieldsEq` counts ONE value and
the door family is four. The per-FLOOR fact the four old registers carried moved onto the
relic (`doorArrivalTooth` / `doorDepartureTooth`), where it names the object that moved. -/
private theorem projectionTeeth_honest {s : DState} (hInv : Inv s) (o : Value) :
    ∀ c ∈ projectionTeeth, evalConstraint c.toExec o (encode s) = true := by
  intro c hc
  simp only [projectionTeeth, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · apply (evalConstraint_countFieldsEq_iff _ _ _ _ _).2
    exact ⟨pack s, countScalarsEq_relicKeys_encode s hInv CARRIED, encode_scalar_pack s⟩
  · apply (evalConstraint_countFieldsEq_iff _ _ _ _ _).2
    exact ⟨bank s, countScalarsEq_relicKeys_encode s hInv BANKED, encode_scalar_bank s⟩
  · apply (evalConstraint_countFieldsEq_iff _ _ _ _ _).2
    exact ⟨hoardAt s 1, countScalarsEq_relicKeys_encode s hInv 1,
      encode_scalar_hoard s 1 (by decide) (by decide)⟩
  · apply (evalConstraint_countFieldsEq_iff _ _ _ _ _).2
    exact ⟨hoardAt s 2, countScalarsEq_relicKeys_encode s hInv 2,
      encode_scalar_hoard s 2 (by decide) (by decide)⟩
  · apply (evalConstraint_countFieldsEq_iff _ _ _ _ _).2
    exact ⟨hoardAt s 3, countScalarsEq_relicKeys_encode s hInv 3,
      encode_scalar_hoard s 3 (by decide) (by decide)⟩
  · apply (evalConstraint_countFieldsEq_iff _ _ _ _ _).2
    exact ⟨hoardAt s 4, countScalarsEq_relicKeys_encode s hInv 4,
      encode_scalar_hoard s 4 (by decide) (by decide)⟩

open Dregg2.Exec in
private theorem spentRider_honest {s s' : DState} {m : Move}
    (hInv : ModelProgramInv s) (hstep : step s m = some s') :
    ∀ c ∈ spentRider.constraints,
      evalConstraint c.toExec (encode s) (encode s') = true := by
  intro c hc
  change c ∈ coreTeeth ++ rangeTeeth ++ custodyTeeth ++ doorFrameTeeth ++
    projectionTeeth ++ [.heapField .sentinel .immutable] at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with ((((hc | hc) | hc) | hc) | hc) | rfl
  · exact coreTeeth_honest hInv hstep c hc
  · exact rangeTeeth_honest (modelProgramInv_step hInv hstep).1 (encode s) c hc
  · exact custodyTeeth_honest hInv hstep c hc
  · exact doorFrameTeeth_honest hInv hstep c hc
  · exact projectionTeeth_honest (modelProgramInv_step hInv hstep).1 (encode s) c hc
  · simp [Constraint.toExec, HeapAtom.toExec, HeapKeyRef.field, evalConstraint,
      evalSimple]

open Dregg2.Exec in
private theorem case_all_of_constraints
    {cs : List Constraint} {o n : Value}
    (h : ∀ c ∈ cs, evalConstraint c.toExec o n = true) :
    (cs.map Constraint.toExec).all (fun c => evalConstraint c o n) = true := by
  apply List.all_eq_true.mpr
  intro ec hec
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hec
  exact h c hc

-- Guard-projection pins keep dispatch proofs from unfolding each case's large
-- constraint payload merely to expose its tiny guard.
@[simp] private theorem genesisCase_guard :
    genesisCase.guard = .methodIs "genesis" := rfl
@[simp] private theorem delveCase_guard : delveCase.guard = .methodIs "delve" := rfl
@[simp] private theorem unlockCase_guard : unlockCase.guard = .methodIs "unlock" := rfl
@[simp] private theorem smiteCase_guard : smiteCase.guard = .methodIs "smite" := rfl
@[simp] private theorem lootCase_guard : lootCase.guard = .methodIs "loot" := rfl
@[simp] private theorem fleeCase_guard : fleeCase.guard = .methodIs "flee" := rfl
@[simp] private theorem lungeCase_guard : lungeCase.guard = .methodIs "lunge" := rfl
@[simp] private theorem ascendCase_guard :
    ascendCase.guard = .methodIs "ascend" := rfl
@[simp] private theorem takeCase_guard : takeCase.guard = .methodIs "take" := rfl
@[simp] private theorem harmRider_guard :
    harmRider.guard = .slotChangedForMethods "harm" verbs := rfl
@[simp] private theorem depthRider_guard :
    depthRider.guard = .slotChangedForMethods "depth" verbs := rfl
@[simp] private theorem wayRider_guard (w : Nat) :
    (wayRider w).guard = .slotChangedForMethods (wayName w) verbs := rfl
@[simp] private theorem fateRider_guard :
    fateRider.guard = .slotChangedForMethods "fate" verbs := rfl
@[simp] private theorem bankRider_guard :
    bankRider.guard = .slotChangedForMethods "bank" verbs := rfl
@[simp] private theorem spentRider_guard :
    spentRider.guard = .slotChangedForMethods "spent" verbs := rfl

open Dregg2.Exec in
private theorem cases_admit_of {tcs : List TransitionCase} {method : Nat}
    {o n : Value}
    (hsome : ∃ tc ∈ tcs, tc.guard.matches method o n = true)
    (hall : ∀ tc ∈ tcs, tc.guard.matches method o n = true →
      tc.constraints.all (fun c => evalConstraint c o n) = true) :
    RecordProgram.admits (.cases tcs) method o n = true := by
  simp only [RecordProgram.admits]
  cases hf : tcs.filter (fun tc => tc.guard.matches method o n) with
  | nil =>
    obtain ⟨tc, hmem, hmatch⟩ := hsome
    have hmemf : tc ∈ tcs.filter (fun tc => tc.guard.matches method o n) :=
      List.mem_filter.mpr ⟨hmem, hmatch⟩
    rw [hf] at hmemf
    exact absurd hmemf (by simp)
  | cons first rest =>
    apply List.all_eq_true.mpr
    intro tc htc
    have htcFilter : tc ∈ tcs.filter (fun tc => tc.guard.matches method o n) := by
      rw [hf]
      exact htc
    apply hall tc
    · exact (List.mem_filter.mp htcFilter).1
    · exact (List.mem_filter.mp htcFilter).2

private theorem wayOpen_getD_one {s : DState} {d : Nat} (hd : 2 ≤ d)
    (hopen : wayOpen s d = true) : s.ways.getD (d - 2) 0 = 1 := by
  have hdNot : ¬ d ≤ 1 := by omega
  rw [wayOpen, if_neg hdNot] at hopen
  cases hget : s.ways[d - 2]? with
  | none => simp [hget] at hopen
  | some v =>
    have hv : v = 1 := by simpa [hget] using hopen
    rw [List.getD_eq_getElem?_getD, hget]
    exact hv

private theorem countP_set_bump_local {l : List Nat} {i a v : Nat}
    (p : Nat → Bool) (hget : l[i]? = some a) (hpa : p a = false)
    (hpv : p v = true) : (l.set i v).countP p = l.countP p + 1 := by
  induction l generalizing i with
  | nil => simp at hget
  | cons hd tl ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      simp [List.set, hpa, hpv]
    | succ j =>
      simp only [List.getElem?_cons_succ] at hget
      simp only [List.set, List.countP_cons, ih hget]
      omega

private theorem countP_set_same_local {l : List Nat} {i a v : Nat}
    (p : Nat → Bool) (hget : l[i]? = some a) (heq : p a = p v) :
    (l.set i v).countP p = l.countP p := by
  induction l generalizing i with
  | nil => simp at hget
  | cons hd tl ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      simp only [List.set, List.countP_cons, heq]
    | succ j =>
      simp only [List.getElem?_cons_succ] at hget
      simp only [List.set, List.countP_cons, ih hget]

private theorem countP_flee_carried_local (l : List Nat) :
    (l.map (fun c => if c = CARRIED then BANKED else c)).countP
      (· == CARRIED) = 0 := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.map_cons, List.countP_cons, ih]
    by_cases h : hd = CARRIED
    · simp [h, show BANKED ≠ CARRIED by decide]
    · simp [h]

private theorem countP_flee_banked_local (l : List Nat) :
    (l.map (fun c => if c = CARRIED then BANKED else c)).countP
      (· == BANKED) =
      l.countP (· == CARRIED) + l.countP (· == BANKED) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.map_cons, List.countP_cons, List.countP_cons, List.countP_cons, ih]
    by_cases hC : hd = CARRIED
    · subst hd
      simp [show CARRIED ≠ BANKED by decide]
      omega
    · by_cases hB : hd = BANKED
      · subst hd
        simp [hC]
        omega
      · simp [hC, hB]

private theorem countP_flee_floor_local (l : List Nat) (d : Nat)
    (hdC : d ≠ CARRIED) (hdB : d ≠ BANKED) :
    (l.map (fun c => if c = CARRIED then BANKED else c)).countP (· == d) =
      l.countP (· == d) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.map_cons, List.countP_cons, List.countP_cons, ih]
    by_cases hC : hd = CARRIED
    · subst hd
      simp [Ne.symm hdC, Ne.symm hdB]
    · simp [hC]

open Dregg2.Exec in
private theorem delve_wayTooth_honest {s s' : DState}
    (hstep : step s .delve = some s') (d : Nat) (hdLo : 2 ≤ d)
    (hdHi : d ≤ FLOORS) :
    evalConstraint (wayTooth d).toExec (encode s) (encode s') = true := by
  simp only [step] at hstep
  split at hstep
  · rename_i hc
    cases hstep
    by_cases heq : s.depth + 1 = d
    · have hopen : wayOpen s d = true := by simpa [heq] using hc.2.2.2.2.1
      have hway := wayOpen_getD_one hdLo hopen
      simp only [wayTooth, Constraint.toExec, List.map_cons, List.map_nil,
        Simple.toExec, evalConstraint, List.any_cons, List.any_nil, Bool.or_false]
      simp only [Bool.or_eq_true]
      right
      unfold evalSimple
      rw [encode_scalar_way _ d hdLo hdHi, hway]
      rfl
    · simp only [wayTooth, Constraint.toExec, List.map_cons, List.map_nil,
        Simple.toExec, evalConstraint, List.any_cons, List.any_nil, Bool.or_false]
      simp only [Bool.or_eq_true]
      left
      simp only [evalSimple]
      rw [encode_scalar_depth]
      have hz : ((s.depth + 1 : Nat) : Int) ≠ (d : Int) := by
        exact_mod_cast heq
      simpa using hz
  · exact absurd hstep (by simp)

open Dregg2.Exec in
/-- The staircase tooth, generically: if the actual `(old depth, new depth)` pair is one of
the table's rungs, the tooth passes. Stated over the PAIR so the case analysis lands on
closed numerals instead of inside a record projection. -/
private theorem depth_transition_pin {s s' : DState} {al : List (Nat × Nat)}
    (hmem : (s.depth, s'.depth) ∈ al) :
    evalConstraint (Constraint.allowedTransitions "depth" al).toExec
      (encode s) (encode s') = true := by
  simp only [Constraint.toExec, evalConstraint]
  rw [encode_scalar_depth, encode_scalar_depth]
  apply List.any_eq_true.mpr
  refine ⟨((s.depth : Int), (s'.depth : Int)), List.mem_map_of_mem hmem, by simp⟩

open Dregg2.Exec in
/-- ⚑ The DOOR-RESIDUE tooth, generically — the twin of `depth_transition_pin`, one zone
over. `unlock` and `take` are the only verbs that post a rung here, and each posts exactly
one: `(k, k+1)` hangs a key, `(k, k−1)` lifts one. Stated over the PAIR for the same reason
the staircase is. -/
private theorem hung_transition_pin {s s' : DState} {al : List (Nat × Nat)}
    (hmem : (hungTotal s, hungTotal s') ∈ al) :
    evalConstraint (Constraint.allowedTransitions hungName al).toExec
      (encode s) (encode s') = true := by
  simp only [Constraint.toExec, evalConstraint]
  rw [encode_scalar_hung, encode_scalar_hung]
  apply List.any_eq_true.mpr
  refine ⟨((hungTotal s : Int), (hungTotal s' : Int)), List.mem_map_of_mem hmem, by simp⟩

open Dregg2.Exec in
/-- The staircase tooth, DESCENDING: `d → d + 1` is one of the eight enumerated rungs
because the delve guard already pins `d < FLOORS`. -/
private theorem delve_depthTransition_honest {s s' : DState}
    (hstep : step s .delve = some s') :
    evalConstraint (Constraint.allowedTransitions "depth"
        [(0, 1), (1, 2), (2, 3), (3, 4), (1, 0), (2, 1), (3, 2), (4, 3)]).toExec
      (encode s) (encode s') = true := by
  simp only [step] at hstep
  split at hstep
  · rename_i hc
    have hlt : s.depth < 4 := hc.2.2.2.1
    cases hstep
    refine depth_transition_pin ?_
    show (s.depth, s.depth + 1) ∈ _
    have hcases : s.depth = 0 ∨ s.depth = 1 ∨ s.depth = 2 ∨ s.depth = 3 := by
      omega
    rcases hcases with h | h | h | h <;> rw [h] <;> decide
  · exact absurd hstep (by simp)

open Dregg2.Exec in
/-- The staircase tooth, ASCENDING: `d → d − 1` is one of the eight enumerated rungs
because the ascend guard pins `1 ≤ d` and the invariant pins `d ≤ FLOORS`. -/
private theorem ascend_depthTransition_honest {s s' : DState}
    (hInv : ModelProgramInv s) (hstep : step s .ascend = some s') :
    evalConstraint (Constraint.allowedTransitions "depth"
        [(0, 1), (1, 2), (2, 3), (3, 4), (1, 0), (2, 1), (3, 2), (4, 3)]).toExec
      (encode s) (encode s') = true := by
  have hhi : s.depth ≤ 4 := hInv.1.2.2.1
  simp only [step] at hstep
  split at hstep
  · rename_i hc
    have hlo : 1 ≤ s.depth := hc.2.2.2
    cases hstep
    refine depth_transition_pin ?_
    show (s.depth, s.depth - 1) ∈ _
    have hcases : s.depth = 1 ∨ s.depth = 2 ∨ s.depth = 3 ∨ s.depth = 4 := by
      omega
    rcases hcases with h | h | h | h <;> rw [h] <;> decide
  · exact absurd hstep (by simp)

open Dregg2.Exec in
/-- The way-tooth on an ASCENT: the floor you land on is one you already stood on, so
its way is open by `Dungeon.WaysBehind` — the invariant clause `ascend` exists for. -/
private theorem ascend_wayTooth_honest {s s' : DState}
    (hInv : ModelProgramInv s) (hstep : step s .ascend = some s')
    (d : Nat) (hdLo : 2 ≤ d) (hdHi : d ≤ FLOORS) :
    evalConstraint (wayTooth d).toExec (encode s) (encode s') = true := by
  have hwb : WaysBehind s := inv_waysBehind hInv.1
  simp only [step] at hstep
  split at hstep
  · rename_i hc
    have hlo : 1 ≤ s.depth := hc.2.2.2
    cases hstep
    by_cases heq : s.depth - 1 = d
    · have hopen : wayOpen s d = true := hwb d hdLo (by omega)
      have hway := wayOpen_getD_one hdLo hopen
      simp only [wayTooth, Constraint.toExec, List.map_cons, List.map_nil,
        Simple.toExec, evalConstraint, List.any_cons, List.any_nil, Bool.or_false]
      simp only [Bool.or_eq_true]
      right
      unfold evalSimple
      rw [encode_scalar_way _ d hdLo hdHi, hway]
      rfl
    · simp only [wayTooth, Constraint.toExec, List.map_cons, List.map_nil,
        Simple.toExec, evalConstraint, List.any_cons, List.any_nil, Bool.or_false]
      simp only [Bool.or_eq_true]
      left
      simp only [evalSimple]
      rw [encode_scalar_depth]
      have hz : ((s.depth - 1 : Nat) : Int) ≠ (d : Int) := by exact_mod_cast heq
      simpa using hz
  · exact absurd hstep (by simp)

open Dregg2.Exec in
/-- **Every honest climb is admitted** — its own arm, plus the depth rider its write
summons and the spent rider every exertion summons. -/
private theorem ascendCase_honest {s s' : DState}
    (hInv : ModelProgramInv s) (hstep : step s .ascend = some s') :
    (ascendCase.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true := by
  apply case_all_of_constraints
  intro c hc
  change c ∈ coreTeeth ++
    [.fieldDelta "spent" 1,
      .allowedTransitions "depth" [(1, 0), (2, 1), (3, 2), (4, 3)],
      .fieldEquals "wounds" 0, .fieldEquals "fate" 0,
      wayTooth 2, wayTooth 3, wayTooth 4] ++
    frozen ["pack", "bank", wayName 2, wayName 3, wayName 4, "harm",
      hoardName 1, hoardName 2, hoardName 3, hoardName 4,
      hungName] ++ relicFreeze at hc
  simp only [List.mem_append] at hc
  rcases hc with ((hcore | hverb) | hfrozen) | hrelic
  · exact coreTeeth_honest hInv hstep c hcore
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hverb
    rcases hverb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [Constraint.toExec, evalConstraint]
      unfold evalSimple
      rw [encode_scalar_spent, encode_scalar_spent]
      rw [legal_step_spent_eq hstep]
      simp [price]
    · have hhi : s.depth ≤ 4 := hInv.1.2.2.1
      simp only [step] at hstep
      split at hstep
      · rename_i hc2
        have hlo : 1 ≤ s.depth := hc2.2.2.2
        cases hstep
        refine depth_transition_pin ?_
        show (s.depth, s.depth - 1) ∈ _
        have hcases : s.depth = 1 ∨ s.depth = 2 ∨ s.depth = 3 ∨ s.depth = 4 := by
          omega
        rcases hcases with h | h | h | h <;> rw [h] <;> decide
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
      · exact absurd hstep (by simp)
    · have hf := (legal_step_fate hstep).1
      simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple, hf]
      · exact absurd hstep (by simp)
    · exact ascend_wayTooth_honest hInv hstep 2 (by decide) (by decide)
    · exact ascend_wayTooth_honest hInv hstep 3 (by decide) (by decide)
    · exact ascend_wayTooth_honest hInv hstep 4 (by decide) (by decide)
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hfrozen
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals
      simp only [step] at hstep
      split at hstep
      · cases hstep
        simp [Constraint.toExec, evalConstraint, evalSimple, pack, bank, hoardAt, hungTotal,
              hangFloors_eq, hungAt]
      · exact absurd hstep (by simp)
  · obtain ⟨i, hiRange, rfl⟩ := List.mem_map.mp hrelic
    have hi : i < RELICS := List.mem_range.mp hiRange
    simp only [step] at hstep
    split at hstep
    · cases hstep
      simp only [Constraint.toExec, HeapAtom.toExec, HeapKeyRef.field, evalConstraint]
      unfold evalSimple
      rw [encode_scalar_relic s i hi, encode_scalar_relic _ i hi]
      change (some (s.custody.getD i 0 : Int) ==
        some (s.custody.getD i 0 : Int)) = true
      simp
    · exact absurd hstep (by simp)

open Dregg2.Exec in
private theorem depthRider_ascend_honest {s s' : DState}
    (hInv : ModelProgramInv s) (hstep : step s .ascend = some s') :
    (depthRider.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true := by
  apply case_all_of_constraints
  intro c hc
  change c ∈ coreTeeth ++ [.allowedTransitions "depth"
      [(0, 1), (1, 2), (2, 3), (3, 4), (1, 0), (2, 1), (3, 2), (4, 3)],
    .fieldEquals "wounds" 0, wayTooth 2, wayTooth 3, wayTooth 4] at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with hcore | rfl | rfl | rfl | rfl | rfl
  · exact coreTeeth_honest hInv hstep c hcore
  · exact ascend_depthTransition_honest hInv hstep
  · simp only [step] at hstep
    split at hstep
    · cases hstep
      simp [Constraint.toExec, evalConstraint, evalSimple]
    · exact absurd hstep (by simp)
  · exact ascend_wayTooth_honest hInv hstep 2 (by decide) (by decide)
  · exact ascend_wayTooth_honest hInv hstep 3 (by decide) (by decide)
  · exact ascend_wayTooth_honest hInv hstep 4 (by decide) (by decide)

open Dregg2.Exec in
private theorem delveCase_honest {s s' : DState}
    (hInv : ModelProgramInv s) (hstep : step s .delve = some s') :
    (delveCase.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true := by
  apply case_all_of_constraints
  intro c hc
  change c ∈ coreTeeth ++
    [.fieldDelta "spent" 1, .fieldDelta "depth" 1,
      .fieldEquals "wounds" 0, .fieldEquals "fate" 0,
      wayTooth 2, wayTooth 3, wayTooth 4] ++
    frozen ["pack", "bank", wayName 2, wayName 3, wayName 4, "harm",
      hoardName 1, hoardName 2, hoardName 3, hoardName 4,
      hungName] ++ relicFreeze at hc
  simp only [List.mem_append] at hc
  rcases hc with ((hcore | hverb) | hfrozen) | hrelic
  · exact coreTeeth_honest hInv hstep c hcore
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hverb
    rcases hverb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [Constraint.toExec, evalConstraint]
      unfold evalSimple
      rw [encode_scalar_spent, encode_scalar_spent]
      rw [legal_step_spent_eq hstep]
      simp [price]
    · simp only [step] at hstep
      split at hstep
      · rename_i hlegal
        cases hstep
        simp [Constraint.toExec, evalConstraint, evalSimple, hlegal.1]
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
      · exact absurd hstep (by simp)
    · have hf := (legal_step_fate hstep).1
      simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple, hf]
      · exact absurd hstep (by simp)
    · exact delve_wayTooth_honest hstep 2 (by decide) (by decide)
    · exact delve_wayTooth_honest hstep 3 (by decide) (by decide)
    · exact delve_wayTooth_honest hstep 4 (by decide) (by decide)
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hfrozen
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals
      simp only [step] at hstep
      split at hstep
      · cases hstep
        simp [Constraint.toExec, evalConstraint, evalSimple, pack, bank, hoardAt, hungTotal,
              hangFloors_eq, hungAt]
      · exact absurd hstep (by simp)
  · obtain ⟨i, hiRange, rfl⟩ := List.mem_map.mp hrelic
    have hi : i < RELICS := List.mem_range.mp hiRange
    simp only [step] at hstep
    split at hstep
    · cases hstep
      simp only [Constraint.toExec, HeapAtom.toExec, HeapKeyRef.field, evalConstraint]
      unfold evalSimple
      rw [encode_scalar_relic s i hi, encode_scalar_relic _ i hi]
      change (some (s.custody.getD i 0 : Int) ==
        some (s.custody.getD i 0 : Int)) = true
      simp
    · exact absurd hstep (by simp)

open Dregg2.Exec in
private theorem depthRider_delve_honest {s s' : DState}
    (hInv : ModelProgramInv s) (hstep : step s .delve = some s') :
    (depthRider.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true := by
  apply case_all_of_constraints
  intro c hc
  change c ∈ coreTeeth ++ [.allowedTransitions "depth"
      [(0, 1), (1, 2), (2, 3), (3, 4), (1, 0), (2, 1), (3, 2), (4, 3)],
    .fieldEquals "wounds" 0, wayTooth 2, wayTooth 3, wayTooth 4] at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with hcore | rfl | rfl | rfl | rfl | rfl
  · exact coreTeeth_honest hInv hstep c hcore
  · exact delve_depthTransition_honest hstep
  · simp only [step] at hstep
    split at hstep
    · cases hstep
      simp [Constraint.toExec, evalConstraint, evalSimple]
    · exact absurd hstep (by simp)
  · exact delve_wayTooth_honest hstep 2 (by decide) (by decide)
  · exact delve_wayTooth_honest hstep 3 (by decide) (by decide)
  · exact delve_wayTooth_honest hstep 4 (by decide) (by decide)

open Dregg2.Exec in
/-- First positive completeness rung: every honest model delve satisfies its verb
arm and every matching cross-method rider in the authored record program. -/
theorem modelProgram_delve_admitted {s s' : DState}
    (hInv : ModelProgramInv s) (hstep : step s .delve = some s') :
    RecordProgram.admits dungeonExec (moveIdx .delve)
      (encode s) (encode s') = true := by
  have hDelve := delveCase_honest hInv hstep
  have hDepth := depthRider_delve_honest hInv hstep
  have hSpent : (spentRider.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true :=
    case_all_of_constraints (spentRider_honest hInv hstep)
  simp only [step] at hstep
  split at hstep
  · have hs' : s' =
        { depth := s.depth + 1, spent := s.spent + 1, wounds := 0, harm := s.harm,
          fate := s.fate, ways := s.ways, custody := s.custody } :=
      (Option.some.inj hstep).symm
    have hfilter :
        (programCases.map Case.toExec).filter (fun tc =>
          tc.guard.matches (moveIdx .delve) (encode s)
            (encode s')) =
          [delveCase.toExec, depthRider.toExec, spentRider.toExec] := by
      simp [programCases, genesisCase, delveCase, unlockCase, smiteCase, lootCase,
        fleeCase, lungeCase, ascendCase, takeCase, depthRider, wayRider, fateRider,
        bankRider, harmRider, spentRider,
        Case.toExec, Guard.toExec, methodIdx, TransitionGuard.matches,
        Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch, verbs, bank, moveIdx, hs']
    simp only [dungeonExec, dungeonProgram, CellProgram.toExec,
      RecordProgram.admits, hfilter, List.all_cons, List.all_nil,
      Bool.and_true, hDelve, hDepth, hSpent]
  · exact absurd hstep (by simp)

open Dregg2.Exec in
/-- The mirror of `countP_set_bump_local`, for the write that takes a relic OUT of a
class — `unlock` moving a key from `CARRIED` into the door. -/
private theorem countP_set_drop_local {l : List Nat} {i a v : Nat}
    (p : Nat → Bool) (hget : l[i]? = some a) (hpa : p a = true)
    (hpv : p v = false) : (l.set i v).countP p + 1 = l.countP p := by
  induction l generalizing i with
  | nil => simp at hget
  | cons hd tl ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      simp [List.set, hpa, hpv]
    | succ j =>
      simp only [List.getElem?_cons_succ] at hget
      simp only [List.set, List.countP_cons, ← ih hget]
      omega

private theorem countP_pos_of_getElem_local {l : List Nat} {i v : Nat}
    (hget : l[i]? = some v) : 1 ≤ l.countP (· == v) := by
  induction l generalizing i with
  | nil => simp at hget
  | cons hd tl ih =>
    rw [List.countP_cons]
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      simp
    | succ j =>
      have := ih (by simpa using hget)
      omega

open Dregg2.Exec in
/-- ⚑ **THE CARRY SLOT COMES BACK.** `unlock` moves the key out of the pack, so `pack`
drops by exactly one — and `pack ≥ 1` is not an extra assumption, it is the exhibited
key: the enumeration `(k, k−1)` has no `(0, ·)` rung, which IS the deployed form of
"you must be holding the key". -/
private theorem unlock_pack_drop {s s' : DState} {w : Nat}
    (hInv : ModelProgramInv s) (hstep : step s (.unlock w) = some s') :
    1 ≤ pack s ∧ pack s ≤ RELICS ∧ pack s' + 1 = pack s := by
  have hlen : s.custody.length = RELICS := hInv.1.1.1
  simp only [step] at hstep
  split at hstep
  · rename_i hlegal
    have hkeyC : s.custody[keyFor w]? = some CARRIED := hlegal.2.2.2.2.2.2.2
    have hHC : ((HUNG + s.depth) == CARRIED) = false := by
      have hH : (HUNG : Nat) = 12 := rfl
      have hC : (CARRIED : Nat) = 8 := rfl
      exact beq_eq_false_iff_ne.mpr (by omega)
    have hdrop := countP_set_drop_local (l := s.custody) (i := keyFor w)
      (a := CARRIED) (v := HUNG + s.depth) (· == CARRIED) hkeyC (by simp) hHC
    cases hstep
    refine ⟨countP_pos_of_getElem_local hkeyC, ?_, ?_⟩
    · simp only [pack]
      exact (List.countP_le_length (l := s.custody)).trans_eq hlen
    · simpa only [pack] using hdrop
  · exact absurd hstep (by simp)

open Dregg2.Exec in
/-- ⚑ **THE DOOR CENSUS GAINS EXACTLY ONE.** `unlock` hangs the key it exercises in the
door on the floor it is standing on, so the residue rises by one at `s.depth` and is frozen
on every other floor. WHICH door it entered is no longer a counter fact — it is
`doorArrivalTooth`, on the object, discharged for every verb by `doorFrameTeeth_honest`. -/
private theorem unlock_hungTotal_bump {s s' : DState} {w : Nat}
    (hInv : ModelProgramInv s) (hstep : step s (.unlock w) = some s') :
    hungTotal s' = hungTotal s + 1 := by
  have hH : (HUNG : Nat) = 12 := rfl
  have hC : (CARRIED : Nat) = 8 := rfl
  have hdHi : s.depth ≤ FLOORS := hInv.1.2.2.1
  have hF : (FLOORS : Nat) = 4 := rfl
  simp only [step] at hstep
  split at hstep
  · rename_i hlegal
    have hdLo : 1 ≤ s.depth := hlegal.2.2.2.1
    have hkeyC : s.custody[keyFor w]? = some CARRIED := hlegal.2.2.2.2.2.2.2
    have hcust : s'.custody = s.custody.set (keyFor w) (HUNG + s.depth) := by
      rw [← Option.some.inj hstep]
    have hAt : ∀ e : Nat, hungAt s' e
        = hungAt s e + (if e = s.depth then 1 else 0) := by
      intro e
      simp only [hungAt, hcust]
      by_cases he : e = s.depth
      · subst he
        rw [if_pos rfl]
        exact countP_set_bump_local _ hkeyC (beq_eq_false_iff_ne.mpr (by omega)) (by simp)
      · rw [if_neg he, Nat.add_zero]
        exact countP_set_same_local _ hkeyC (by
          have h1 : ((CARRIED : Nat) == HUNG + e) = false :=
            beq_eq_false_iff_ne.mpr (by omega)
          have h2 : ((HUNG + s.depth) == HUNG + e) = false :=
            beq_eq_false_iff_ne.mpr (by omega)
          rw [h1, h2])
    have hd : s.depth = 1 ∨ s.depth = 2 ∨ s.depth = 3 ∨ s.depth = 4 := by omega
    have := hungTotal_eq_of (s := s) (s' := s') (j := 0) (k := 1)
      (by rw [hAt 1, hAt 2, hAt 3, hAt 4]
          rcases hd with h | h | h | h <;> rw [h] <;> simp <;> omega)
    omega
  · exact absurd hstep (by simp)

open Dregg2.Exec in
/-- ⚑ **THE UNLOCK ARM.** It no longer freezes `pack` and no longer freezes the relics:
`unlock` is one of the two verbs that move a custody code, and both counters it touches
are pinned exactly (the pack enumeration above, the standing floor's door here). -/
private theorem unlockCase_honest {s s' : DState} {w : Nat}
    (hInv : ModelProgramInv s) (hstep : step s (.unlock w) = some s') :
    (unlockCase.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true := by
  have hH : (HUNG : Nat) = 12 := rfl
  have hC : (CARRIED : Nat) = 8 := rfl
  have hB : (BANKED : Nat) = 9 := rfl
  have hF : (FLOORS : Nat) = 4 := rfl
  apply case_all_of_constraints
  intro c hc
  change c ∈ coreTeeth ++
    [.fieldDelta "spent" 1, .fieldEquals "fate" 0,
      .allowedTransitions "pack" ((List.range' 1 RELICS).map (fun k => (k, k - 1))),
      .allowedTransitions hungName ((List.range' 0 RELICS).map (fun k => (k, k + 1)))] ++
    frozen ["depth", "wounds", "bank", "harm",
      hoardName 1, hoardName 2, hoardName 3, hoardName 4] at hc
  simp only [List.mem_append] at hc
  rcases hc with (hcore | hverb) | hfrozen
  · exact coreTeeth_honest hInv hstep c hcore
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hverb
    rcases hverb with rfl | rfl | rfl | rfl
    · simp only [Constraint.toExec, evalConstraint]
      unfold evalSimple
      rw [encode_scalar_spent, encode_scalar_spent, legal_step_spent_eq hstep]
      simp [price]
    · simp only [step] at hstep
      split at hstep
      · rename_i hlegal
        cases hstep
        simp [Constraint.toExec, evalConstraint, evalSimple, hlegal.1]
      · exact absurd hstep (by simp)
    · obtain ⟨hpos, hle, hdrop⟩ := unlock_pack_drop hInv hstep
      have hrelics : (RELICS : Nat) = 8 := rfl
      simp only [Constraint.toExec, evalConstraint]
      rw [encode_scalar_pack, encode_scalar_pack]
      apply List.any_eq_true.mpr
      refine ⟨((pack s : Int), (pack s' : Int)), ?_, by simp⟩
      refine List.mem_map.mpr ⟨(pack s, pack s'), ?_, by simp⟩
      refine List.mem_map.mpr ⟨pack s, ?_, ?_⟩
      · -- `pack ≥ 1` is not an extra premise: it IS the exhibited key, and the
        -- enumeration has no `(0, ·)` rung.
        have hlist : (List.range' 1 RELICS) = [1, 2, 3, 4, 5, 6, 7, 8] := by decide
        rw [hlist]
        have hc : pack s = 1 ∨ pack s = 2 ∨ pack s = 3 ∨ pack s = 4 ∨ pack s = 5
            ∨ pack s = 6 ∨ pack s = 7 ∨ pack s = 8 := by omega
        rcases hc with h|h|h|h|h|h|h|h <;> rw [h] <;> simp
      · have hsub : pack s - 1 = pack s' := by omega
        rw [hsub]
    · -- ⚑ THE DOOR RESIDUE GAINS EXACTLY ONE. The upper rung `(7, 8)` is reachable only in
      -- principle: the residue is bounded by the partition it belongs to
      -- (`hungTotal_le_relics` on the POST state), so the pair is always on the table.
      have hbump := unlock_hungTotal_bump hInv hstep
      have hle : hungTotal s' ≤ RELICS :=
        hungTotal_le_relics (modelProgramInv_step hInv hstep).1
      have hrelics : (RELICS : Nat) = 8 := rfl
      refine hung_transition_pin ?_
      have hlist : (List.range' 0 RELICS) = [0, 1, 2, 3, 4, 5, 6, 7] := by decide
      rw [hlist]
      have hcases : hungTotal s = 0 ∨ hungTotal s = 1 ∨ hungTotal s = 2 ∨ hungTotal s = 3
          ∨ hungTotal s = 4 ∨ hungTotal s = 5 ∨ hungTotal s = 6 ∨ hungTotal s = 7 := by
        omega
      rcases hcases with h|h|h|h|h|h|h|h <;> rw [hbump, h] <;> simp
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hfrozen
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    -- depth / wounds / harm are registers this verb does not write; `bank` and the four
    -- hoards ARE custody projections, and the write is `CARRIED → HUNG + depth`, which
    -- lands in neither class.
    simp only [step] at hstep
    split at hstep
    · rename_i hlegal
      have hkeyC : s.custody[keyFor w]? = some CARRIED := hlegal.2.2.2.2.2.2.2
      have hdHi : s.depth ≤ FLOORS := hInv.1.2.2.1
      have hbankSame : (s.custody.set (keyFor w) (HUNG + s.depth)).countP (· == BANKED)
          = s.custody.countP (· == BANKED) :=
        countP_set_same_local _ hkeyC
          (by
            have h1 : ((CARRIED : Nat) == BANKED) = false :=
              beq_eq_false_iff_ne.mpr (by omega)
            have h2 : ((HUNG + s.depth) == BANKED) = false :=
              beq_eq_false_iff_ne.mpr (by omega)
            rw [h1, h2])
      have hhoardSame : ∀ d : Nat, d ≤ FLOORS →
          (s.custody.set (keyFor w) (HUNG + s.depth)).countP (· == d)
            = s.custody.countP (· == d) := by
        intro d hd
        refine countP_set_same_local _ hkeyC ?_
        have h1 : ((CARRIED : Nat) == d) = false := beq_eq_false_iff_ne.mpr (by omega)
        have h2 : ((HUNG + s.depth) == d) = false := beq_eq_false_iff_ne.mpr (by omega)
        rw [h1, h2]
      cases hstep
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [Constraint.toExec, evalConstraint, evalSimple]
      · simp [Constraint.toExec, evalConstraint, evalSimple]
      · simpa [Constraint.toExec, evalConstraint, evalSimple, bank] using hbankSame
      · simp [Constraint.toExec, evalConstraint, evalSimple]
      · simpa [Constraint.toExec, evalConstraint, evalSimple, hoardAt] using
          hhoardSame 1 (by decide)
      · simpa [Constraint.toExec, evalConstraint, evalSimple, hoardAt] using
          hhoardSame 2 (by decide)
      · simpa [Constraint.toExec, evalConstraint, evalSimple, hoardAt] using
          hhoardSame 3 (by decide)
      · simpa [Constraint.toExec, evalConstraint, evalSimple, hoardAt] using
          hhoardSame 4 (by decide)
    · exact absurd hstep (by simp)

open Dregg2.Exec in
/-- ⚑ **THE FLOOR HALF OF THE WAY LAW.** `depth = d ⇒ relic k hangs on floor d` — the
deployed form of `Dungeon.key_hangs_where_it_was_turned`. -/
private theorem unlock_keyHangsHere_honest {s s' : DState} {w d : Nat}
    (hInv : ModelProgramInv s) (hstep : step s (.unlock w) = some s') :
    evalConstraint (keyHangsHereTooth (keyFor w) d).toExec
      (encode s) (encode s') = true := by
  simp only [step] at hstep
  split at hstep
  · rename_i hlegal
    have hwLo : 2 ≤ w := hlegal.2.2.2.2.1
    have hwHi : w ≤ FLOORS := hlegal.2.2.2.2.2.1
    have hkeyC : s.custody[keyFor w]? = some CARRIED := hlegal.2.2.2.2.2.2.2
    have hkeyLt : keyFor w < RELICS := by
      have hwHi' : w ≤ 4 := hwHi
      have hw : w = 2 ∨ w = 3 ∨ w = 4 := by omega
      rcases hw with rfl | rfl | rfl <;> decide
    have hilt : keyFor w < s.custody.length := by
      have := hInv.1.1.1; omega
    by_cases heq : s.depth = d
    · cases hstep
      simp only [keyHangsHereTooth, Constraint.toExec, List.map_cons, List.map_nil,
        Simple.toExec, HeapAtom.toExecSimple, HeapKeyRef.field, evalConstraint,
        List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
      right
      unfold evalSimple
      rw [encode_scalar_relic _ (keyFor w) hkeyLt,
        getD_set_self hilt, heq]
      simp
    · cases hstep
      simp only [keyHangsHereTooth, Constraint.toExec, List.map_cons, List.map_nil,
        Simple.toExec, HeapAtom.toExecSimple, HeapKeyRef.field, evalConstraint,
        List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
      left
      simp only [evalSimple]
      rw [encode_scalar_depth]
      have hz : (s.depth : Int) ≠ (d : Int) := by exact_mod_cast heq
      simp only [Bool.not_eq_true']
      simpa using hz
  · exact absurd hstep (by simp)

open Dregg2.Exec in
/-- ⚑ **THE EXHIBIT IS A HOP, NOT A POST-STATE READ.** The rider demands `(CARRIED,
HUNG + d)` for the key relic on a flipping turn: the capability was OWNED going in and IS
hanging coming out. The old post-state form (`relic = CARRIED` after the turn) is FALSE of
every legal unlock in this tree. -/
private theorem wayRider_unlock_honest {s s' : DState} {w : Nat}
    (hInv : ModelProgramInv s) (hstep : step s (.unlock w) = some s') :
    ((wayRider w).toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true := by
  apply case_all_of_constraints
  intro c hc
  change c ∈ coreTeeth ++
    [.allowedTransitions (wayName w) [(0, 1)],
      .heapField (.named (relicName (keyFor w)))
        (.allowedTransitions
          [(CARRIED, HUNG + 1), (CARRIED, HUNG + 2), (CARRIED, HUNG + 3),
           (CARRIED, HUNG + 4)])] ++
    [keyHangsHereTooth (keyFor w) 1, keyHangsHereTooth (keyFor w) 2,
     keyHangsHereTooth (keyFor w) 3, keyHangsHereTooth (keyFor w) 4] at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with (hcore | rfl | rfl) | rfl | rfl | rfl | rfl
  · exact coreTeeth_honest hInv hstep c hcore
  · simp only [step] at hstep
    split at hstep
    · rename_i hlegal
      have hwLo : 2 ≤ w := hlegal.2.2.2.2.1
      have hwHi : w ≤ FLOORS := hlegal.2.2.2.2.2.1
      have hidx : w - 2 < s.ways.length := by
        have hlen := hInv.1.2.2.2.2.1
        omega
      have hold : s.ways.getD (w - 2) 0 = 0 :=
        getD_eq_of_getElem?_eq_some hlegal.2.2.2.2.2.2.1
      have hnew : (s.ways.set (w - 2) 1).getD (w - 2) 0 = 1 :=
        getD_set_self hidx
      cases hstep
      simp only [Constraint.toExec, evalConstraint]
      rw [encode_scalar_way s w hwLo hwHi,
        encode_scalar_way _ w hwLo hwHi, hold, hnew]
      simp
    · exact absurd hstep (by simp)
  · -- The key's hop: `CARRIED → HUNG + depth`, on a real floor.
    have hkeyLt : keyFor w < RELICS := by
      simp only [step] at hstep
      split at hstep
      · rename_i hlegal
        have hwLo : 2 ≤ w := hlegal.2.2.2.2.1
        have hwHi : w ≤ 4 := hlegal.2.2.2.2.2.1
        have hw : w = 2 ∨ w = 3 ∨ w = 4 := by omega
        rcases hw with rfl | rfl | rfl <;> decide
      · exact absurd hstep (by simp)
    refine relic_transition_pin hkeyLt ?_
    have hhop := custody_hop_of_step hInv hstep (keyFor w) hkeyLt
    simp only [step] at hstep
    split at hstep
    · rename_i hlegal
      have hdLo : 1 ≤ s.depth := hlegal.2.2.2.1
      have hdHi : s.depth ≤ FLOORS := hInv.1.2.2.1
      have hkeyC : s.custody[keyFor w]? = some CARRIED := hlegal.2.2.2.2.2.2.2
      have hilt : keyFor w < s.custody.length := by
        have := hInv.1.1.1; omega
      have hold : s.custody.getD (keyFor w) 0 = CARRIED :=
        getD_eq_of_getElem?_eq_some hkeyC
      cases hstep
      have hnew : (s.custody.set (keyFor w) (HUNG + s.depth)).getD (keyFor w) 0
          = HUNG + s.depth := getD_set_self hilt
      show (s.custody.getD (keyFor w) 0,
        (s.custody.set (keyFor w) (HUNG + s.depth)).getD (keyFor w) 0) ∈ _
      rw [hold, hnew]
      have hd : s.depth = 1 ∨ s.depth = 2 ∨ s.depth = 3 ∨ s.depth = 4 := by
        have : s.depth ≤ 4 := hdHi
        omega
      rcases hd with h | h | h | h <;> rw [h] <;> decide
    · exact absurd hstep (by simp)
  · exact unlock_keyHangsHere_honest hInv hstep
  · exact unlock_keyHangsHere_honest hInv hstep
  · exact unlock_keyHangsHere_honest hInv hstep
  · exact unlock_keyHangsHere_honest hInv hstep

open Dregg2.Exec in
/-- Every honest keyed unlock satisfies the unlock arm, exactly the rider selected by its
legal way parameter, and the universal spent rider. -/
theorem modelProgram_unlock_admitted {s s' : DState} {w : Nat}
    (hInv : ModelProgramInv s) (hstep : step s (.unlock w) = some s') :
    RecordProgram.admits dungeonExec (moveIdx (.unlock w))
      (encode s) (encode s') = true := by
  have hUnlock := unlockCase_honest hInv hstep
  have hWay := wayRider_unlock_honest hInv hstep
  have hSpent : (spentRider.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true :=
    case_all_of_constraints (spentRider_honest hInv hstep)
  have hH : (HUNG : Nat) = 12 := rfl
  have hC : (CARRIED : Nat) = 8 := rfl
  have hB : (BANKED : Nat) = 9 := rfl
  simp only [step] at hstep
  split at hstep
  · rename_i hlegal
    have hwLo : 2 ≤ w := hlegal.2.2.2.2.1
    have hwHi : w ≤ FLOORS := hlegal.2.2.2.2.2.1
    have hwHi' : w ≤ 4 := hwHi
    have hkeyC : s.custody[keyFor w]? = some CARRIED := hlegal.2.2.2.2.2.2.2
    -- `bank` does NOT move on an unlock (the write is `CARRIED → HUNG + depth`), so the
    -- bank rider does not fire — the anti-staple discipline working in the quiet
    -- direction.
    have hbankSame : (s.custody.set (keyFor w) (HUNG + s.depth)).countP (· == BANKED)
        = s.custody.countP (· == BANKED) :=
      countP_set_same_local _ hkeyC
        (by
          have h1 : ((CARRIED : Nat) == BANKED) = false :=
            beq_eq_false_iff_ne.mpr (by omega)
          have h2 : ((HUNG + s.depth) == BANKED) = false :=
            beq_eq_false_iff_ne.mpr (by omega)
          rw [h1, h2])
    have hw : w = 2 ∨ w = 3 ∨ w = 4 := by omega
    rcases hw with rfl | rfl | rfl
    all_goals cases hstep
    all_goals
      simp only [dungeonExec, dungeonProgram, CellProgram.toExec]
      apply cases_admit_of
      · refine ⟨unlockCase.toExec, ?_, ?_⟩
        · simp [programCases]
        · simp [Case.toExec, Guard.toExec, methodIdx,
            TransitionGuard.matches, moveIdx]
      · intro tc htc hmatch
        simp only [programCases, List.map_cons, List.map_nil, List.mem_cons,
          List.not_mem_nil, or_false] at htc
        rcases htc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exfalso
          simp [Case.toExec, Guard.toExec, methodIdx, TransitionGuard.matches,
            moveIdx] at hmatch
        · exfalso
          simp [Case.toExec, Guard.toExec, methodIdx, TransitionGuard.matches,
            moveIdx] at hmatch
        · exact hUnlock
        · exfalso
          simp [Case.toExec, Guard.toExec, methodIdx, TransitionGuard.matches,
            moveIdx] at hmatch
        · exfalso
          simp [Case.toExec, Guard.toExec, methodIdx, TransitionGuard.matches,
            moveIdx] at hmatch
        · exfalso
          simp [Case.toExec, Guard.toExec, methodIdx, TransitionGuard.matches,
            moveIdx] at hmatch
        · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
            TransitionGuard.matches, moveIdx] at hmatch
        · -- ascend: a different method entirely
          exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
            TransitionGuard.matches, moveIdx] at hmatch
        · -- take: a different method entirely
          exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
            TransitionGuard.matches, moveIdx] at hmatch
        · exfalso
          simp [Case.toExec, Guard.toExec, methodIdx, TransitionGuard.matches,
            Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch, verbs, moveIdx] at hmatch
        · first
          | (exfalso
             simp [Case.toExec, Guard.toExec, methodIdx, TransitionGuard.matches,
               Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch, verbs, moveIdx,
               hlegal] at hmatch
             done)
          | exact hWay
        · first
          | (exfalso
             simp [Case.toExec, Guard.toExec, methodIdx, TransitionGuard.matches,
               Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch, verbs, moveIdx,
               hlegal] at hmatch
             done)
          | exact hWay
        · first
          | (exfalso
             simp [Case.toExec, Guard.toExec, methodIdx, TransitionGuard.matches,
               Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch, verbs, moveIdx,
               hlegal] at hmatch
             done)
          | exact hWay
        · exfalso
          simp [Case.toExec, Guard.toExec, methodIdx, TransitionGuard.matches,
            Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch, verbs, moveIdx,
            hlegal] at hmatch
        · exfalso
          simp [Case.toExec, Guard.toExec, methodIdx, TransitionGuard.matches,
            Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch, verbs, bank, moveIdx,
            hbankSame, hlegal] at hmatch
        · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
            TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
            verbs, moveIdx] at hmatch
        · exact hSpent
  · exact absurd hstep (by simp)

open Dregg2.Exec in
private theorem smite_guardCap_honest {s s' : DState}
    (hstep : step s .smite = some s') (d : Nat) :
    evalConstraint (guardCapTooth d).toExec (encode s) (encode s') = true := by
  simp only [step] at hstep
  split at hstep
  · rename_i hlegal
    cases hstep
    by_cases heq : s.depth = d
    · simp only [guardCapTooth, Constraint.toExec, List.map_cons, List.map_nil,
        Simple.toExec, evalConstraint, List.any_cons, List.any_nil, Bool.or_false,
        Bool.or_eq_true]
      right
      unfold evalSimple
      rw [encode_scalar_wounds]
      change decide (((s.wounds + 1 : Nat) : Int) ≤ (guardHp d : Int)) = true
      apply decide_eq_true
      exact_mod_cast (heq ▸ hlegal.2.2.2.2)
    · simp only [guardCapTooth, Constraint.toExec, List.map_cons, List.map_nil,
        Simple.toExec, evalConstraint, List.any_cons, List.any_nil, Bool.or_false,
        Bool.or_eq_true]
      left
      simp only [evalSimple]
      rw [encode_scalar_depth]
      have hz : (s.depth : Int) ≠ (d : Int) := by exact_mod_cast heq
      simpa using hz
  · exact absurd hstep (by simp)

open Dregg2.Exec in
private theorem smiteCase_honest {s s' : DState}
    (hInv : ModelProgramInv s) (hstep : step s .smite = some s') :
    (smiteCase.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true := by
  apply case_all_of_constraints
  intro c hc
  change c ∈ coreTeeth ++
    [.fieldDelta "spent" 2, .fieldDelta "wounds" 1,
      .fieldGte "depth" 1, .fieldEquals "fate" 0,
      guardCapTooth 1, guardCapTooth 2, guardCapTooth 3, guardCapTooth 4] ++
    frozen ["depth", "pack", "bank", wayName 2, wayName 3, wayName 4, "harm",
      hoardName 1, hoardName 2, hoardName 3, hoardName 4,
      hungName] ++ relicFreeze at hc
  simp only [List.mem_append] at hc
  rcases hc with ((hcore | hverb) | hfrozen) | hrelic
  · exact coreTeeth_honest hInv hstep c hcore
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hverb
    rcases hverb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [Constraint.toExec, evalConstraint]
      unfold evalSimple
      rw [encode_scalar_spent, encode_scalar_spent, legal_step_spent_eq hstep]
      simp [price]
    · simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · rename_i hlegal
        cases hstep
        simp only [Constraint.toExec, evalConstraint]
        unfold evalSimple
        rw [encode_scalar_depth]
        change decide ((1 : Int) ≤ (s.depth : Int)) = true
        exact decide_eq_true (by exact_mod_cast hlegal.2.2.2.1)
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · rename_i hlegal
        cases hstep
        simp [Constraint.toExec, evalConstraint, evalSimple, hlegal.1]
      · exact absurd hstep (by simp)
    · exact smite_guardCap_honest hstep 1
    · exact smite_guardCap_honest hstep 2
    · exact smite_guardCap_honest hstep 3
    · exact smite_guardCap_honest hstep 4
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hfrozen
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals
      simp only [step] at hstep
      split at hstep
      · cases hstep
        simp [Constraint.toExec, evalConstraint, evalSimple, pack, bank, hoardAt, hungTotal,
              hangFloors_eq, hungAt]
      · exact absurd hstep (by simp)
  · obtain ⟨i, hiRange, rfl⟩ := List.mem_map.mp hrelic
    have hi : i < RELICS := List.mem_range.mp hiRange
    simp only [step] at hstep
    split at hstep
    · cases hstep
      simp only [Constraint.toExec, HeapAtom.toExec, HeapKeyRef.field,
        evalConstraint, evalSimple]
      rw [encode_scalar_relic s i hi, encode_scalar_relic _ i hi]
      simp
    · exact absurd hstep (by simp)

open Dregg2.Exec in
theorem modelProgram_smite_admitted {s s' : DState}
    (hInv : ModelProgramInv s) (hstep : step s .smite = some s') :
    RecordProgram.admits dungeonExec (moveIdx .smite)
      (encode s) (encode s') = true := by
  have hSmite := smiteCase_honest hInv hstep
  have hSpent : (spentRider.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true :=
    case_all_of_constraints (spentRider_honest hInv hstep)
  simp only [step] at hstep
  split at hstep
  · rename_i hlegal
    cases hstep
    simp only [dungeonExec, dungeonProgram, CellProgram.toExec]
    apply cases_admit_of
    · refine ⟨smiteCase.toExec, by simp [programCases], ?_⟩
      simp [Case.toExec, Guard.toExec, methodIdx, TransitionGuard.matches, moveIdx]
    · intro tc htc hmatch
      simp only [programCases, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at htc
      rcases htc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exact hSmite
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · -- ascend: a different method entirely
        exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · -- take: a different method entirely
        exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx, hlegal.1] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, bank, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exact hSpent
  · exact absurd hstep (by simp)

/-! ### The LUNGE — the second blow, and the only verb that may move `harm`.

`lunge` is `smite`'s twin everywhere except the two registers that are the whole design:
it pays `1` breath instead of `2`, and it writes `harm += 1`. So its completeness rung
is the smite rung plus (a) the `harm` delta and range teeth on its own arm and (b) the
`harmRider`, which fires on ANY method that moves the slot and therefore has to be
discharged here rather than assumed. -/

open Dregg2.Exec in
private theorem lunge_guardCap_honest {s s' : DState}
    (hstep : step s .lunge = some s') (d : Nat) :
    evalConstraint (guardCapTooth d).toExec (encode s) (encode s') = true := by
  simp only [step] at hstep
  split at hstep
  · rename_i hlegal
    cases hstep
    by_cases heq : s.depth = d
    · simp only [guardCapTooth, Constraint.toExec, List.map_cons, List.map_nil,
        Simple.toExec, evalConstraint, List.any_cons, List.any_nil, Bool.or_false,
        Bool.or_eq_true]
      right
      unfold evalSimple
      rw [encode_scalar_wounds]
      change decide (((s.wounds + 1 : Nat) : Int) ≤ (guardHp d : Int)) = true
      apply decide_eq_true
      exact_mod_cast (heq ▸ hlegal.2.2.2.2.1)
    · simp only [guardCapTooth, Constraint.toExec, List.map_cons, List.map_nil,
        Simple.toExec, evalConstraint, List.any_cons, List.any_nil, Bool.or_false,
        Bool.or_eq_true]
      left
      simp only [evalSimple]
      rw [encode_scalar_depth]
      have hz : (s.depth : Int) ≠ (d : Int) := by exact_mod_cast heq
      simpa using hz
  · exact absurd hstep (by simp)

open Dregg2.Exec in
/-- The two teeth that ARE the lunge: an exact `+1` on `harm`, inside the ratchet's
`[0, HARMCAP]` range. Both are discharged from the model gate `s.harm + 1 ≤ HARMCAP`. -/
private theorem lunge_harm_eq {s s' : DState} (hstep : step s .lunge = some s') :
    s'.harm = s.harm + 1 ∧ s.harm + 1 ≤ HARMCAP := by
  simp only [step] at hstep
  split at hstep
  · rename_i hlegal
    cases hstep
    exact ⟨rfl, hlegal.2.2.2.2.2.1⟩
  · exact absurd hstep (by simp)

open Dregg2.Exec in
private theorem lunge_harm_honest {s s' : DState}
    (hstep : step s .lunge = some s') :
    evalConstraint (Constraint.fieldDelta "harm" 1).toExec (encode s) (encode s') = true
      ∧ evalConstraint (Constraint.inRangeTwoSided "harm" 0 HARMCAP).toExec
          (encode s) (encode s') = true := by
  obtain ⟨hdelta, hcapH⟩ := lunge_harm_eq hstep
  refine ⟨?_, ?_⟩
  · simp only [Constraint.toExec, evalConstraint]
    unfold evalSimple
    rw [encode_scalar_harm, encode_scalar_harm, hdelta]
    simp
  · apply (evalSimple_inRangeTwoSided_iff "harm" (0 : Int) ((HARMCAP : Nat) : Int)
      (encode s) (encode s')).2
    refine ⟨(s'.harm : Int), encode_scalar_harm s', by exact_mod_cast Nat.zero_le _, ?_⟩
    rw [hdelta]
    exact_mod_cast hcapH

open Dregg2.Exec in
private theorem lungeCase_honest {s s' : DState}
    (hInv : ModelProgramInv s) (hstep : step s .lunge = some s') :
    (lungeCase.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true := by
  apply case_all_of_constraints
  intro c hc
  change c ∈ coreTeeth ++
    [.fieldDelta "spent" 1, .fieldDelta "wounds" 1, .fieldDelta "harm" 1,
      .inRangeTwoSided "harm" 0 HARMCAP,
      .fieldGte "depth" 1, .fieldEquals "fate" 0,
      guardCapTooth 1, guardCapTooth 2, guardCapTooth 3, guardCapTooth 4] ++
    frozen ["depth", "pack", "bank", wayName 2, wayName 3, wayName 4,
      hoardName 1, hoardName 2, hoardName 3, hoardName 4,
      hungName] ++ relicFreeze at hc
  simp only [List.mem_append] at hc
  rcases hc with ((hcore | hverb) | hfrozen) | hrelic
  · exact coreTeeth_honest hInv hstep c hcore
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hverb
    rcases hverb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [Constraint.toExec, evalConstraint]
      unfold evalSimple
      rw [encode_scalar_spent, encode_scalar_spent, legal_step_spent_eq hstep]
      simp [price]
    · simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
      · exact absurd hstep (by simp)
    · exact (lunge_harm_honest hstep).1
    · exact (lunge_harm_honest hstep).2
    · simp only [step] at hstep
      split at hstep
      · rename_i hlegal
        cases hstep
        simp only [Constraint.toExec, evalConstraint]
        unfold evalSimple
        rw [encode_scalar_depth]
        change decide ((1 : Int) ≤ (s.depth : Int)) = true
        exact decide_eq_true (by exact_mod_cast hlegal.2.2.2.1)
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · rename_i hlegal
        cases hstep
        simp [Constraint.toExec, evalConstraint, evalSimple, hlegal.1]
      · exact absurd hstep (by simp)
    · exact lunge_guardCap_honest hstep 1
    · exact lunge_guardCap_honest hstep 2
    · exact lunge_guardCap_honest hstep 3
    · exact lunge_guardCap_honest hstep 4
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hfrozen
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals
      simp only [step] at hstep
      split at hstep
      · cases hstep
        simp [Constraint.toExec, evalConstraint, evalSimple, pack, bank, hoardAt, hungTotal,
              hangFloors_eq, hungAt]
      · exact absurd hstep (by simp)
  · obtain ⟨i, hiRange, rfl⟩ := List.mem_map.mp hrelic
    have hi : i < RELICS := List.mem_range.mp hiRange
    simp only [step] at hstep
    split at hstep
    · cases hstep
      simp only [Constraint.toExec, HeapAtom.toExec, HeapKeyRef.field,
        evalConstraint, evalSimple]
      rw [encode_scalar_relic s i hi, encode_scalar_relic _ i hi]
      simp
    · exact absurd hstep (by simp)

open Dregg2.Exec in
/-- ⚑ THE ANTI-STAPLE RIDER, DISCHARGED. `harmRider` fires on any method that moves the
`harm` slot; the honest lunge satisfies its whole law, so the rider costs the legal verb
nothing while making the slot unstapleable onto every other one. -/
private theorem harmRider_lunge_honest {s s' : DState}
    (hInv : ModelProgramInv s) (hstep : step s .lunge = some s') :
    (harmRider.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true := by
  apply case_all_of_constraints
  intro c hc
  change c ∈ coreTeeth ++
    [.fieldDelta "harm" 1, .inRangeTwoSided "harm" 0 HARMCAP,
      .fieldDelta "wounds" 1, .fieldGte "depth" 1, .fieldEquals "fate" 0] at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with hcore | rfl | rfl | rfl | rfl | rfl
  · exact coreTeeth_honest hInv hstep c hcore
  · exact (lunge_harm_honest hstep).1
  · exact (lunge_harm_honest hstep).2
  · simp only [step] at hstep
    split at hstep
    · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
    · exact absurd hstep (by simp)
  · simp only [step] at hstep
    split at hstep
    · rename_i hlegal
      cases hstep
      simp only [Constraint.toExec, evalConstraint]
      unfold evalSimple
      rw [encode_scalar_depth]
      change decide ((1 : Int) ≤ (s.depth : Int)) = true
      exact decide_eq_true (by exact_mod_cast hlegal.2.2.2.1)
    · exact absurd hstep (by simp)
  · simp only [step] at hstep
    split at hstep
    · rename_i hlegal
      cases hstep
      simp [Constraint.toExec, evalConstraint, evalSimple, hlegal.1]
    · exact absurd hstep (by simp)

open Dregg2.Exec in
/-- **Every honest lunge is admitted** — its own arm, the `harmRider` its write summons,
and the universal spent rider. -/
theorem modelProgram_lunge_admitted {s s' : DState}
    (hInv : ModelProgramInv s) (hstep : step s .lunge = some s') :
    RecordProgram.admits dungeonExec (moveIdx .lunge)
      (encode s) (encode s') = true := by
  have hLunge := lungeCase_honest hInv hstep
  have hHarm := harmRider_lunge_honest hInv hstep
  have hSpent : (spentRider.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true :=
    case_all_of_constraints (spentRider_honest hInv hstep)
  simp only [step] at hstep
  split at hstep
  · rename_i hlegal
    cases hstep
    simp only [dungeonExec, dungeonProgram, CellProgram.toExec]
    apply cases_admit_of
    · refine ⟨lungeCase.toExec, by simp [programCases], ?_⟩
      simp [Case.toExec, Guard.toExec, methodIdx, TransitionGuard.matches, moveIdx]
    · intro tc htc hmatch
      simp only [programCases, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at htc
      rcases htc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exact hLunge
      · -- ascend: a different method entirely
        exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · -- take: a different method entirely
        exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx, hlegal.1] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, bank, moveIdx] at hmatch
      · exact hHarm
      · exact hSpent
  · exact absurd hstep (by simp)

open Dregg2.Exec in
private theorem loot_guardSlain_honest {s s' : DState} {r : Nat}
    (hstep : step s (.loot r) = some s') (d : Nat) :
    evalConstraint (guardSlainTooth d).toExec (encode s) (encode s') = true := by
  simp only [step] at hstep
  split at hstep
  · rename_i hlegal
    cases hstep
    by_cases heq : s.depth = d
    · simp only [guardSlainTooth, Constraint.toExec, List.map_cons,
        List.map_nil, Simple.toExec, evalConstraint, List.any_cons, List.any_nil,
        Bool.or_false, Bool.or_eq_true]
      right
      unfold evalSimple
      rw [encode_scalar_wounds]
      change decide ((guardHp d : Int) ≤ (s.wounds : Int)) = true
      apply decide_eq_true
      exact_mod_cast (heq ▸ hlegal.2.2.2.2.2.1).ge
    · simp only [guardSlainTooth, Constraint.toExec, List.map_cons,
        List.map_nil, Simple.toExec, evalConstraint, List.any_cons, List.any_nil,
        Bool.or_false, Bool.or_eq_true]
      left
      simp only [evalSimple]
      rw [encode_scalar_depth]
      have hz : (s.depth : Int) ≠ (d : Int) := by exact_mod_cast heq
      simpa using hz
  · exact absurd hstep (by simp)

open Dregg2.Exec in
private theorem loot_hoardFrame_honest {s s' : DState} {r d : Nat}
    (hInv : ModelProgramInv s) (hstep : step s (.loot r) = some s')
    (hdLo : 1 ≤ d) (hdHi : d ≤ FLOORS) :
    evalConstraint (hoardFrameTooth d).toExec (encode s) (encode s') = true := by
  simp only [step] at hstep
  split at hstep
  · rename_i hlegal
    by_cases heq : s.depth = d
    · cases hstep
      simp only [hoardFrameTooth, Constraint.toExec, List.map_cons,
        List.map_nil, Simple.toExec, evalConstraint, List.any_cons, List.any_nil,
        Bool.or_false, Bool.or_eq_true]
      left
      unfold evalSimple
      rw [encode_scalar_depth]
      have hz : (s.depth : Int) = (d : Int) := by exact_mod_cast heq
      simpa using hz
    · have hdepthLt : s.depth ≤ FLOORS := hInv.1.2.2.1
      have holdFalse : (s.depth == d) = false := beq_eq_false_iff_ne.mpr heq
      have hcarriedFalse : (CARRIED == d) = false := by
        apply beq_eq_false_iff_ne.mpr
        have hFloorCarried : FLOORS < CARRIED := by decide
        omega
      have hsame : (s.custody.set r CARRIED).countP (· == d) =
          s.custody.countP (· == d) :=
        countP_set_same_local _ hlegal.2.2.2.2.1 (by rw [holdFalse, hcarriedFalse])
      cases hstep
      simp only [hoardFrameTooth, Constraint.toExec, List.map_cons,
        List.map_nil, Simple.toExec, evalConstraint, List.any_cons, List.any_nil,
        Bool.or_false, Bool.or_eq_true]
      right
      unfold evalSimple
      rw [encode_scalar_hoard s d hdLo hdHi,
        encode_scalar_hoard _ d hdLo hdHi]
      simpa [hoardAt] using hsame
  · exact absurd hstep (by simp)

open Dregg2.Exec in
/-- ⚑ **A `loot` NEVER TOUCHES A DOOR.** It writes `CARRIED` over a FLOOR code, and
neither code is in the `HUNG` family, so every door census is frozen across the turn —
the register-side twin of "a relic found lying in a hoard was already lying there". -/
private theorem loot_hungTotal_same {s s' : DState} {r : Nat}
    (hInv : ModelProgramInv s) (hstep : step s (.loot r) = some s') :
    hungTotal s' = hungTotal s := by
  have hdepthLt : s.depth ≤ FLOORS := hInv.1.2.2.1
  have hH : (HUNG : Nat) = 12 := rfl
  have hF : (FLOORS : Nat) = 4 := rfl
  have hC : (CARRIED : Nat) = 8 := rfl
  simp only [step] at hstep
  split at hstep
  · rename_i hlegal
    have hcust : s'.custody = s.custody.set r CARRIED := by rw [← Option.some.inj hstep]
    have hAt : ∀ e : Nat, hungAt s' e = hungAt s e := by
      intro e
      simp only [hungAt, hcust]
      exact countP_set_same_local _ hlegal.2.2.2.2.1
        (by
          have h1 : (s.depth == HUNG + e) = false := beq_eq_false_iff_ne.mpr (by omega)
          have h2 : ((CARRIED : Nat) == HUNG + e) = false :=
            beq_eq_false_iff_ne.mpr (by omega)
          rw [h1, h2])
    have := hungTotal_eq_of (s := s) (s' := s') (j := 0) (k := 0)
      (by rw [hAt 1, hAt 2, hAt 3, hAt 4])
    omega
  · exact absurd hstep (by simp)

open Dregg2.Exec in
/-- The `loot` arm's door freeze, deployed: ONE register, frozen. -/
private theorem loot_hung_immutable_honest {s s' : DState} {r : Nat}
    (hInv : ModelProgramInv s) (hstep : step s (.loot r) = some s') :
    evalConstraint (Constraint.immutable hungName).toExec
      (encode s) (encode s') = true := by
  have hsame := loot_hungTotal_same hInv hstep
  simp only [Constraint.toExec, evalConstraint]
  unfold evalSimple
  rw [encode_scalar_hung s, encode_scalar_hung s', hsame]
  simp

open Dregg2.Exec in
private theorem lootCase_honest {s s' : DState} {r : Nat}
    (hInv : ModelProgramInv s) (hstep : step s (.loot r) = some s') :
    (lootCase.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true := by
  apply case_all_of_constraints
  intro c hc
  change c ∈ coreTeeth ++
    [.fieldDelta "spent" 1, .fieldDelta "pack" 1,
      .fieldGte "depth" 1, .fieldEquals "fate" 0,
      guardSlainTooth 1, guardSlainTooth 2, guardSlainTooth 3, guardSlainTooth 4,
      hoardFrameTooth 1, hoardFrameTooth 2, hoardFrameTooth 3,
      hoardFrameTooth 4] ++
    frozen ["depth", "wounds", "bank", wayName 2, wayName 3, wayName 4, "harm",
      hungName] at hc
  simp only [List.mem_append] at hc
  rcases hc with (hcore | hverb) | hfrozen
  · exact coreTeeth_honest hInv hstep c hcore
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hverb
    rcases hverb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · simp only [Constraint.toExec, evalConstraint]
      unfold evalSimple
      rw [encode_scalar_spent, encode_scalar_spent, legal_step_spent_eq hstep]
      simp [price]
    · simp only [step] at hstep
      split at hstep
      · rename_i hlegal
        have hdepthLt : s.depth ≤ FLOORS := hInv.1.2.2.1
        have hdepthCarried : (s.depth == CARRIED) = false := by
          apply beq_eq_false_iff_ne.mpr
          have hFloorCarried : FLOORS < CARRIED := by decide
          omega
        have hpack : pack (DState.mk s.depth (s.spent + 1) s.wounds s.harm s.fate
              s.ways (s.custody.set r CARRIED)) = pack s + 1 := by
          simp only [pack]
          exact countP_set_bump_local _ hlegal.2.2.2.2.1 hdepthCarried (by simp)
        cases hstep
        simp only [Constraint.toExec, evalConstraint]
        unfold evalSimple
        rw [encode_scalar_pack, encode_scalar_pack, hpack]
        simp
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · rename_i hlegal
        cases hstep
        simp only [Constraint.toExec, evalConstraint]
        unfold evalSimple
        rw [encode_scalar_depth]
        change decide ((1 : Int) ≤ (s.depth : Int)) = true
        exact decide_eq_true (by exact_mod_cast hlegal.2.2.2.1)
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · rename_i hlegal
        cases hstep
        simp [Constraint.toExec, evalConstraint, evalSimple, hlegal.1]
      · exact absurd hstep (by simp)
    · exact loot_guardSlain_honest hstep 1
    · exact loot_guardSlain_honest hstep 2
    · exact loot_guardSlain_honest hstep 3
    · exact loot_guardSlain_honest hstep 4
    · exact loot_hoardFrame_honest hInv hstep (by decide) (by decide)
    · exact loot_hoardFrame_honest hInv hstep (by decide) (by decide)
    · exact loot_hoardFrame_honest hInv hstep (by decide) (by decide)
    · exact loot_hoardFrame_honest hInv hstep (by decide) (by decide)
  · obtain ⟨reg, hreg, rfl⟩ := List.mem_map.mp hfrozen
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hreg
    rcases hreg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · rename_i hlegal
        have hdepthLt : s.depth ≤ FLOORS := hInv.1.2.2.1
        have hdepthBanked : (s.depth == BANKED) = false := by
          apply beq_eq_false_iff_ne.mpr
          have hFloorBanked : FLOORS < BANKED := by decide
          omega
        have hcarriedBanked : (CARRIED == BANKED) = false := by decide
        have hbank : bank (DState.mk s.depth (s.spent + 1) s.wounds s.harm s.fate
              s.ways (s.custody.set r CARRIED)) = bank s := by
          simp only [bank]
          exact countP_set_same_local _ hlegal.2.2.2.2.1
            (by rw [hdepthBanked, hcarriedBanked])
        cases hstep
        simp [Constraint.toExec, evalConstraint, evalSimple, hbank]
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
      · exact absurd hstep (by simp)
    · exact loot_hung_immutable_honest hInv hstep

open Dregg2.Exec in
theorem modelProgram_loot_admitted {s s' : DState} {r : Nat}
    (hInv : ModelProgramInv s) (hstep : step s (.loot r) = some s') :
    RecordProgram.admits dungeonExec (moveIdx (.loot r))
      (encode s) (encode s') = true := by
  have hLoot := lootCase_honest hInv hstep
  have hSpent : (spentRider.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true :=
    case_all_of_constraints (spentRider_honest hInv hstep)
  simp only [step] at hstep
  split at hstep
  · rename_i hlegal
    have hdepthLt : s.depth ≤ FLOORS := hInv.1.2.2.1
    have hdepthBanked : (s.depth == BANKED) = false := by
      apply beq_eq_false_iff_ne.mpr
      have hFloorBanked : FLOORS < BANKED := by decide
      omega
    have hcarriedBanked : (CARRIED == BANKED) = false := by decide
    have hbankSame : (s.custody.set r CARRIED).countP (· == BANKED) =
        s.custody.countP (· == BANKED) :=
      countP_set_same_local _ hlegal.2.2.2.2.1
        (by rw [hdepthBanked, hcarriedBanked])
    cases hstep
    simp only [dungeonExec, dungeonProgram, CellProgram.toExec]
    apply cases_admit_of
    · refine ⟨lootCase.toExec, by simp [programCases], ?_⟩
      simp [Case.toExec, Guard.toExec, methodIdx, TransitionGuard.matches, moveIdx]
    · intro tc htc hmatch
      simp only [programCases, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at htc
      rcases htc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exact hLoot
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · -- ascend: a different method entirely
        exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · -- take: a different method entirely
        exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx, hlegal.1] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, bank, moveIdx, hbankSame] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exact hSpent
  · exact absurd hstep (by simp)

/-! ### ⚑ THE NEW VERB — `take`, the one step in the rulebook that LOWERS a custody code.

`take` is `loot` minus the guardian tooth, one zone over: the relic is not lying in a
hoard under a standing guardian, it is hanging in a door already opened. So its
completeness rung is the loot rung with the hoard frame replaced by the DOOR frame, and
the hop it must exhibit is `HUNG + depth → CARRIED` rather than `home → CARRIED`. The
carry slot is charged all the same, at the identical posted price, and the capacity
commons in `coreTeeth` price it against depth and harm exactly as they price a loot. -/

open Dregg2.Exec in
/-- Lifting a key out of its door costs the carry slot back: `pack` rises by exactly one. -/
private theorem take_pack_bump {s s' : DState} {r : Nat}
    (hInv : ModelProgramInv s) (hstep : step s (.take r) = some s') :
    pack s' = pack s + 1 := by
  have hH : (HUNG : Nat) = 12 := rfl
  have hC : (CARRIED : Nat) = 8 := rfl
  simp only [step] at hstep
  split at hstep
  · rename_i hlegal
    have hhangs : s.custody[r]? = some (HUNG + s.depth) := hlegal.2.2.2.2.1
    have hbump := countP_set_bump_local (l := s.custody) (i := r)
      (a := HUNG + s.depth) (v := CARRIED) (· == CARRIED) hhangs
      (beq_eq_false_iff_ne.mpr (by omega)) (by simp)
    cases hstep
    simpa only [pack] using hbump
  · exact absurd hstep (by simp)

open Dregg2.Exec in
/-- ⚑ **THE DOOR CENSUS LOSES EXACTLY ONE.** `take` lifts the key out of the door on the
floor it is standing on, so the residue drops by one at `s.depth` and is frozen on every
other floor. WHICH door it came out of is `doorDepartureTooth`, on the object — and THAT is
the tooth that refuses the remote take, method-independently, because it rides the `spent`
rider rather than this arm. -/
private theorem take_hungTotal_drop {s s' : DState} {r : Nat}
    (hInv : ModelProgramInv s) (hstep : step s (.take r) = some s') :
    hungTotal s' + 1 = hungTotal s := by
  have hH : (HUNG : Nat) = 12 := rfl
  have hC : (CARRIED : Nat) = 8 := rfl
  have hdHi : s.depth ≤ FLOORS := hInv.1.2.2.1
  have hF : (FLOORS : Nat) = 4 := rfl
  simp only [step] at hstep
  split at hstep
  · rename_i hlegal
    have hdLo : 1 ≤ s.depth := hlegal.2.2.2.1
    have hhangs : s.custody[r]? = some (HUNG + s.depth) := hlegal.2.2.2.2.1
    have hcust : s'.custody = s.custody.set r CARRIED := by rw [← Option.some.inj hstep]
    have hAt : ∀ e : Nat, hungAt s e = hungAt s' e + (if e = s.depth then 1 else 0) := by
      intro e
      simp only [hungAt, hcust]
      by_cases he : e = s.depth
      · rw [if_pos he, he]
        exact (countP_set_drop_local (· == HUNG + s.depth) hhangs (by simp)
          (beq_eq_false_iff_ne.mpr (by omega))).symm
      · rw [if_neg he, Nat.add_zero]
        exact (countP_set_same_local (· == HUNG + e) hhangs (by
          have h1 : ((HUNG + s.depth) == HUNG + e) = false :=
            beq_eq_false_iff_ne.mpr (by omega)
          have h2 : ((CARRIED : Nat) == HUNG + e) = false :=
            beq_eq_false_iff_ne.mpr (by omega)
          rw [h1, h2])).symm
    have hd : s.depth = 1 ∨ s.depth = 2 ∨ s.depth = 3 ∨ s.depth = 4 := by omega
    have := hungTotal_eq_of (s := s) (s' := s') (j := 1) (k := 0)
      (by rw [hAt 1, hAt 2, hAt 3, hAt 4]
          rcases hd with h | h | h | h <;> rw [h] <;> simp <;> omega)
    omega
  · exact absurd hstep (by simp)

open Dregg2.Exec in
/-- ⚑ **THE DOOR RESIDUE'S `take` RUNG.** `(k, k−1)`; the residue is at least one because a
key was hanging, and at most `RELICS` because it is part of the partition. -/
private theorem take_hung_transition_honest {s s' : DState} {r : Nat}
    (hInv : ModelProgramInv s) (hstep : step s (.take r) = some s') :
    evalConstraint (Constraint.allowedTransitions hungName
        ((List.range' 1 RELICS).map (fun k => (k, k - 1)))).toExec
      (encode s) (encode s') = true := by
  have hdrop := take_hungTotal_drop hInv hstep
  have hle : hungTotal s ≤ RELICS := hungTotal_le_relics hInv.1
  have hrelics : (RELICS : Nat) = 8 := rfl
  refine hung_transition_pin ?_
  have hlist : (List.range' 1 RELICS) = [1, 2, 3, 4, 5, 6, 7, 8] := by decide
  rw [hlist]
  have hcases : hungTotal s = 1 ∨ hungTotal s = 2 ∨ hungTotal s = 3 ∨ hungTotal s = 4
      ∨ hungTotal s = 5 ∨ hungTotal s = 6 ∨ hungTotal s = 7 ∨ hungTotal s = 8 := by omega
  have hs' : hungTotal s' = hungTotal s - 1 := by omega
  rcases hcases with h|h|h|h|h|h|h|h <;> rw [hs', h] <;> simp

open Dregg2.Exec in
/-- A `take` never touches a hoard: it writes `CARRIED` over a `HUNG` code, and neither is
a floor code. -/
private theorem take_hoard_immutable_honest {s s' : DState} {r : Nat}
    (hInv : ModelProgramInv s) (hstep : step s (.take r) = some s') (d : Nat)
    (hdLo : 1 ≤ d) (hdHi : d ≤ FLOORS) :
    evalConstraint (Constraint.immutable (hoardName d)).toExec
      (encode s) (encode s') = true := by
  have hH : (HUNG : Nat) = 12 := rfl
  have hC : (CARRIED : Nat) = 8 := rfl
  have hF : (FLOORS : Nat) = 4 := rfl
  simp only [step] at hstep
  split at hstep
  · rename_i hlegal
    have hhangs : s.custody[r]? = some (HUNG + s.depth) := hlegal.2.2.2.2.1
    have hsame : (s.custody.set r CARRIED).countP (· == d) =
        s.custody.countP (· == d) :=
      countP_set_same_local _ hhangs
        (by
          have h1 : ((HUNG + s.depth) == d) = false :=
            beq_eq_false_iff_ne.mpr (by omega)
          have h2 : ((CARRIED : Nat) == d) = false :=
            beq_eq_false_iff_ne.mpr (by omega)
          rw [h1, h2])
    cases hstep
    simp only [Constraint.toExec, evalConstraint]
    unfold evalSimple
    rw [encode_scalar_hoard s d hdLo hdHi, encode_scalar_hoard _ d hdLo hdHi]
    simpa [hoardAt] using hsame
  · exact absurd hstep (by simp)

open Dregg2.Exec in
private theorem take_bank_same {s s' : DState} {r : Nat}
    (hInv : ModelProgramInv s) (hstep : step s (.take r) = some s') :
    bank s' = bank s := by
  have hH : (HUNG : Nat) = 12 := rfl
  have hC : (CARRIED : Nat) = 8 := rfl
  have hB : (BANKED : Nat) = 9 := rfl
  simp only [step] at hstep
  split at hstep
  · rename_i hlegal
    have hhangs : s.custody[r]? = some (HUNG + s.depth) := hlegal.2.2.2.2.1
    have hsame : (s.custody.set r CARRIED).countP (· == BANKED) =
        s.custody.countP (· == BANKED) :=
      countP_set_same_local _ hhangs
        (by
          have h1 : ((HUNG + s.depth) == BANKED) = false :=
            beq_eq_false_iff_ne.mpr (by omega)
          have h2 : ((CARRIED : Nat) == BANKED) = false :=
            beq_eq_false_iff_ne.mpr (by omega)
          rw [h1, h2])
    cases hstep
    simpa only [bank] using hsame
  · exact absurd hstep (by simp)

open Dregg2.Exec in
private theorem takeCase_honest {s s' : DState} {r : Nat}
    (hInv : ModelProgramInv s) (hstep : step s (.take r) = some s') :
    (takeCase.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true := by
  apply case_all_of_constraints
  intro c hc
  change c ∈ coreTeeth ++
    [.fieldDelta "spent" 1, .fieldDelta "pack" 1,
      .fieldGte "depth" 1, .fieldEquals "fate" 0,
      .allowedTransitions hungName ((List.range' 1 RELICS).map (fun k => (k, k - 1)))] ++
    frozen ["depth", "wounds", "bank", wayName 2, wayName 3, wayName 4, "harm",
      hoardName 1, hoardName 2, hoardName 3, hoardName 4] at hc
  simp only [List.mem_append] at hc
  rcases hc with (hcore | hverb) | hfrozen
  · exact coreTeeth_honest hInv hstep c hcore
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hverb
    rcases hverb with rfl | rfl | rfl | rfl | rfl
    · simp only [Constraint.toExec, evalConstraint]
      unfold evalSimple
      rw [encode_scalar_spent, encode_scalar_spent, legal_step_spent_eq hstep]
      simp [price]
    · have hbump := take_pack_bump hInv hstep
      simp only [Constraint.toExec, evalConstraint]
      unfold evalSimple
      rw [encode_scalar_pack, encode_scalar_pack, hbump]
      simp
    · simp only [step] at hstep
      split at hstep
      · rename_i hlegal
        cases hstep
        simp only [Constraint.toExec, evalConstraint]
        unfold evalSimple
        rw [encode_scalar_depth]
        change decide ((1 : Int) ≤ (s.depth : Int)) = true
        exact decide_eq_true (by exact_mod_cast hlegal.2.2.2.1)
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · rename_i hlegal
        cases hstep
        simp [Constraint.toExec, evalConstraint, evalSimple, hlegal.1]
      · exact absurd hstep (by simp)
    · exact take_hung_transition_honest hInv hstep
  · obtain ⟨reg, hreg, rfl⟩ := List.mem_map.mp hfrozen
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hreg
    rcases hreg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
      · exact absurd hstep (by simp)
    · have hbank := take_bank_same hInv hstep
      simp only [Constraint.toExec, evalConstraint]
      unfold evalSimple
      rw [encode_scalar_bank, encode_scalar_bank, hbank]
      simp
    · simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
      · exact absurd hstep (by simp)
    · exact take_hoard_immutable_honest hInv hstep 1 (by decide) (by decide)
    · exact take_hoard_immutable_honest hInv hstep 2 (by decide) (by decide)
    · exact take_hoard_immutable_honest hInv hstep 3 (by decide) (by decide)
    · exact take_hoard_immutable_honest hInv hstep 4 (by decide) (by decide)

open Dregg2.Exec in
/-- **Every honest `take` is admitted** — its own arm plus the universal spent rider. The
depth, way, fate, bank and harm riders all FAIL to match: lifting a key moves none of
those slots, which is the anti-staple discipline working in the quiet direction. -/
theorem modelProgram_take_admitted {s s' : DState} {r : Nat}
    (hInv : ModelProgramInv s) (hstep : step s (.take r) = some s') :
    RecordProgram.admits dungeonExec (moveIdx (.take r))
      (encode s) (encode s') = true := by
  have hTake := takeCase_honest hInv hstep
  have hSpent : (spentRider.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true :=
    case_all_of_constraints (spentRider_honest hInv hstep)
  have hbankSame := take_bank_same hInv hstep
  simp only [bank] at hbankSame
  simp only [step] at hstep
  split at hstep
  · rename_i hlegal
    cases hstep
    simp only [dungeonExec, dungeonProgram, CellProgram.toExec]
    apply cases_admit_of
    · refine ⟨takeCase.toExec, by simp [programCases], ?_⟩
      simp [Case.toExec, Guard.toExec, methodIdx, TransitionGuard.matches, moveIdx]
    · intro tc htc hmatch
      simp only [programCases, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at htc
      rcases htc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exact hTake
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx, hlegal.1] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, bank, moveIdx, hbankSame] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exact hSpent
  · exact absurd hstep (by simp)

open Dregg2.Exec in
private theorem flee_hoard_immutable_honest {s s' : DState}
    (hstep : step s .flee = some s') (d : Nat)
    (hdLo : 1 ≤ d) (hdHi : d ≤ FLOORS) :
    evalConstraint (Constraint.immutable (hoardName d)).toExec
      (encode s) (encode s') = true := by
  simp only [step] at hstep
  split at hstep
  · have hdC : d ≠ CARRIED := by
      have hFC : FLOORS < CARRIED := by decide
      omega
    have hdB : d ≠ BANKED := by
      have hFB : FLOORS < BANKED := by decide
      omega
    have hsame := countP_flee_floor_local s.custody d hdC hdB
    cases hstep
    simp only [Constraint.toExec, evalConstraint]
    unfold evalSimple
    rw [encode_scalar_hoard s d hdLo hdHi,
      encode_scalar_hoard _ d hdLo hdHi]
    rw [show hoardAt
        { depth := s.depth, spent := s.spent + 1, wounds := s.wounds, harm := s.harm,
          fate := 1, ways := s.ways,
          custody := s.custody.map
            (fun c => if c = CARRIED then BANKED else c) } d = hoardAt s d by
      simpa [hoardAt, Function.comp_def] using hsame]
    simp
  · exact absurd hstep (by simp)

open Dregg2.Exec in
/-- ⚑ **A HUNG KEY IS NOT YOURS.** `flee` promotes `CARRIED` and only `CARRIED`, so the
door censuses ride through the bank untouched — a key left in its door banks nothing, and
conservation cannot launder it into the bank on the way past. -/
private theorem flee_hungTotal_same {s s' : DState}
    (hstep : step s .flee = some s') : hungTotal s' = hungTotal s := by
  have hH : (HUNG : Nat) = 12 := rfl
  have hF : (FLOORS : Nat) = 4 := rfl
  have hC : (CARRIED : Nat) = 8 := rfl
  have hB : (BANKED : Nat) = 9 := rfl
  simp only [step] at hstep
  split at hstep
  · have hcust : s'.custody
        = s.custody.map (fun c => if c = CARRIED then BANKED else c) := by
      rw [← Option.some.inj hstep]
    have hAt : ∀ e : Nat, hungAt s' e = hungAt s e := by
      intro e
      simp only [hungAt, hcust]
      exact countP_flee_pred_local s.custody (· == HUNG + e)
        (beq_eq_false_iff_ne.mpr (by omega)) (beq_eq_false_iff_ne.mpr (by omega))
    have := hungTotal_eq_of (s := s) (s' := s') (j := 0) (k := 0)
      (by rw [hAt 1, hAt 2, hAt 3, hAt 4])
    omega
  · exact absurd hstep (by simp)

open Dregg2.Exec in
/-- The `flee` arm's door freeze, deployed: ONE register, frozen. -/
private theorem flee_hung_immutable_honest {s s' : DState}
    (hstep : step s .flee = some s') :
    evalConstraint (Constraint.immutable hungName).toExec
      (encode s) (encode s') = true := by
  have hsame := flee_hungTotal_same hstep
  simp only [Constraint.toExec, evalConstraint]
  unfold evalSimple
  rw [encode_scalar_hung s, encode_scalar_hung s', hsame]
  simp

open Dregg2.Exec in
private theorem fleeCase_honest {s s' : DState}
    (hInv : ModelProgramInv s) (hstep : step s .flee = some s') :
    (fleeCase.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true := by
  apply case_all_of_constraints
  intro c hc
  change c ∈ coreTeeth ++
    [.fieldDelta "spent" 1, .fieldEquals "fate" 1, .fieldEquals "pack" 0,
      .fieldEquals "depth" 0] ++
    frozen ["depth", "wounds", wayName 2, wayName 3, wayName 4, "harm",
      hoardName 1, hoardName 2, hoardName 3, hoardName 4,
      hungName] at hc
  simp only [List.mem_append] at hc
  rcases hc with (hcore | hverb) | hfrozen
  · exact coreTeeth_honest hInv hstep c hcore
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hverb
    rcases hverb with rfl | rfl | rfl | rfl
    · simp only [Constraint.toExec, evalConstraint]
      unfold evalSimple
      rw [encode_scalar_spent, encode_scalar_spent, legal_step_spent_eq hstep]
      simp [price]
    · simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · have hpack : pack
            { depth := s.depth, spent := s.spent + 1, wounds := s.wounds, harm := s.harm,
              fate := 1, ways := s.ways,
              custody := s.custody.map
                (fun c => if c = CARRIED then BANKED else c) } = 0 := by
          simpa [pack] using countP_flee_carried_local s.custody
        cases hstep
        simp [Constraint.toExec, evalConstraint, evalSimple, hpack]
      · exact absurd hstep (by simp)
    · -- ⚑ THE SURFACE GATE: banking happens at the mouth (`flee` demands `depth = 0`).
      simp only [step] at hstep
      split at hstep
      · rename_i hlegal
        cases hstep
        simp [Constraint.toExec, evalConstraint, evalSimple, hlegal.2.2.2]
      · exact absurd hstep (by simp)
  · obtain ⟨reg, hreg, rfl⟩ := List.mem_map.mp hfrozen
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hreg
    rcases hreg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
      · exact absurd hstep (by simp)
    · exact flee_hoard_immutable_honest hstep 1 (by decide) (by decide)
    · exact flee_hoard_immutable_honest hstep 2 (by decide) (by decide)
    · exact flee_hoard_immutable_honest hstep 3 (by decide) (by decide)
    · exact flee_hoard_immutable_honest hstep 4 (by decide) (by decide)
    · exact flee_hung_immutable_honest hstep

open Dregg2.Exec in
private theorem fateRider_flee_honest {s s' : DState}
    (hInv : ModelProgramInv s) (hstep : step s .flee = some s') :
    (fateRider.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true := by
  apply case_all_of_constraints
  intro c hc
  change c ∈ coreTeeth ++
    [.allowedTransitions "fate" [(0, 1)], .fieldEquals "pack" 0,
      .fieldEquals "depth" 0] at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with hcore | rfl | rfl | rfl
  · exact coreTeeth_honest hInv hstep c hcore
  · simp only [step] at hstep
    split at hstep
    · rename_i hlegal
      cases hstep
      simp [Constraint.toExec, evalConstraint, hlegal.1]
    · exact absurd hstep (by simp)
  · simp only [step] at hstep
    split at hstep
    · have hpack : pack
          { depth := s.depth, spent := s.spent + 1, wounds := s.wounds, harm := s.harm,
            fate := 1, ways := s.ways,
            custody := s.custody.map
              (fun c => if c = CARRIED then BANKED else c) } = 0 := by
        simpa [pack] using countP_flee_carried_local s.custody
      cases hstep
      simp [Constraint.toExec, evalConstraint, evalSimple, hpack]
    · exact absurd hstep (by simp)

  · -- ⚑ THE SURFACE GATE: banking happens at the mouth (`flee` demands `depth = 0`).
    simp only [step] at hstep
    split at hstep
    · rename_i hlegal
      cases hstep
      simp [Constraint.toExec, evalConstraint, evalSimple, hlegal.2.2.2]
    · exact absurd hstep (by simp)
open Dregg2.Exec in
private theorem bankRider_flee_honest {s s' : DState}
    (hInv : ModelProgramInv s) (hstep : step s .flee = some s') :
    (bankRider.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true := by
  apply case_all_of_constraints
  intro c hc
  change c ∈ coreTeeth ++ [.fieldEquals "fate" 1, .fieldEquals "pack" 0,
      .fieldEquals "depth" 0] at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with hcore | rfl | rfl | rfl
  · exact coreTeeth_honest hInv hstep c hcore
  · simp only [step] at hstep
    split at hstep
    · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
    · exact absurd hstep (by simp)
  · simp only [step] at hstep
    split at hstep
    · have hpack : pack
          { depth := s.depth, spent := s.spent + 1, wounds := s.wounds, harm := s.harm,
            fate := 1, ways := s.ways,
            custody := s.custody.map
              (fun c => if c = CARRIED then BANKED else c) } = 0 := by
        simpa [pack] using countP_flee_carried_local s.custody
      cases hstep
      simp [Constraint.toExec, evalConstraint, evalSimple, hpack]
    · exact absurd hstep (by simp)

  · -- ⚑ THE SURFACE GATE: banking happens at the mouth (`flee` demands `depth = 0`).
    simp only [step] at hstep
    split at hstep
    · rename_i hlegal
      cases hstep
      simp [Constraint.toExec, evalConstraint, evalSimple, hlegal.2.2.2]
    · exact absurd hstep (by simp)
open Dregg2.Exec in
theorem modelProgram_flee_admitted {s s' : DState}
    (hInv : ModelProgramInv s) (hstep : step s .flee = some s') :
    RecordProgram.admits dungeonExec (moveIdx .flee)
      (encode s) (encode s') = true := by
  have hFlee := fleeCase_honest hInv hstep
  have hFate := fateRider_flee_honest hInv hstep
  have hBank := bankRider_flee_honest hInv hstep
  have hSpent : (spentRider.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true :=
    case_all_of_constraints (spentRider_honest hInv hstep)
  simp only [step] at hstep
  split at hstep
  · cases hstep
    simp only [dungeonExec, dungeonProgram, CellProgram.toExec]
    apply cases_admit_of
    · refine ⟨fleeCase.toExec, by simp [programCases], ?_⟩
      simp [Case.toExec, Guard.toExec, methodIdx, TransitionGuard.matches, moveIdx]
    · intro tc htc hmatch
      simp only [programCases, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at htc
      rcases htc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exact hFlee
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · -- ascend: a different method entirely
        exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · -- take: a different method entirely
        exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exact hFate
      · exact hBank
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exact hSpent
  · exact absurd hstep (by simp)

open Dregg2.Exec in
/-- **Every honest climb is admitted** by the full authored program: its own `ascend` arm,
the depth rider its write summons, and the spent rider every exertion summons. The way
riders, the fate/bank riders and the harm rider all FAIL to match — the climb moves none
of those slots, which is exactly the anti-staple discipline working in the quiet direction. -/
theorem modelProgram_ascend_admitted {s s' : DState}
    (hInv : ModelProgramInv s) (hstep : step s .ascend = some s') :
    RecordProgram.admits dungeonExec (moveIdx .ascend)
      (encode s) (encode s') = true := by
  have hAscend := ascendCase_honest hInv hstep
  have hDepth := depthRider_ascend_honest hInv hstep
  have hSpent : (spentRider.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true :=
    case_all_of_constraints (spentRider_honest hInv hstep)
  simp only [step] at hstep
  split at hstep
  · cases hstep
    simp only [dungeonExec, dungeonProgram, CellProgram.toExec]
    apply cases_admit_of
    · refine ⟨ascendCase.toExec, by simp [programCases], ?_⟩
      simp [Case.toExec, Guard.toExec, methodIdx, TransitionGuard.matches, moveIdx]
    · intro tc htc hmatch
      simp only [programCases, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at htc
      rcases htc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exact hAscend
      · -- take: a different method entirely
        exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exact hDepth
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx, bank, pack] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx, bank, pack] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx, bank, pack] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx, bank, pack] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx, bank, pack] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx, bank, pack] at hmatch
      · exact hSpent
  · exact absurd hstep (by simp)

open Dregg2.Exec in
/-- Repaired model-to-program completeness: the native rulebook's every legal
verb step is admitted by the full authored record program once the model state
carries the minted-home provenance relation preserved by actual play. -/
theorem modelProgram_step_admitted {s s' : DState} {m : Move}
    (hInv : ModelProgramInv s) (hstep : step s m = some s') :
    RecordProgram.admits dungeonExec (moveIdx m) (encode s) (encode s') = true := by
  cases m with
  | delve => exact modelProgram_delve_admitted hInv hstep
  | ascend => exact modelProgram_ascend_admitted hInv hstep
  | unlock w => exact modelProgram_unlock_admitted hInv hstep
  | smite => exact modelProgram_smite_admitted hInv hstep
  | lunge => exact modelProgram_lunge_admitted hInv hstep
  | loot r => exact modelProgram_loot_admitted hInv hstep
  | take r => exact modelProgram_take_admitted hInv hstep
  | flee => exact modelProgram_flee_admitted hInv hstep

private theorem foldl_none_modelProgram (ms : List Move) :
    ms.foldl (fun acc m => acc.bind (fun t => step t m)) none = none := by
  induction ms with
  | nil => rfl
  | cons m rest ih => exact ih

/-- Every state produced by a legal replay carries the stronger per-relic
provenance invariant needed by the authored program.  Thus the counterexample
above is an abstraction mismatch in `Inv`, not a reachable game state. -/
theorem modelProgramInv_replay {ms : List Move} {s : DState}
    (h : replay ms = some s) : ModelProgramInv s := by
  suffices H : ∀ (xs : List Move) (s0 s1 : DState), ModelProgramInv s0 →
      xs.foldl (fun acc m => acc.bind (fun t => step t m)) (some s0) = some s1 →
      ModelProgramInv s1 by
    exact H ms genesisState s modelProgramInv_genesis h
  intro xs
  induction xs with
  | nil =>
    intro s0 s1 h0 hrun
    simp at hrun
    simpa [hrun] using h0
  | cons m rest ih =>
    intro s0 s1 h0 hrun
    simp only [List.foldl_cons, Option.bind_some] at hrun
    cases hstep : step s0 m with
    | none =>
      rw [hstep, foldl_none_modelProgram] at hrun
      simp at hrun
    | some smid =>
      rw [hstep] at hrun
      exact ih smid s1 (modelProgramInv_step h0 hstep) hrun

theorem modelProgramInv_reachable {s : DState} (h : Reachable s) :
    ModelProgramInv s := by
  obtain ⟨ms, hms⟩ := h
  exact modelProgramInv_replay hms

/-- Every legal continuation from a replay-reachable game state is accepted by
the authored `Exec.RecordProgram`; no extra invariant premise is exposed to a
caller who already has the receipt-chain reachability witness. -/
theorem reachable_step_admitted {s s' : DState} {m : Move}
    (hReach : Reachable s) (hstep : step s m = some s') :
    Dregg2.Exec.RecordProgram.admits dungeonExec (moveIdx m)
      (encode s) (encode s') = true :=
  modelProgram_step_admitted (modelProgramInv_reachable hReach) hstep

/-- Formal obstruction to the formerly desired `Inv -> legal -> admitted` theorem:
there is an `Inv` state and a legal model transition which the authored program
correctly refuses because the state violates per-relic minted-home provenance. -/
theorem inv_not_sufficient_for_step_admission :
    ∃ s s' : DState,
      Inv s ∧ @step (instAt 0) s .delve = some s' ∧
        Dregg2.Exec.RecordProgram.admits (@dungeonExec (instAt 0)) (moveIdx .delve)
          (encode s) (encode s') = false := by
  refine ⟨wrongHomeState,
    { wrongHomeState with depth := 1, wounds := 0, spent := 1 },
    wrongHomeState_inv, wrongHomeState_delve_legal, wrongHomeState_delve_refused⟩

#assert_axioms way_flip_exhibits_key
#assert_axioms way_flip_key_mutation_refused
#assert_axioms modelProgramInv_genesis
#assert_axioms modelProgramInv_step
#assert_axioms modelProgram_delve_admitted
#assert_axioms modelProgram_ascend_admitted
#assert_axioms modelProgram_unlock_admitted
#assert_axioms modelProgram_smite_admitted
#assert_axioms modelProgram_lunge_admitted
#assert_axioms modelProgram_loot_admitted
#assert_axioms modelProgram_take_admitted
#assert_axioms modelProgram_flee_admitted
#assert_axioms custody_hop_of_step
#assert_axioms modelProgram_step_admitted
#assert_axioms modelProgramInv_replay
#assert_axioms modelProgramInv_reachable
#assert_axioms reachable_step_admitted
#assert_axioms wrongHomeState_inv
#assert_axioms wrongHomeState_delve_legal
#assert_axioms wrongHomeState_delve_refused
#assert_axioms inv_not_sufficient_for_step_admission

end Dregg2.Games.Dungeon.Prog
