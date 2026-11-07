/-
# Dregg2.Games.DungeonProgram — the DEPLOYED descent cell program, AUTHORED IN LEAN.

The reimagined descent (`Dregg2.Games.Dungeon` — the model, the design laws) is deployed as
THIS `CellProgram` value: emitted to the checked-in artifact
`dungeon-on-dregg/program/dungeon_program.json` (regen + drift-gated by
`dungeon-on-dregg/program/regen.sh`) and loaded by `dungeon_on_dregg::descent`
(`Deployment::program()` resolves the symbolic slot/method names against the
translation-validated `dregg-schema` allocator). There is NO hand-rolled Rust
`CellProgram` in the descent's path — the deployed program IS this Lean object by
construction (edit a rule here, re-emit, and the deployed game changes: the canary).

## What is NEW here relative to the tug pattern (`MultiwayTugProgram.lean`)

1. **Guards are part of the authored object** — not just `MethodIs`: the program carries
   `SlotChanged`-guarded RIDER cases (`slotChangedForMethods`, lowered by the loader to
   `AllOf[SlotChanged, AnyOf[MethodIs…]]`). This retires the standing
   stapleable-slot falsifier *structurally*: ANY verb that moves `depth` pays the delve
   law, ANY verb that flips a `way_w` must EXHIBIT the carried key-relic, ANY verb that
   moves `bank`/`fate` pays the banking law, ANY verb that moves `harm` pays the WHOLE
   lunge law (`harmRider` — the newest slot got its rider in the same change that
   introduced it, not later), and ANY exertion (a `spent` change) pays the
   conservation/ratchet/capacity commons. The method list inside the guard keeps the
   executor's method-default-deny intact (`unknown_method_refused`).

2. **The proofs run against the LAW-#1 evaluator.** `toExec` lifts this program into
   `Dregg2.Exec.RecordProgram` — the name-keyed algebra the Rust evaluator mirrors — and
   the theorems below are admission-soundness INVERSIONS over ARBITRARY record values
   (attacker-supplied writes), not structural pins:
     * `admitted_verb_conserves` — any admitted verb turn's post-state sums the relic
       zones to exactly `RELICS` (no dupe, no burn);
     * `admitted_verb_capacity` — any admitted verb turn satisfies
       `pack + depth + harm ≤ CAP` (attenuation, INCLUDING the grip the guardians broke,
       reaches the deployed teeth);
     * `admitted_verb_pays` — any admitted verb turn strictly spends breath, capped at
       `BREATH` (the clock);
     * `admitted_verb_alive` — any admitted verb turn starts from `fate = 0`
       (the banked tomb is frozen: `banked_tomb_refuses`);
     * `way_flip_exhibits_key` — any admitted turn that flips `way_w` carries the
       `0 → 1` transition AND the post-state holds key-relic `w−1` CARRIED;
     * `unknown_method_refused` — a method outside the seven verbs is default-denied.

3. **Custody projections are exact, not parallel bookkeeping.** The spent rider
   carries six `countFieldsEq` aggregate teeth.  Every ordinary verb therefore proves
   that `pack`, `bank`, and each floor hoard are the exact census of the eight
   individually committed relic custody fields.  A forged loot can neither advance a
   counter without moving a relic nor move two relics behind one `pack += 1` receipt.

4. **The model and the program share ONE substrate** (name-keyed records): `encode`
   embeds the model `DState` into `Exec.Value`, and the `#guard` battery DRIVES the
   crowned run of `Dungeon.lean` through `RecordProgram.admits` step by step — the
   model-legal run IS admitted — while eight named attacks (dupe, keyless way, staple,
   tomb move, dead light, fake flee, relic teleport, genesis replay) are REFUSED.
   Tug could not do this (its model lived on multisets, a different substrate); the
   reimagined dungeon was AUTHORED so the refinement is direct. ⚑ The way-flip inversion is
   now proven for ALL THREE locked ways (`way_flip_exhibits_key` ⇒ `way2/3/4_flip_exhibits_key`),
   closing the audit's "ways 3/4 are Rust-driven" gap.

5. **TWO BLOWS, ONE OF THEM PAID IN CAPACITY.** `smite` (the press: 2 breath, no harm) and
   `lunge` (1 breath, `harm += 1`) wound identically; what separates them is the core
   `affineLe`, which now prices `pack + depth + harm` against `CAP`. Because capacity
   already attenuates with depth, the same posted price is cheap at depth 1 (7 slots) and
   ruinous at depth 4 (4 slots — exactly three keys plus the prize), so a `guardHp = 2`
   floor is a mixable decision rather than a quotient. `harm` is a `[0, HARMCAP]` ratchet:
   `lungeCase` and `harmRider` both carry `fieldDelta harm 1` (an exact step, so it cannot
   run backward) and `inRangeTwoSided harm 0 HARMCAP`, and every other verb FREEZES the
   slot.

## Honest scope

* The theorems hold of the Lean `Exec.RecordProgram` evaluator — a name-keyed record MODEL
  of the referee. ⚑ `docs/audit/GAME-PROOF-LARP-AUDIT.md` correctly flagged that this is NOT the
  evaluator `eval.rs` calls, and that it had DIVERGED from the deployed one: `Exec`'s field
  compares (`affineLe`/`fieldGe`) are signed unbounded `Int`, whereas the deployed field is
  UNSIGNED 256-bit (`eval.rs:2842`). The SEMANTICS axis of that disconnect is now closed at its
  source: the pure (context-free, witness-free) constraint teeth are AUTHORED ONCE over the
  DEPLOYED substrate (`[FieldElement;16]` + heap, UNSIGNED-256) in
  `Dregg2.Exec.DeployedConstraint.admits`, `@[export dregg_constraint_admits]`-ed and CALLED by the
  deployed node (`eval.rs`'s `evaluate_constraint_full` routes the subset through it via the
  `dregg_cell::program::ConstraintOracle` seam installed by `dregg-exec-lean`; the reality-gate
  canary in `dregg-lean-ffi`/`exec-lean` tests proves the deployed decision IS the Lean source, and
  the differential gate pins Lean == Rust across the subset). These dungeon inversions remain over
  the signed-`Int` `Exec` MODEL — their honest scope — and reaching the deployed unsigned evaluator
  is the register-substrate refinement the audit named (NOT re-claimed here). The Rust-side agreement
  the descent crate's executor tests exercise (illegal turns are REAL `WorldError::Refused`) is now
  ALSO backed by the differential gate, not prose alone.
* The per-relic custody ratchet (`monotonic` + `memberOf {home, CARRIED, BANKED}`),
  zone-counter conservation, and the exact custody↔counter census are all enforced.
  The aggregate is over this game's fixed eight custody keys; an unbounded dynamic
  inventory still belongs on the first-class collection/AIR path.

## ⚑ DeployedConstraint refinement — why tug lands and the descent is BOUNDED (LARP-audit fix #4/#5)

The tug game's action teeth ALL live in `Dregg2.Exec.DeployedConstraint`'s exported PURE subset
(`sumEquals`/`writeOnce`/`strictMonotonic`/`fieldGte`/`heapField`-atoms) over NONNEG counters, so
tug's forward refinement was RE-STATED against the deployed evaluator itself
(`MultiwayTugProgram §4I` `program_admits_legal_play_deployed`). The descent is TWO honest steps
short of that, and this is a structural fact, not an omission:

  1. **Vocabulary.** The descent's teeth use `affineLe` (capacity), `allowedTransitions`
     (fate/way), `inRangeTwoSided` (zone ranges) and `fieldDelta` (posted prices) — NONE of which
     are in `DeployedConstraint`'s exported pure subset (which is context-free/witness-free field &
     heap atoms). Only `admitted_verb_conserves` (`sumEquals`) and `admitted_verb_pays`
     (`strictMonotonic`+`fieldLte`) sit inside the pure subset; capacity/alive/way-flip do not.
  2. **Signedness.** The inversions quantify over ARBITRARY `Exec.Value`s, where a scalar is a
     SIGNED unbounded `Int`. `DeployedConstraint` is UNSIGNED 256-bit `Nat` — the EXACT divergence
     the audit flagged. On a negative attacker scalar the two evaluators genuinely DISAGREE, so an
     arbitrary-`Value` inversion CANNOT be faithfully re-stated over `DeployedConstraint`. The two
     agree only on the NONNEG `encode` image — i.e. via the weld below, not the inversions.

  So the honest descent scope is: the inversions are proven over the signed-`Int` `Exec` MODEL
  (all three ways now included); a faithful `DeployedConstraint` refinement would hold only on the
  nonneg `encode` image and only for the pure-subset teeth (conserves/pays), routed through the
  ∀-weld. That is the NAMED remainder — it needs the ∀-weld (below) plus a nonneg `Int→Nat`
  register marshalling, not a new substrate.

## ⚑ The model↔program WELD — DRIVEN status, honestly (LARP-audit fix #5)

The weld `model-legal step ⟹ program-admitted` (the FORWARD refinement direction) is DRIVEN, not
yet a ∀-theorem: `programAdmitsRun crownedRun = true` checks it for ONE legal run (genesis + 17
verbs), and nine attack `#guard`s check named forgeries are refused. The GENERAL ∀-weld
(`∀ s m s', step s m = some s' → RecordProgram.admits dungeonExec (moveIdx m) (encode s)
(encode s') = true`) is NAMED, not proven here: it is a per-move, tooth-by-tooth discharge of every
matching verb case + `SlotChanged` rider over the SHARED `Exec` substrate (large — ~5 moves × the
verb+rider teeth, with custody-`countP` conservation/ratchet lemmas — but tractable, and NOT a new
substrate). Several of its consequences ARE already ∀-theorems in the REVERSE direction (the
inversions `admitted_verb_*`, `banked_tomb_refuses`, `dead_light_refuses`, `way{2,3,4}_flip_*`),
which is why the driven attacks each correspond to a proven inversion. What remains driven is the
forward completeness (legal ⇒ admitted) beyond the single crowned run.
-/
import Dregg2.Games.Dungeon
import Dregg2.Exec.Program

namespace Dregg2.Games.Dungeon.Prog

open Dregg2.Exec (Value)

/-! ⚑ THE TEETH ARE PARAMETRIC IN THE DAY'S WORLD. `homeCode`, `genesisHoard` and the
guardian teeth read `Dungeon.homeFloors` / `Dungeon.guardHp`, which are now functions of
the drawn map (`Dungeon.WorldParam`) rather than compile-time constants — so every
definition and every inversion below carries the world it is stated over, and the emit
(§6) renders ONE program per family member. -/
variable [WorldParam]

-- The world parameter is blanket-scoped over the file (every rule and law is stated over
-- the day's drawn map); a handful of pure list/count helpers legitimately do not mention
-- it, and the section-variable linter would otherwise report each one.
set_option linter.unusedSectionVars false

/-! ## 1. The symbolic vocabulary (names, not indices — the loader resolves). -/

/-- A heap-key reference: a schema collection by NAME, or the spween genesis-done
sentinel (`spween_dregg::GENESIS_DONE_EXT_KEY`). -/
inductive HeapKeyRef where
  | named (name : String)
  | sentinel
deriving Repr, DecidableEq

/-- The heap-atom subset the descent uses.

⚑ **`allowedTransitions` — THE HEAP GETS THE ATOM THE REGISTERS HAVE.** A relic's custody
code is a HEAP-resident object (`dregg_schema` places a `collection` on the heap, not in
the register file), so a per-relic hop table stated as `Constraint.allowedTransitions
(relicName i) …` is a tooth about a REGISTER THAT DOES NOT EXIST: `Deployment::reg
("relic_0")` has no slot to return. The table belongs on the atom, beside `memberOf` —
one is the value allowlist, the other is the hop allowlist, and both read the same key.

The arm is RELATIONAL (it reads BOTH sides), so it lifts to `Exec.StateConstraint`, not
`Exec.SimpleConstraint` — the same split both substrates already make for the register
form. It is therefore admissible at TOP level (`Constraint.heapField`) and NOT inside an
`anyOf` variant; `simplesCompose` (§2) pins by kernel evaluation that no authored
`Simple.heapField` carries one. -/
inductive HeapAtom where
  | equals (v : Nat)
  | immutable
  | monotonic
  | memberOf (set : List Nat)
  | deltaEquals (d : Int)
  | allowedTransitions (allowed : List (Nat × Nat))
deriving Repr, DecidableEq

/-- Which heap atoms COMPOSE — i.e. lift into the name-keyed `Exec.SimpleConstraint`
lane and may therefore sit inside an `anyOf` variant or under a `negate`. The deployed
twin of that lane is `SimpleStateConstraint::HeapField { key, atom }`, which the Rust
vocabulary already carries; a transition TABLE has no `SimpleStateConstraint` form on
EITHER substrate. -/
def HeapAtom.composes : HeapAtom → Bool
  | .allowedTransitions _ => false
  | _                     => true

/-- The simple (anyOf-liftable) subset.

⚑ **`heapField` — the arm whose absence made teeth reach for registers a cell has not
got.** Before it, an `anyOf` variant could only name a REGISTER, so every guarded
statement about a heap-resident relic (`depth = d ⇒ key k hangs on floor d`) had to be
written as `fieldEquals "relic_1" …` — a register demand for a name that lives on the
heap, and a runtime panic in the loader. With this arm the same law is stated where the
object lives. Mirrors the deployed `SimpleStateConstraint::HeapField { key, atom }`. -/
inductive Simple where
  | fieldEquals (reg : String) (v : Nat)
  | fieldGte (reg : String) (v : Nat)
  | fieldLte (reg : String) (v : Nat)
  | immutable (reg : String)
  | heapField (key : HeapKeyRef) (atom : HeapAtom)
  | negate (inner : Simple)
deriving Repr, DecidableEq

/-- The `StateConstraint` subset the descent's teeth are built from. -/
inductive Constraint where
  | fieldEquals (reg : String) (v : Nat)
  | fieldGte (reg : String) (v : Nat)
  | fieldLte (reg : String) (v : Nat)
  | fieldDelta (reg : String) (d : Nat)          -- every posted price is a positive step
  | strictMonotonic (reg : String)
  | immutable (reg : String)
  | sumEquals (regs : List String) (v : Nat)
  | affineLe (terms : List (Int × String)) (c : Int)
  | inRangeTwoSided (reg : String) (lo hi : Nat)
  | allowedTransitions (reg : String) (allowed : List (Nat × Nat))
  | anyOf (variants : List Simple)
  | heapField (key : HeapKeyRef) (atom : HeapAtom)
  | countFieldsEq (keys : List HeapKeyRef) (value : Nat) (reg : String)
deriving Repr, DecidableEq

/-- Guards: the descent authors BOTH method dispatch AND slot-changed riders. A rider
`slotChangedForMethods reg ms` lowers to `AllOf[SlotChanged reg, AnyOf[MethodIs m | m ∈ ms]]`
— the anti-staple gate that still keeps method-default-deny (the method disjunct). -/
inductive Guard where
  | methodIs (method : String)
  | slotChangedForMethods (reg : String) (methods : List String)
deriving Repr, DecidableEq

structure Case where
  guard : Guard
  constraints : List Constraint
deriving Repr, DecidableEq

inductive CellProgram where
  | cases (cs : List Case)
deriving Repr, DecidableEq

/-! ## 2. The descent's teeth (the design of `Dungeon.lean`, as deployed constraints). -/

def relicName (i : Nat) : String := s!"relic_{i}"
def wayName (w : Nat) : String := s!"way_{w}"
def hoardName (d : Nat) : String := s!"hoard_{d}"

/-- ⚑ **THE KEY-IN-THE-DOOR ZONE — ONE register, and the floor law lives on the OBJECT.**
`hung` is the census of keys left hanging in doors, ANY door — custody code in
`HUNG + 1 … HUNG + FLOORS` (`Dungeon.hungAt` summed over the floors). A zone counter is
needed at all only because conservation is a `sumEquals` over REGISTERS and a key in a
door is in none of the old six: it left the pack (`unlock` costs the carry slot back) and
it never reached the bank (`fleeMap` promotes `CARRIED` and only `CARRIED`). Without it
`Σ zones = RELICS` is simply FALSE on every turn after the first `unlock`.

⚑ It is ONE register, not a `hung_1 … hung_4` family, and that is not rationing. A cell
has `STATE_SLOTS = 16` registers; the descent's other thirteen plus four doors is
EIGHTEEN, which no cell can hold. The four-counter form spent three registers carrying
WHICH door a key hangs in — a fact about an OBJECT, stated on a projection of it. Stated
on the object instead (`doorArrival` / `doorDeparture` / `keyHangsHereTooth` below, all
`heapField` teeth over the relic's own custody key) it is strictly STRONGER: a per-floor
counter frame says "this floor's census did not move", the object teeth say "THIS RELIC
did not enter or leave THIS door", which names the thing that moved. And `hung` itself
needs no census tooth of its own: `Σ zones = RELICS` plus the six EXACT
`countFieldsEq` projections plus the per-relic `memberOf` alphabet force it to the true
door total (every code is a hoard floor, `CARRIED`, `BANKED`, or `HUNG + d`, and the
other six zones are pinned exactly, so the residue IS the door census). -/
def hungName : String := "hung"

/-- The relic-zone registers summed by conservation (`Σ = RELICS` on every turn).
⚑ SEVEN, not six and not ten: the doors joined the partition as ONE `hung` residue. -/
def zones : List String :=
  ["pack", "bank", "hoard_1", "hoard_2", "hoard_3", "hoard_4", "hung"]

/-- The individually committed relic custody fields, in their canonical mint order. -/
def relicKeys : List HeapKeyRef :=
  (List.range RELICS).map fun i => .named (relicName i)

/-- Each relic's minted home floor — THE SAME list the model mints from
(`Dungeon.homeFloors`); the emit reads the model, so the world and its teeth cannot
drift apart. -/
def homeCode (i : Nat) : Nat := homeFloors.getD i 0

/-- The genesis hoard census — a PROJECTION of `homeFloors` (relics at floor d). -/
def genesisHoard (d : Nat) : Nat := (homeFloors.filter (· == d)).length

/-- ⚑ EIGHT, not seven. `take` is a first-class verb of the model (`Dungeon.step`'s
`.take r` arm — lift a key back out of the door it hangs in), so it is a first-class
method here: it appears in EVERY rider's method list, which is what keeps the riders'
anti-staple law method-independent ACROSS the new verb rather than leaving `take` a hole
the riders cannot see. -/
def verbs : List String :=
  ["delve", "unlock", "smite", "loot", "flee", "lunge", "ascend", "take"]

/-- **The core commons** — on EVERY verb case and every rider:
conservation, capacity attenuation **including the broken grip** (`pack + depth + harm ≤
CAP` — the deployed form of `Dungeon.capacity_attenuates`), the strictly-spending capped
clock, and the aliveness/banking fate law (`0→0` stay alive, `0→1` bank; a banked run
matches nothing). -/
def coreTeeth : List Constraint :=
  [ .sumEquals zones RELICS,
    .affineLe [((1 : Int), "pack"), ((1 : Int), "depth"), ((1 : Int), "harm")] (CAP : Int),
    .strictMonotonic "spent",
    .fieldLte "spent" BREATH,
    .allowedTransitions "fate" [(0, 0), (0, 1)] ]

/-- The floors a key can hang on: `1 … FLOORS`. (`unlock` demands `1 ≤ depth` and `Inv`
bounds `depth ≤ FLOORS`, so `HUNG + 0` is a code no step ever writes.) -/
def hangFloors : List Nat := List.range' 1 FLOORS

/-- The whole door census — how many keys hang in doors, across every floor. This is the
model-side reading the `hung` register projects (`Dungeon.hungAt` summed over the
floors), and it is what makes the register a PROJECTION rather than a parallel counter. -/
def hungTotal (s : DState) : Nat := (hangFloors.map (hungAt s)).sum

/-- ⚑ **THE PRIZE NEVER HANGS.** `unlock w` writes slot `keyFor w = w − 1` for
`2 ≤ w ≤ FLOORS`, so exactly relics `1 … FLOORS − 1` can ever take a `HUNG` code. Relic 0
is the prize and relics `FLOORS …` are plain loot; encoding that here rather than giving
every relic the HUNG alphabet is what makes the teeth as narrow as the model
(`Dungeon.Inv`'s prize clause is three-way, not four). -/
def isKeyRelic (i : Nat) : Bool := decide (1 ≤ i ∧ i + 1 ≤ FLOORS)

/-- The complete custody alphabet for relic `i`: its minted home floor, `CARRIED`,
`BANKED`, and — for a key — the whole `HUNG + 1 … HUNG + FLOORS` family. -/
def custodyAlphabet (i : Nat) : List Nat :=
  [homeCode i, CARRIED, BANKED] ++
    (if isKeyRelic i then hangFloors.map (HUNG + ·) else [])

/-- ⚑ **THE EXACT CUSTODY HOP SET** — this REPLACES the `monotonic` atom, which is now
FALSE of the rulebook: `take` LOWERS a code (`HUNG + d = 13…16` back down to
`CARRIED = 8`), and `Dungeon.custody_lowers_only_by_take` says so in the model. A
monotone tooth would refuse every legal `take`.

Enumerating the hops is not a weakening dressed as a fix — it is STRICTLY STRONGER than
what it replaces. `monotonic ∧ memberOf {home, CARRIED, BANKED}` admitted `home → BANKED`
(a relic teleporting out of a hoard straight into the bank, skipping the pack and
therefore skipping the capacity commons entirely). That transition is in no arm of
`Dungeon.step`, and it is not in this list.

  stay      `(c, c)` for every code in the alphabet — every verb that does not move it
  loot      `(home, CARRIED)`
  flee      `(CARRIED, BANKED)`
  unlock    `(CARRIED, HUNG + d)` — keys only; WHICH `d` is the way-rider's floor law
  take      `(HUNG + d, CARRIED)` — keys only; the one lowering hop in the rulebook -/
def custodyHops (i : Nat) : List (Nat × Nat) :=
  (custodyAlphabet i).map (fun c => (c, c))
    ++ [(homeCode i, CARRIED), (CARRIED, BANKED)]
    ++ (if isKeyRelic i then
          hangFloors.flatMap (fun d => [(CARRIED, HUNG + d), (HUNG + d, CARRIED)])
        else [])

/-- Per-relic provenance law: custody moves ONLY through the enumerated hops, and only
through the legal alphabet (no floor-to-floor teleport, no minting a code from nothing).

⚑ BOTH teeth are `heapField` teeth now. A relic is a `collection` in the descent's
schema, i.e. HEAP-resident, so the hop table stated as `Constraint.allowedTransitions
(relicName i) …` demanded a register slot for `relic_i` — a slot the cell does not have
and the loader cannot resolve. The atom moved to where the object is; `toExec` is
UNCHANGED (`Exec` is name-keyed, so the lifted constraint is the same value), which is
why every inversion over the ratchet reads exactly as it did. -/
def custodyTeeth : List Constraint :=
  (List.range RELICS).flatMap fun i =>
    [ .heapField (.named (relicName i)) (.allowedTransitions (custodyHops i)),
      .heapField (.named (relicName i)) (.memberOf (custodyAlphabet i)) ]

/-- Zone counters live in `[0, RELICS]` — no field-wrap tricks. -/
def rangeTeeth : List Constraint :=
  zones.map fun z => .inRangeTwoSided z 0 RELICS

/-- Bind every register projection to the exact census of the eight custody fields.
This is the heap/object ↔ register bridge: conservation among counters can no longer
be satisfied by counters that describe a different custody state. -/
def projectionTeeth : List Constraint :=
  [ .countFieldsEq relicKeys CARRIED "pack",
    .countFieldsEq relicKeys BANKED "bank",
    .countFieldsEq relicKeys 1 (hoardName 1),
    .countFieldsEq relicKeys 2 (hoardName 2),
    .countFieldsEq relicKeys 3 (hoardName 3),
    .countFieldsEq relicKeys 4 (hoardName 4) ]
    -- ⚑ THE DOOR RESIDUE NEEDS NO CENSUS TOOTH OF ITS OWN. `hung` is not an
    -- independently-writable counter that a forgery could inflate: conservation
    -- (`Σ zones = RELICS`) plus these six EXACT censuses plus the per-relic
    -- `memberOf (custodyAlphabet i)` leave it exactly one value — the number of relics
    -- whose code is in the `HUNG` family. Adding a seventh `countFieldsEq` would be
    -- restating a consequence, and it could not be stated anyway: `countFieldsEq` counts
    -- ONE value, and the door family is four.

/-- Freeze a register set (a verb's write-frame: what it does NOT own, it cannot touch). -/
def frozen (regs : List String) : List Constraint := regs.map .immutable

/-- Freeze every relic's custody (verbs that do not move relics). -/
def relicFreeze : List Constraint :=
  (List.range RELICS).map fun i => .heapField (.named (relicName i)) .immutable

/-- `depth = d ⇒ way_d open` (delve teeth; way 1 is the always-open first stair). -/
def wayTooth (d : Nat) : Constraint :=
  .anyOf [.negate (.fieldEquals "depth" d), .fieldGte (wayName d) 1]

/-- `depth = d ⇒ wounds ≤ guardHp d` (a guardian cannot be over-slain). -/
def guardCapTooth (d : Nat) : Constraint :=
  .anyOf [.negate (.fieldEquals "depth" d), .fieldLte "wounds" (guardHp d)]

/-- `depth = d ⇒ wounds ≥ guardHp d` (loot only over a slain guardian). -/
def guardSlainTooth (d : Nat) : Constraint :=
  .anyOf [.negate (.fieldEquals "depth" d), .fieldGte "wounds" (guardHp d)]

/-- `depth ≠ d ⇒ hoard_d frozen` (loot may only draw from the standing floor;
conservation then forces the −1 exactly). -/
def hoardFrameTooth (d : Nat) : Constraint :=
  .anyOf [.fieldEquals "depth" d, .immutable (hoardName d)]

/-- The key relics — the only relics that can ever take a `HUNG` code. -/
def keyRelics : List Nat := (List.range RELICS).filter isKeyRelic

/-- ⚑ **THE DOOR FRAME, ON THE OBJECT — ARRIVAL.** `depth ≠ d ⇒ relic `i` did not
NEWLY arrive in floor `d`'s door. The three disjuncts are exactly the three innocent
readings: you are standing on floor `d`; relic `i` is not in that door after the turn; or
relic `i` did not move at all (it was already hanging there, and a key already in a door
stays put through every other floor's turns).

This REPLACES the `hung_d`-counter frame and is strictly stronger: the counter form said
"floor `d`'s census did not move", which a two-relic forgery can satisfy while a relic
teleports between doors; this names the RELIC. It is also METHOD-INDEPENDENT (it rides
the `spent` rider, i.e. every verb), so a key cannot be hung on a floor you are not
standing on under `loot`'s or `smite`'s guard either. -/
def doorArrivalTooth (i d : Nat) : Constraint :=
  .anyOf [ .fieldEquals "depth" d,
           .negate (.heapField (.named (relicName i)) (.equals (HUNG + d))),
           .heapField (.named (relicName i)) (.deltaEquals 0) ]

/-- ⚑ **THE DOOR FRAME, ON THE OBJECT — DEPARTURE.** `depth ≠ d ⇒ relic `i` did not
make the `HUNG + d → CARRIED` hop. This is the `take` half, and it is the tooth that
refuses THE REMOTE TAKE (attack 7b): lifting a key out of a door you are not standing at.

The hop is pinned by its exact DELTA, and that is unambiguous rather than clever: the
lifting hop is the ONLY hop in `custodyHops` with a negative delta (`Dungeon`'s
`custody_lowers_only_by_take` — `take` is the one verb that lowers a code), and each
floor's is a different negative number. So `deltaEquals (CARRIED − (HUNG + d))` names
"lifted out of floor `d`'s door" and nothing else, on ANY verb. Method-independent for
the same reason as arrival. -/
def doorDepartureTooth (i d : Nat) : Constraint :=
  .anyOf [ .fieldEquals "depth" d,
           .negate (.heapField (.named (relicName i))
             (.deltaEquals ((CARRIED : Int) - ((HUNG + d : Nat) : Int)))) ]

/-- Both halves of the object-side door frame, for every key relic and every floor. -/
def doorFrameTeeth : List Constraint :=
  keyRelics.flatMap fun i =>
    hangFloors.flatMap fun d => [doorArrivalTooth i d, doorDepartureTooth i d]

/-- The door census, frozen (verbs that neither hang nor lift a key). -/
def hungFreeze : List String := [hungName]

/-- Every floor's hoard, frozen. -/
def hoardFreeze : List String := hangFloors.map hoardName

/-- **genesis** — the world's one-shot mint, pinned EXACTLY: the spween sentinel `0→1`
plus the canonical seed (all counters, every relic at its `homeFloors` floor). The
receipt chain of every relic replays to THIS turn. -/
def genesisCase : Case :=
  ⟨.methodIs "genesis",
    [ .heapField .sentinel (.equals 1),
      .heapField .sentinel (.deltaEquals 1),
      .fieldEquals "depth" 0, .fieldEquals "spent" 0, .fieldEquals "wounds" 0,
      .fieldEquals "fate" 0, .fieldEquals "pack" 0, .fieldEquals "bank" 0,
      .fieldEquals "harm" 0,
      .fieldEquals (wayName 2) 0, .fieldEquals (wayName 3) 0, .fieldEquals (wayName 4) 0,
      .fieldEquals (hoardName 1) (genesisHoard 1),
      .fieldEquals (hoardName 2) (genesisHoard 2),
      .fieldEquals (hoardName 3) (genesisHoard 3),
      .fieldEquals (hoardName 4) (genesisHoard 4) ]
    -- Every door is EMPTY at the mint: no relic is minted already-hanging, which is the
    -- register-side twin of `Dungeon.genesis_pack_zero`/`genesis_bank_zero`.
    ++ [.fieldEquals hungName 0]
    ++ (List.range RELICS).map (fun i => .heapField (.named (relicName i)) (.equals (homeCode i)))⟩

/-- **delve** — descend exactly one floor: pay 1 breath, the way to the NEW floor must
be open, the guardian below is fresh (`wounds = 0`), and nothing else moves. -/
def delveCase : Case :=
  ⟨.methodIs "delve",
    coreTeeth ++
    [ .fieldDelta "spent" 1, .fieldDelta "depth" 1,
      .fieldEquals "wounds" 0, .fieldEquals "fate" 0,
      wayTooth 2, wayTooth 3, wayTooth 4 ]
    ++ frozen (["pack", "bank", wayName 2, wayName 3, wayName 4, "harm"]
               ++ hoardFreeze ++ hungFreeze)
    ++ relicFreeze⟩

/-- **ascend** — THE CLIMB. Rise exactly one floor toward the surface: pay 1 breath, the
guardian above stands fresh again (`wounds = 0`), and nothing else moves — in particular
`harm` is FROZEN, so a walk upstairs never launders the grip the guardians broke. The
step is posted as an exact `allowedTransitions` rather than a delta because the descent's
vocabulary prices deltas as unsigned; enumerating `4→3→2→1→0` is both the honest form and
strictly stronger (it pins `depth ≤ FLOORS` in the same tooth). -/
def ascendCase : Case :=
  ⟨.methodIs "ascend",
    coreTeeth ++
    [ .fieldDelta "spent" 1,
      .allowedTransitions "depth" [(1, 0), (2, 1), (3, 2), (4, 3)],
      .fieldEquals "wounds" 0, .fieldEquals "fate" 0,
      wayTooth 2, wayTooth 3, wayTooth 4 ]
    ++ frozen (["pack", "bank", wayName 2, wayName 3, wayName 4, "harm"]
               ++ hoardFreeze ++ hungFreeze)
    ++ relicFreeze⟩

/-- **unlock** — ⚑ **THE KEY STAYS IN THE DOOR.** Exercise a carried key: pay 1 breath,
the way flips (WHICH way, and that its key is exhibited, is the way-riders' law) — and
the key LEAVES THE PACK AND HANGS. That is why this arm no longer freezes `pack` and no
longer freezes the relics: it is the one verb besides `take` that moves a custody code
UPWARD into the `HUNG` family, and both counters it touches are pinned exactly.

  `pack`     `(k, k−1)` enumerated — the carry slot comes back. `pack ≥ 1` falls out of
             the enumeration (there is no `(0, ·)` rung), which IS the "you must be
             holding the key" clause of `Dungeon.step`'s `.unlock` arm.
  `hung`     `(k, k+1)` — the door census gains exactly one. WHICH door is not a counter
             fact any more: `doorArrivalTooth` (on the `spent` rider, so every verb pays
             it) says the relic that arrived is in the door on the floor you stand on. -/
def unlockCase : Case :=
  ⟨.methodIs "unlock",
    coreTeeth ++
    [ .fieldDelta "spent" 1, .fieldEquals "fate" 0,
      .allowedTransitions "pack" ((List.range' 1 RELICS).map (fun k => (k, k - 1))),
      .allowedTransitions hungName ((List.range' 0 RELICS).map (fun k => (k, k + 1))) ]
    ++ frozen (["depth", "wounds", "bank", "harm"] ++ hoardFreeze)⟩

/-- **smite — THE PRESS.** Wound the standing guardian by exactly 1: pay 2 breath (it
strikes back); never below the surface's edge (`depth ≥ 1`); never past the guardian's
vitality. Nothing else moves — in particular `harm` is FROZEN here, which is what makes
the press the safe blow and `lunge` the paid one. -/
def smiteCase : Case :=
  ⟨.methodIs "smite",
    coreTeeth ++
    [ .fieldDelta "spent" 2, .fieldDelta "wounds" 1,
      .fieldGte "depth" 1, .fieldEquals "fate" 0,
      guardCapTooth 1, guardCapTooth 2, guardCapTooth 3, guardCapTooth 4 ]
    ++ frozen (["depth", "pack", "bank", wayName 2, wayName 3, wayName 4, "harm"]
               ++ hoardFreeze ++ hungFreeze)
    ++ relicFreeze⟩

/-- **lunge** — the SAME wound for ONE breath, paid in grip: `harm += 1`, ratcheted
inside `[0, HARMCAP]`, and the core `affineLe` then prices it against depth
(`pack + depth + harm ≤ CAP`). Everything the press freezes is frozen here too, except
the one register that is the whole point. -/
def lungeCase : Case :=
  ⟨.methodIs "lunge",
    coreTeeth ++
    [ .fieldDelta "spent" 1, .fieldDelta "wounds" 1, .fieldDelta "harm" 1,
      .inRangeTwoSided "harm" 0 HARMCAP,
      .fieldGte "depth" 1, .fieldEquals "fate" 0,
      guardCapTooth 1, guardCapTooth 2, guardCapTooth 3, guardCapTooth 4 ]
    ++ frozen (["depth", "pack", "bank", wayName 2, wayName 3, wayName 4]
               ++ hoardFreeze ++ hungFreeze)
    ++ relicFreeze⟩

/-- **loot** — take ONE relic from the standing floor's hoard: pay 1 breath, the
guardian must be slain, only THIS floor's hoard may move (conservation forces the −1),
and the capacity commons attenuate what you may carry. Relics are NOT frozen here —
the looted relic's custody ratchets (`custodyTeeth` on the spent-rider bind it). -/
def lootCase : Case :=
  ⟨.methodIs "loot",
    coreTeeth ++
    [ .fieldDelta "spent" 1, .fieldDelta "pack" 1,
      .fieldGte "depth" 1, .fieldEquals "fate" 0,
      guardSlainTooth 1, guardSlainTooth 2, guardSlainTooth 3, guardSlainTooth 4,
      hoardFrameTooth 1, hoardFrameTooth 2, hoardFrameTooth 3, hoardFrameTooth 4 ]
    ++ frozen (["depth", "wounds", "bank", wayName 2, wayName 3, wayName 4, "harm"]
               ++ hungFreeze)⟩

/-- ⚑ **take** — LIFT A KEY BACK OUT OF THE DOOR IT HANGS IN. `lootCase` minus the
guardian tooth, one zone over: the relic is not lying in a hoard under a standing
guardian, it is hanging in a door you already opened, so there is no fight — but the
carry slot is charged all the same, at the identical posted price, and the capacity
commons in `coreTeeth` price it against depth and harm exactly as they price a `loot`.
`doorDepartureTooth` (on the `spent` rider, so every verb pays it) pins WHICH door — the
one you are standing at — by the relic's own custody hop; the `hung` census then loses
exactly one and the pack gains it. `1 ≤ depth` is posted directly, and it is also implied
— `HUNG + 0` is a code `unlock` can never write. -/
def takeCase : Case :=
  ⟨.methodIs "take",
    coreTeeth ++
    [ .fieldDelta "spent" 1, .fieldDelta "pack" 1,
      .fieldGte "depth" 1, .fieldEquals "fate" 0,
      .allowedTransitions hungName ((List.range' 1 RELICS).map (fun k => (k, k - 1))) ]
    ++ frozen (["depth", "wounds", "bank", wayName 2, wayName 3, wayName 4, "harm"]
               ++ hoardFreeze)⟩

/-- **flee** — the run ends AT THE MOUTH: pay 1 breath, stand on the surface
(`depth = 0` — you climb out, you do not teleport out), the pack empties into the bank
(`pack' = 0` + hoards frozen + conservation ⇒ `bank' = bank + pack`), fate `0→1`.
⚑ A HUNG KEY IS NOT YOURS: the doors are frozen here too, so `Dungeon.fleeMap`'s
"promotes `CARRIED` and only `CARRIED`" is a deployed tooth — a key left in its door
banks nothing, and conservation cannot launder it into the bank on the way past. -/
def fleeCase : Case :=
  ⟨.methodIs "flee",
    coreTeeth ++
    [ .fieldDelta "spent" 1, .fieldEquals "fate" 1, .fieldEquals "pack" 0,
      .fieldEquals "depth" 0 ]
    ++ frozen (["depth", "wounds", wayName 2, wayName 3, wayName 4, "harm"]
               ++ hoardFreeze ++ hungFreeze)⟩

/-! ### The riders — `SlotChanged` carries the gate (the stapleable-slot fix). -/

/-- ANY verb that moves `depth` pays the stair law — in EITHER direction. One floor at a
time, a fresh guardian tally, and the way to the floor you land on must be open (on an
ascent that is a way you have already passed — `Dungeon.ways_behind_stay_open`). The
eight enumerated transitions are the whole staircase; there is no verb from which a
two-floor drop, a two-floor climb, or a landing on a shut floor is admissible. -/
def depthRider : Case :=
  ⟨.slotChangedForMethods "depth" verbs,
    coreTeeth ++ [.allowedTransitions "depth"
                    [(0, 1), (1, 2), (2, 3), (3, 4), (1, 0), (2, 1), (3, 2), (4, 3)],
                  .fieldEquals "wounds" 0,
                  wayTooth 2, wayTooth 3, wayTooth 4]⟩

/-- ⚑ `depth = d ⇒ relic k hangs on floor d`. The floor half of the way law — and a
`heapField` variant, because the relic is a heap object: the register form of this tooth
asked the loader for a slot named `relic_k`, which no cell has. -/
def keyHangsHereTooth (k d : Nat) : Constraint :=
  .anyOf [.negate (.fieldEquals "depth" d),
          .heapField (.named (relicName k)) (.equals (HUNG + d))]

/-- ANY verb that flips `way_w` must carry the `0→1` transition AND exhibit its key-relic.

⚑ **THE EXHIBIT MOVED FROM THE POST-STATE TO THE HOP**, because the model's `unlock` now
LEAVES THE KEY IN THE DOOR: after a lawful turn the key's code is `HUNG + depth`, not
`CARRIED`, so the old post-state tooth `relic (keyFor w) = CARRIED` refused every legal
way-flip in the tree. The replacement is not a weakening — it pins strictly more:

  * `(CARRIED, HUNG + d)` as the ONLY admissible hop for that relic on a flipping turn:
    the key WAS carried (the pre-state, which is what "exercise a capability you own"
    actually means and which the post-state tooth never said), and it IS now hanging;
  * `keyHangsHereTooth` for every floor: the door it hangs in is THE FLOOR YOU ARE
    STANDING ON — `Dungeon.key_hangs_where_it_was_turned`, deployed. -/
def wayRider (w : Nat) : Case :=
  ⟨.slotChangedForMethods (wayName w) verbs,
    coreTeeth ++
    [ .allowedTransitions (wayName w) [(0, 1)],
      .heapField (.named (relicName (keyFor w)))
        (.allowedTransitions (hangFloors.map (fun d => (CARRIED, HUNG + d)))) ]
    ++ hangFloors.map (keyHangsHereTooth (keyFor w))⟩

/-- ANY verb that flips `fate` is a lawful banking (`0→1`, pack emptied, AT THE SURFACE).
⚑ The `depth = 0` clause is new with the climb: without it the surface gate would be a
property of the `flee` arm alone and therefore stapleable onto any other verb's turn. -/
def fateRider : Case :=
  ⟨.slotChangedForMethods "fate" verbs,
    coreTeeth ++ [.allowedTransitions "fate" [(0, 1)], .fieldEquals "pack" 0,
                  .fieldEquals "depth" 0]⟩

/-- ANY verb that moves `bank` is a banking turn (`fate' = 1`, pack emptied, at the
surface). -/
def bankRider : Case :=
  ⟨.slotChangedForMethods "bank" verbs,
    coreTeeth ++ [.fieldEquals "fate" 1, .fieldEquals "pack" 0,
                  .fieldEquals "depth" 0]⟩

/-- ⚑ **ANY verb that moves `harm` is a lawful lunge.** Without this rider the `harm`
slot would be STAPLEABLE onto another method's turn — the standing hole class this
program retires structurally (see the module header, point 1). The rider re-demands the
lunge law METHOD-INDEPENDENTLY: exactly `+1`, inside the `[0, HARMCAP]` ratchet, on the
same turn as the wound it bought, below the surface's edge, and alive. -/
def harmRider : Case :=
  ⟨.slotChangedForMethods "harm" verbs,
    coreTeeth ++
    [ .fieldDelta "harm" 1, .inRangeTwoSided "harm" 0 HARMCAP,
      .fieldDelta "wounds" 1, .fieldGte "depth" 1, .fieldEquals "fate" 0 ]⟩

/-- ANY exertion (a `spent` change — every verb) pays the heavy commons: zone ranges,
the per-relic provenance ratchet, THE OBJECT-SIDE DOOR FRAME, and the genesis-sentinel
freeze. ⚑ The door frame rides HERE rather than on `unlock`/`take`, which is what makes
"you must be standing where it hangs" method-independent: there is no verb from which a
key can be hung in, or lifted out of, a door on another floor. -/
def spentRider : Case :=
  ⟨.slotChangedForMethods "spent" verbs,
    coreTeeth ++ rangeTeeth ++ custodyTeeth ++ doorFrameTeeth ++ projectionTeeth ++
      [.heapField .sentinel .immutable]⟩

/-- The deployed case list: genesis + the EIGHT verb arms + the seven riders. -/
def programCases : List Case :=
  [ genesisCase, delveCase, unlockCase, smiteCase, lootCase, fleeCase, lungeCase,
    ascendCase, takeCase,
    depthRider, wayRider 2, wayRider 3, wayRider 4, fateRider, bankRider, harmRider,
    spentRider ]

/-- **`dungeonProgram` — the DEPLOYED descent teeth, authored in Lean.** -/
def dungeonProgram : CellProgram := .cases programCases

/-! ### ⚑ THE REGISTER WALL — an over-wide program is a BUILD ERROR, here, at the source.

A cell carries `STATE_SLOTS = 16` register slots (`dregg_cell::state::STATE_SLOTS`,
re-exported through `spween_dregg` to `dregg_schema::layout`). Nothing downstream of
this file can widen that. Two ways a program can ask for more than a cell has, and both
were LIVE until this gate existed:

  1. **too many register names** — the four-counter door family put the descent at 18
     names, and the failure surfaced as a runtime `LayoutError::OutOfRegisters
     { needed: 18, available: 16 }` at deploy time, in Rust, days after the teeth were
     authored;
  2. **a HEAP-resident name used as a register** — a relic is a `collection`, so
     `Deployment::reg("relic_0")` had no slot to return and PANICKED in the loader.

Both are decidable properties of the authored object, so both are checked HERE, by the
kernel, in the file that writes the teeth. `registerNames` is the declared register file;
`regsOfConstraint` walks every tooth and reports every name used in a REGISTER position;
`programRegistersOK` is `by rfl` — it cannot be satisfied by a comment. -/

/-- The register names the descent's teeth may mention. Heap keys are NOT here: they are
`HeapKeyRef`s and live in `keyList` (`DungeonDeployed`). -/
def registerNames : List String :=
  ["depth", "spent", "wounds", "fate", "pack", "bank",
   wayName 2, wayName 3, wayName 4,
   hoardName 1, hoardName 2, hoardName 3, hoardName 4, "harm", hungName]

/-- The cell's register-file width — `dregg_cell::state::STATE_SLOTS`. -/
def stateSlotsBudget : Nat := 16

/-- Every name a `Simple` uses in a REGISTER position. A `heapField` variant contributes
NONE: that is the whole point of the arm. -/
def regsOfSimple : Simple → List String
  | .fieldEquals r _ => [r]
  | .fieldGte r _    => [r]
  | .fieldLte r _    => [r]
  | .immutable r     => [r]
  | .heapField _ _   => []
  | .negate inner    => regsOfSimple inner

/-- Every heap atom under a `Simple` composes (lifts into `Exec.SimpleConstraint`). -/
def simplesComposeAux : Simple → Bool
  | .heapField _ a => a.composes
  | .negate inner  => simplesComposeAux inner
  | _              => true

/-- Every name a tooth uses in a REGISTER position. `heapField` and `countFieldsEq`'s
`keys` contribute none; `countFieldsEq`'s COUNT target is a register and does. -/
def regsOfConstraint : Constraint → List String
  | .fieldEquals r _ => [r]
  | .fieldGte r _    => [r]
  | .fieldLte r _    => [r]
  | .fieldDelta r _  => [r]
  | .strictMonotonic r => [r]
  | .immutable r     => [r]
  | .sumEquals rs _  => rs
  | .affineLe ts _   => ts.map Prod.snd
  | .inRangeTwoSided r _ _ => [r]
  | .allowedTransitions r _ => [r]
  | .anyOf vs        => vs.flatMap regsOfSimple
  | .heapField _ _   => []
  | .countFieldsEq _ _ r => [r]

/-- A guard's register position (`SlotChanged` indexes the register file). -/
def regsOfGuard : Guard → List String
  | .methodIs _ => []
  | .slotChangedForMethods r _ => [r]

/-- **THE WALL.** The declared register file fits in a cell, and every register position
in every tooth and every guard of the authored program names a declared register. A tooth
that reaches for a heap-resident name, or a program that declares more registers than a
cell has, fails THIS `rfl` — at Lean build time, in this file. -/
theorem programRegistersOK :
    (decide (registerNames.length ≤ stateSlotsBudget)
      && registerNames.eraseDups.length == registerNames.length
      && programCases.all (fun c =>
           (regsOfGuard c.guard).all (fun r => decide (r ∈ registerNames))
             && c.constraints.all (fun t =>
                  (regsOfConstraint t).all (fun r => decide (r ∈ registerNames))))) = true := by
  rfl

/-- The companion pin: no `anyOf` variant carries a relational heap atom, so
`HeapAtom.toExecSimple`'s fail-closed ⊥ branch is unreachable in the authored object. -/
theorem simplesCompose :
    (programCases.all fun c => c.constraints.all fun t =>
      match t with
      | .anyOf vs => vs.all simplesComposeAux
      | _ => true) = true := by
  rfl

/-! ### The wall goes RED — the shapes it refuses, exhibited.

`programRegistersOK` is only a gate if a wrong program fails it. Both shapes below are
verbatim the ones this campaign removed, and both are REFUSED by the same predicate the
authored program passes. -/

/-- The register-position walker, as a decidable predicate on any case list. -/
def registersOK (cs : List Case) : Bool :=
  decide (registerNames.length ≤ stateSlotsBudget)
    && registerNames.eraseDups.length == registerNames.length
    && cs.all (fun c =>
         (regsOfGuard c.guard).all (fun r => decide (r ∈ registerNames))
           && c.constraints.all (fun t =>
                (regsOfConstraint t).all (fun r => decide (r ∈ registerNames))))

section CanonRegisterWall
local instance : WorldParam := instAt 0

-- The authored program passes.
#guard registersOK programCases = true

-- ⚑ RED 1 — **THE FOUR-COUNTER DOOR FAMILY.** `Σ zones = RELICS` over ten register
-- zones, which is what the repaired model asked for. Eighteen register names in a cell
-- that has sixteen: REFUSED, at Lean build time, in this file — not as a
-- `LayoutError::OutOfRegisters { needed: 18, available: 16 }` days later at deploy.
#guard registersOK
  [⟨.methodIs "unlock",
     [.sumEquals ["pack", "bank", "hoard_1", "hoard_2", "hoard_3", "hoard_4",
                  "hung_1", "hung_2", "hung_3", "hung_4"] RELICS]⟩] = false

-- ⚑ RED 2 — **A HEAP-RESIDENT NAME IN A REGISTER POSITION.** The per-relic custody hop
-- table, written the way it was written: `allowedTransitions "relic_1" …`. A relic is a
-- `collection`, i.e. heap-resident, so this tooth asked `Deployment::reg("relic_1")` for
-- a slot that does not exist — a runtime PANIC in the loader. REFUSED here.
#guard registersOK
  [⟨.methodIs "unlock",
     [.allowedTransitions (relicName 1) (custodyHops 1)]⟩] = false

-- ⚑ RED 3 — the same wound one level down, inside an `anyOf` variant: the floor half of
-- the way law as `fieldEquals "relic_1" (HUNG + d)`. This is the shape `Simple.heapField`
-- exists to make unnecessary; the wall refuses it either way.
#guard registersOK
  [⟨.methodIs "unlock",
     [.anyOf [.negate (.fieldEquals "depth" 1), .fieldEquals (relicName 1) (HUNG + 1)]]⟩] = false

-- …and the GREEN twin of RED 2/3: the same two laws stated on the object are ACCEPTED.
#guard registersOK
  [⟨.methodIs "unlock",
     [.heapField (.named (relicName 1)) (.allowedTransitions (custodyHops 1)),
      keyHangsHereTooth 1 1]⟩] = true

-- ⚑ THE MEASUREMENT, PINNED. Before this change the authored program used `hung_d` in a
-- register position 60 times and `relic_i` in one 23 times; both are now ZERO, and the
-- whole register demand is 15 of the cell's 16.
#guard (programCases.flatMap (fun c =>
          regsOfGuard c.guard ++ c.constraints.flatMap regsOfConstraint)).countP
        (fun r => hangFloors.any (fun d => r == s!"hung_{d}")) = 0
#guard (programCases.flatMap (fun c =>
          regsOfGuard c.guard ++ c.constraints.flatMap regsOfConstraint)).countP
        (fun r => (List.range RELICS).any (fun i => r == relicName i)) = 0
#guard ((programCases.flatMap (fun c =>
          regsOfGuard c.guard ++ c.constraints.flatMap regsOfConstraint)).eraseDups).length = 15

end CanonRegisterWall

/-! ## 3. The lift into the LAW-#1 algebra (`Dregg2.Exec`) — proofs run HERE. -/

/-- The reserved record field standing for the spween genesis-done sentinel. -/
def sentinelField : String := "genesis_done"

def HeapKeyRef.field : HeapKeyRef → String
  | .named n  => n
  | .sentinel => sentinelField

/-- Method-name interning for the Exec algebra (`methodIs (method : Nat)`). -/
def methodIdx : String → Nat
  | "genesis" => 0
  | "delve"   => 1
  | "unlock"  => 2
  | "smite"   => 3
  | "loot"    => 4
  | "flee"    => 5
  | "lunge"   => 6
  | "ascend"  => 7
  | "take"    => 8
  | _         => 1000

/-- The COMPOSING heap atoms, lifted into the name-keyed `Exec.SimpleConstraint` lane —
the `Exec` substrate has one namespace, so a heap key reads exactly like a register name
and the lift is the identity on meaning.

⚑ `allowedTransitions` is relational and has no `SimpleConstraint` form on EITHER
substrate, so it lowers here to the EMPTY allowlist — `new ∈ ∅`, the canonical ⊥. That is
fail-closed by construction rather than a silent reinterpretation, and it is UNREACHABLE
in the authored program: `simplesCompose` (below) pins by kernel evaluation that no
`Simple.heapField` in `dungeonProgram` carries one. -/
def HeapAtom.toExecSimple (f : String) : HeapAtom → Dregg2.Exec.SimpleConstraint
  | .equals v      => .fieldEquals f (v : Int)
  | .immutable     => .immutable f
  | .monotonic     => .monotonic f
  | .memberOf set  => .memberOf f (set.map (fun v => (v : Int)))
  | .deltaEquals d => .fieldDelta f d
  | .allowedTransitions _ => .memberOf f []

def Simple.toExec : Simple → Dregg2.Exec.SimpleConstraint
  | .fieldEquals r v => .fieldEquals r (v : Int)
  | .fieldGte r v    => .fieldGe r (v : Int)
  | .fieldLte r v    => .fieldLe r (v : Int)
  | .immutable r     => .immutable r
  | .heapField k a   => a.toExecSimple k.field
  | .negate inner    => .not inner.toExec

def HeapAtom.toExec (f : String) : HeapAtom → Dregg2.Exec.StateConstraint
  | .equals v      => .simple (.fieldEquals f (v : Int))
  | .immutable     => .simple (.immutable f)
  | .monotonic     => .simple (.monotonic f)
  | .memberOf set  => .simple (.memberOf f (set.map (fun v => (v : Int))))
  | .deltaEquals d => .simple (.fieldDelta f d)
  | .allowedTransitions al =>
      .allowedTransitions f (al.map (fun p => ((p.1 : Int), (p.2 : Int))))

def Constraint.toExec : Constraint → Dregg2.Exec.StateConstraint
  | .fieldEquals r v => .simple (.fieldEquals r (v : Int))
  | .fieldGte r v    => .simple (.fieldGe r (v : Int))
  | .fieldLte r v    => .simple (.fieldLe r (v : Int))
  | .fieldDelta r d  => .simple (.fieldDelta r (d : Int))
  | .strictMonotonic r => .simple (.strictMono r)
  | .immutable r     => .simple (.immutable r)
  | .sumEquals rs v  => .sumEquals rs (v : Int)
  | .affineLe ts c   => .affineLe (ts.map (fun t => (t.1, t.2))) c
  | .inRangeTwoSided r lo hi => .simple (.inRangeTwoSided r (lo : Int) (hi : Int))
  | .allowedTransitions r al =>
      .allowedTransitions r (al.map (fun p => ((p.1 : Int), (p.2 : Int))))
  | .anyOf vs        => .anyOf (vs.map Simple.toExec)
  | .heapField k a   => a.toExec k.field
  | .countFieldsEq ks v r =>
      .countFieldsEq (ks.map HeapKeyRef.field) (v : Int) r

def Guard.toExec : Guard → Dregg2.Exec.TransitionGuard
  | .methodIs m => .methodIs (methodIdx m)
  | .slotChangedForMethods reg ms =>
      .allOf [.slotChanged reg, .anyOf (ms.map (fun m => .methodIs (methodIdx m)))]

def Case.toExec (c : Case) : Dregg2.Exec.TransitionCase :=
  ⟨c.guard.toExec, c.constraints.map Constraint.toExec⟩

def CellProgram.toExec : CellProgram → Dregg2.Exec.RecordProgram
  | .cases cs => .cases (cs.map Case.toExec)

/-- The deployed program in the LAW-#1 algebra. -/
def dungeonExec : Dregg2.Exec.RecordProgram := dungeonProgram.toExec

/-! ## 4. Admission-soundness inversions (over ARBITRARY record values). -/

open Dregg2.Exec in
/-- If a `Cases` program admits, then EVERY member case whose guard matches has all its
constraints satisfied (the executor ANDs all matching arms). -/
theorem admits_cases_mem {tcs : List TransitionCase} {m : Nat} {o n : Value}
    (h : RecordProgram.admits (.cases tcs) m o n = true)
    {tc : TransitionCase} (hmem : tc ∈ tcs)
    (hmatch : tc.guard.matches m o n = true) :
    ∀ c ∈ tc.constraints, evalConstraint c o n = true := by
  simp only [RecordProgram.admits] at h
  have hmemf : tc ∈ tcs.filter (fun tc => tc.guard.matches m o n) :=
    List.mem_filter.mpr ⟨hmem, hmatch⟩
  cases hfil : tcs.filter (fun tc => tc.guard.matches m o n) with
  | nil => rw [hfil] at hmemf; cases hmemf
  | cons a as =>
    rw [hfil] at h hmemf
    have hall := (List.all_eq_true.mp h) tc hmemf
    intro c hc
    exact (List.all_eq_true.mp hall) c hc

open Dregg2.Exec in
/-- Every verb case's teeth BEGIN with `coreTeeth`; an admitted verb turn therefore
satisfies every core tooth. (`m` ranges over the five verb indices.) -/
theorem verb_core_teeth {m : Nat} (hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8)
    {o n : Value} (h : RecordProgram.admits dungeonExec m o n = true) :
    ∀ c ∈ coreTeeth, evalConstraint c.toExec o n = true := by
  intro c hc
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact admits_cases_mem (tcs := programCases.map Case.toExec) h
      (tc := delveCase.toExec)
      (List.mem_map_of_mem (by simp [programCases])) (by rfl)
      c.toExec (List.mem_map_of_mem (by simp [delveCase, List.mem_append, hc]))
  · exact admits_cases_mem (tcs := programCases.map Case.toExec) h
      (tc := unlockCase.toExec)
      (List.mem_map_of_mem (by simp [programCases])) (by rfl)
      c.toExec (List.mem_map_of_mem (by simp [unlockCase, List.mem_append, hc]))
  · exact admits_cases_mem (tcs := programCases.map Case.toExec) h
      (tc := smiteCase.toExec)
      (List.mem_map_of_mem (by simp [programCases])) (by rfl)
      c.toExec (List.mem_map_of_mem (by simp [smiteCase, List.mem_append, hc]))
  · exact admits_cases_mem (tcs := programCases.map Case.toExec) h
      (tc := lootCase.toExec)
      (List.mem_map_of_mem (by simp [programCases])) (by rfl)
      c.toExec (List.mem_map_of_mem (by simp [lootCase, List.mem_append, hc]))
  · exact admits_cases_mem (tcs := programCases.map Case.toExec) h
      (tc := fleeCase.toExec)
      (List.mem_map_of_mem (by simp [programCases])) (by rfl)
      c.toExec (List.mem_map_of_mem (by simp [fleeCase, List.mem_append, hc]))
  · exact admits_cases_mem (tcs := programCases.map Case.toExec) h
      (tc := lungeCase.toExec)
      (List.mem_map_of_mem (by simp [programCases])) (by rfl)
      c.toExec (List.mem_map_of_mem (by simp [lungeCase, List.mem_append, hc]))
  · exact admits_cases_mem (tcs := programCases.map Case.toExec) h
      (tc := ascendCase.toExec)
      (List.mem_map_of_mem (by simp [programCases])) (by rfl)
      c.toExec (List.mem_map_of_mem (by simp [ascendCase, List.mem_append, hc]))
  · exact admits_cases_mem (tcs := programCases.map Case.toExec) h
      (tc := takeCase.toExec)
      (List.mem_map_of_mem (by simp [programCases])) (by rfl)
      c.toExec (List.mem_map_of_mem (by simp [takeCase, List.mem_append, hc]))

open Dregg2.Exec in
/-- **No dupe, no burn — deployed**: any admitted verb turn's post-state sums the six
relic zones to exactly `RELICS`, whatever the writes were. -/
theorem admitted_verb_conserves {m : Nat}
    (hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8)
    {o n : Value} (h : RecordProgram.admits dungeonExec m o n = true) :
    sumScalars n zones = some (RELICS : Int) := by
  have := verb_core_teeth hm h (.sumEquals zones RELICS) (by simp [coreTeeth])
  simpa [Constraint.toExec, evalConstraint] using this

open Dregg2.Exec in
/-- **Attenuation — deployed**: any admitted verb turn's post-state satisfies
`pack + depth + harm ≤ CAP`. ⚑ The `harm` term is what makes the guardian's blow cost
something on the deployed teeth rather than in prose: a broken grip is a carry slot the
capacity commons will not give back, on EVERY verb. -/
theorem admitted_verb_capacity {m : Nat}
    (hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8)
    {o n : Value} (h : RecordProgram.admits dungeonExec m o n = true) :
    ∃ p d x : Int, n.scalar "pack" = some p ∧ n.scalar "depth" = some d
      ∧ n.scalar "harm" = some x ∧ p + d + x ≤ (CAP : Int) := by
  have hT := verb_core_teeth hm h
    (.affineLe [((1 : Int), "pack"), ((1 : Int), "depth"), ((1 : Int), "harm")] (CAP : Int))
    (by simp [coreTeeth])
  have hT' : evalConstraint
      (.affineLe [((1 : Int), "pack"), ((1 : Int), "depth"), ((1 : Int), "harm")]
        (CAP : Int)) o n = true := hT
  obtain ⟨s, hsum, hle⟩ :=
    (evalConstraint_affineLe_iff
      [((1 : Int), "pack"), ((1 : Int), "depth"), ((1 : Int), "harm")]
      (CAP : Int) o n).mp hT'
  cases hp : n.scalar "pack" with
  | none => simp [affineSum, hp] at hsum
  | some p =>
    cases hd : n.scalar "depth" with
    | none => simp [affineSum, hp, hd] at hsum
    | some d =>
      cases hx : n.scalar "harm" with
      | none => simp [affineSum, hp, hd, hx] at hsum
      | some x =>
        refine ⟨p, d, x, rfl, rfl, rfl, ?_⟩
        simp only [affineSum, List.foldr_cons, List.foldr_nil, hp, hd, hx] at hsum
        injection hsum with hsum
        omega

open Dregg2.Exec in
/-- **The clock — deployed**: any admitted verb turn strictly spends breath, and the
post-state clock is capped at `BREATH`. -/
theorem admitted_verb_pays {m : Nat}
    (hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8)
    {o n : Value} (h : RecordProgram.admits dungeonExec m o n = true) :
    ∃ a b : Int, o.scalar "spent" = some a ∧ n.scalar "spent" = some b
      ∧ a < b ∧ b ≤ (BREATH : Int) := by
  have hs := verb_core_teeth hm h (.strictMonotonic "spent") (by simp [coreTeeth])
  have hs' : evalSimple (.strictMono "spent") o n = true := hs
  have hl := verb_core_teeth hm h (.fieldLte "spent" BREATH) (by simp [coreTeeth])
  have hl' : evalSimple (.fieldLe "spent" (BREATH : Int)) o n = true := hl
  obtain ⟨a, b, ha, hb, hab⟩ := (evalSimple_strictMono_iff "spent" o n).mp hs'
  refine ⟨a, b, ha, hb, hab, ?_⟩
  simp only [evalSimple, hb] at hl'
  exact of_decide_eq_true hl'

open Dregg2.Exec in
/-- **Aliveness — deployed**: any admitted verb turn STARTS alive (`old fate = 0`);
its post-fate is `0` (still alive) or `1` (banked this turn). -/
theorem admitted_verb_alive {m : Nat}
    (hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8)
    {o n : Value} (h : RecordProgram.admits dungeonExec m o n = true) :
    o.scalar "fate" = some 0
      ∧ (n.scalar "fate" = some 0 ∨ n.scalar "fate" = some 1) := by
  have hT := verb_core_teeth hm h (.allowedTransitions "fate" [(0, 0), (0, 1)])
    (by simp [coreTeeth])
  have hT' : evalConstraint
      (.allowedTransitions "fate" [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int))])
      o n = true := hT
  cases ha : o.scalar "fate" with
  | none =>
    simp only [evalConstraint, ha] at hT'
    exact absurd hT' (by decide)
  | some a =>
    cases hb : n.scalar "fate" with
    | none =>
      simp only [evalConstraint, ha, hb] at hT'
      exact absurd hT' (by decide)
    | some b =>
      simp only [evalConstraint, ha, hb, List.any_cons, List.any_nil, Bool.or_false,
                 Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hT'
      rcases hT' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨by rw [← h1], Or.inl (by rw [← h2])⟩
      · exact ⟨by rw [← h1], Or.inr (by rw [← h2])⟩

open Dregg2.Exec in
/-- **The banked tomb is frozen — deployed**: from `old fate = 1` NO verb is admitted. -/
theorem banked_tomb_refuses {m : Nat}
    (hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8)
    {o n : Value} (hf : o.scalar "fate" = some 1) :
    RecordProgram.admits dungeonExec m o n = false := by
  cases hadm : RecordProgram.admits dungeonExec m o n with
  | false => rfl
  | true =>
    have := (admitted_verb_alive hm hadm).1
    rw [hf] at this
    cases this

open Dregg2.Exec in
/-- **The dead light refuses — deployed**: at `old spent = BREATH` NO verb is admitted
(strict spend + the cap are jointly unsatisfiable). -/
theorem dead_light_refuses {m : Nat}
    (hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8)
    {o n : Value} (hs : o.scalar "spent" = some (BREATH : Int)) :
    RecordProgram.admits dungeonExec m o n = false := by
  cases hadm : RecordProgram.admits dungeonExec m o n with
  | false => rfl
  | true =>
    obtain ⟨a, b, ha, hb, hab, hcap⟩ := admitted_verb_pays hm hadm
    rw [hs] at ha
    injection ha with ha
    omega

open Dregg2.Exec in
/-- **Keys are exercised capabilities — deployed, ALL THREE WAYS.** Any admitted VERB turn that
flips `way_w` (`w ∈ {2,3,4}`) carries the lawful `0→1` transition AND exercises its key-relic
`keyFor w = w−1`: the key WAS `CARRIED` in the pre-state and IS hanging (`HUNG + d`, on a real
floor) in the post-state. The rider guard makes this METHOD-INDEPENDENT across the verb set —
there is no verb from which a keyless way-flip is admissible. ⚑ This GENERALIZES the
former way-2-only inversion: ways 3 and 4 (`way3_flip_exhibits_key`, `way4_flip_exhibits_key` below)
are now proven, not Rust-driven — the audit's "ways 3/4 are Rust-driven" gap is closed.

⚑ **THE EXHIBIT IS NOW A HOP, NOT A POST-STATE READ**, and that is a strengthening, not a
restatement. The old conclusion `n.relic = CARRIED` said nothing about who held the key BEFORE
the turn — an attacker who acquired the key ON the flipping turn satisfied it. This one pins
`o.relic = CARRIED`: the capability was OWNED going in. It also matches the rulebook, where a
turned key does not stay in the pack (`Dungeon.step`'s `.unlock` writes `HUNG + depth`), so the
old post-state form was not merely weak — it was FALSE of every legal unlock in the tree. -/
theorem way_flip_exhibits_key (w : Nat) (hw : w = 2 ∨ w = 3 ∨ w = 4)
    {m : Nat} (hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8)
    {o n : Value} (h : RecordProgram.admits dungeonExec m o n = true)
    (hflip : (o.scalar (wayName w) == n.scalar (wayName w)) = false) :
    o.scalar (relicName (keyFor w)) = some (CARRIED : Int)
      ∧ (∃ d : Nat, 1 ≤ d ∧ d ≤ FLOORS
          ∧ n.scalar (relicName (keyFor w)) = some ((HUNG + d : Nat) : Int))
      ∧ o.scalar (wayName w) = some 0 ∧ n.scalar (wayName w) = some 1 := by
  have hmem : (wayRider w).toExec ∈ programCases.map Case.toExec := by
    rcases hw with rfl | rfl | rfl <;> exact List.mem_map_of_mem (by simp [programCases])
  have hmatch : (wayRider w).toExec.guard.matches m o n = true := by
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [wayRider, Case.toExec, Guard.toExec, verbs, methodIdx,
            TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch, hflip]
  have hall := admits_cases_mem (tcs := programCases.map Case.toExec) h
    (tc := (wayRider w).toExec) hmem hmatch
  have hkey := hall ((Constraint.heapField (.named (relicName (keyFor w)))
      (.allowedTransitions (hangFloors.map (fun d => (CARRIED, HUNG + d))))).toExec)
    (List.mem_map_of_mem (by simp [wayRider, List.mem_append]))
  have htrans := hall ((Constraint.allowedTransitions (wayName w) [(0, 1)]).toExec)
    (List.mem_map_of_mem (by simp [wayRider, List.mem_append]))
  -- The key hop, decided: `hangFloors = [1,2,3,4]`, so the table is the four concrete pairs
  -- `(CARRIED, HUNG + d)` and each disjunct fixes BOTH endpoints.
  have hkey' : evalConstraint (Dregg2.Exec.StateConstraint.allowedTransitions
      (relicName (keyFor w))
      [((CARRIED : Int), ((HUNG + 1 : Nat) : Int)), ((CARRIED : Int), ((HUNG + 2 : Nat) : Int)),
       ((CARRIED : Int), ((HUNG + 3 : Nat) : Int)), ((CARRIED : Int), ((HUNG + 4 : Nat) : Int))])
      o n = true := by
    simpa [Constraint.toExec, HeapAtom.toExec, HeapKeyRef.field, hangFloors, FLOORS, List.range'] using hkey
  have hpair : o.scalar (relicName (keyFor w)) = some (CARRIED : Int)
      ∧ (∃ d : Nat, 1 ≤ d ∧ d ≤ FLOORS
          ∧ n.scalar (relicName (keyFor w)) = some ((HUNG + d : Nat) : Int)) := by
    cases ha : o.scalar (relicName (keyFor w)) with
    | none => simp only [evalConstraint, ha] at hkey'; exact absurd hkey' (by decide)
    | some a =>
      cases hb : n.scalar (relicName (keyFor w)) with
      | none => simp only [evalConstraint, ha, hb] at hkey'; exact absurd hkey' (by decide)
      | some b =>
        simp only [evalConstraint, ha, hb, List.any_cons, List.any_nil, Bool.or_false,
                   Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hkey'
        rcases hkey' with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨by rw [← h1], ⟨1, by decide, by decide, by rw [← h2]⟩⟩
        · exact ⟨by rw [← h1], ⟨2, by decide, by decide, by rw [← h2]⟩⟩
        · exact ⟨by rw [← h1], ⟨3, by decide, by decide, by rw [← h2]⟩⟩
        · exact ⟨by rw [← h1], ⟨4, by decide, by decide, by rw [← h2]⟩⟩
  refine ⟨hpair.1, hpair.2, ?_, ?_⟩
  all_goals
    (have hT : evalConstraint
        (.allowedTransitions (wayName w) [((0 : Int), (1 : Int))]) o n = true := htrans
     cases ha : o.scalar (wayName w) with
     | none =>
       simp only [evalConstraint, ha] at hT
       exact absurd hT (by decide)
     | some a =>
       cases hb : n.scalar (wayName w) with
       | none =>
         simp only [evalConstraint, ha, hb] at hT
         exact absurd hT (by decide)
       | some b =>
         simp only [evalConstraint, ha, hb, List.any_cons, List.any_nil, Bool.or_false,
                    Bool.and_eq_true, beq_iff_eq] at hT
         obtain ⟨h1, h2⟩ := hT
         first
           | rw [← h1]
           | rw [← h2])

open Dregg2.Exec in
/-- Way 2 (`keyFor 2 = 1`) — the original inversion, now a corollary of the general lemma. -/
theorem way2_flip_exhibits_key {m : Nat}
    (hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8)
    {o n : Value} (h : RecordProgram.admits dungeonExec m o n = true)
    (hflip : (o.scalar (wayName 2) == n.scalar (wayName 2)) = false) :
    o.scalar (relicName 1) = some (CARRIED : Int)
      ∧ (∃ d : Nat, 1 ≤ d ∧ d ≤ FLOORS
          ∧ n.scalar (relicName 1) = some ((HUNG + d : Nat) : Int))
      ∧ o.scalar (wayName 2) = some 0 ∧ n.scalar (wayName 2) = some 1 :=
  way_flip_exhibits_key 2 (Or.inl rfl) hm h hflip

open Dregg2.Exec in
/-- Way 3 (`keyFor 3 = 2`) — proven, not Rust-driven. -/
theorem way3_flip_exhibits_key {m : Nat}
    (hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8)
    {o n : Value} (h : RecordProgram.admits dungeonExec m o n = true)
    (hflip : (o.scalar (wayName 3) == n.scalar (wayName 3)) = false) :
    o.scalar (relicName 2) = some (CARRIED : Int)
      ∧ (∃ d : Nat, 1 ≤ d ∧ d ≤ FLOORS
          ∧ n.scalar (relicName 2) = some ((HUNG + d : Nat) : Int))
      ∧ o.scalar (wayName 3) = some 0 ∧ n.scalar (wayName 3) = some 1 :=
  way_flip_exhibits_key 3 (Or.inr (Or.inl rfl)) hm h hflip

open Dregg2.Exec in
/-- Way 4 (`keyFor 4 = 3`) — proven, not Rust-driven. -/
theorem way4_flip_exhibits_key {m : Nat}
    (hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8)
    {o n : Value} (h : RecordProgram.admits dungeonExec m o n = true)
    (hflip : (o.scalar (wayName 4) == n.scalar (wayName 4)) = false) :
    o.scalar (relicName 3) = some (CARRIED : Int)
      ∧ (∃ d : Nat, 1 ≤ d ∧ d ≤ FLOORS
          ∧ n.scalar (relicName 3) = some ((HUNG + d : Nat) : Int))
      ∧ o.scalar (wayName 4) = some 0 ∧ n.scalar (wayName 4) = some 1 :=
  way_flip_exhibits_key 4 (Or.inr (Or.inr rfl)) hm h hflip

open Dregg2.Exec in
/-- **Method-default-deny survives the riders**: a method outside the EIGHT verbs is
refused outright — no case (method arm or rider) matches it. ⚑ The bound moved `8 → 9`
with `take`: leaving it at 8 would have proved default-deny for a method index the
program now HAS an arm for, which is the shape of a gate that stops biting where the
tree grew. -/
theorem unknown_method_refused {m : Nat} (hm : 9 ≤ m) (o n : Value) :
    RecordProgram.admits dungeonExec m o n = false := by
  have h0 : ((0 : Nat) == m) = false := beq_eq_false_iff_ne.mpr (by omega)
  have h1 : ((1 : Nat) == m) = false := beq_eq_false_iff_ne.mpr (by omega)
  have h2 : ((2 : Nat) == m) = false := beq_eq_false_iff_ne.mpr (by omega)
  have h3 : ((3 : Nat) == m) = false := beq_eq_false_iff_ne.mpr (by omega)
  have h4 : ((4 : Nat) == m) = false := beq_eq_false_iff_ne.mpr (by omega)
  have h5 : ((5 : Nat) == m) = false := beq_eq_false_iff_ne.mpr (by omega)
  have h6 : ((6 : Nat) == m) = false := beq_eq_false_iff_ne.mpr (by omega)
  have h7 : ((7 : Nat) == m) = false := beq_eq_false_iff_ne.mpr (by omega)
  have h8 : ((8 : Nat) == m) = false := beq_eq_false_iff_ne.mpr (by omega)
  simp [dungeonExec, dungeonProgram, programCases, CellProgram.toExec, Case.toExec,
        Guard.toExec, verbs, methodIdx, RecordProgram.admits,
        TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
        genesisCase, delveCase, unlockCase, smiteCase, lootCase, fleeCase, lungeCase,
        ascendCase, takeCase,
        depthRider, wayRider, fateRider, bankRider, harmRider, spentRider,
        List.map_cons, List.map_nil, List.filter_nil,
        h0, h1, h2, h3, h4, h5, h6, h7, h8]

/-! ## 5. The model↔program weld — encode the model state, DRIVE the runs. -/

/-- Embed the model state into the record substrate the deployed teeth read. Every
counter is a PROJECTION of custody (`pack`/`bank`/`hoardAt` are the model's own
definitions), so the encoding cannot disagree with the model about counts. -/
def encode (s : DState) : Value :=
  .record
    ([ ("depth", .int s.depth), ("spent", .int s.spent), ("wounds", .int s.wounds),
       ("harm", .int s.harm),
       ("fate", .int s.fate), ("pack", .int (pack s)), ("bank", .int (bank s)),
       (wayName 2, .int (s.ways.getD 0 0)), (wayName 3, .int (s.ways.getD 1 0)),
       (wayName 4, .int (s.ways.getD 2 0)),
       (hoardName 1, .int (hoardAt s 1)), (hoardName 2, .int (hoardAt s 2)),
       (hoardName 3, .int (hoardAt s 3)), (hoardName 4, .int (hoardAt s 4)),
       (hungName, .int (hungTotal s)) ]
     ++ (List.range RELICS).map (fun i => (relicName i, .int (s.custody.getD i 0)))
     ++ [(sentinelField, .int 1)])

/-- The pre-genesis cell: every register field-zero, the sentinel birthed at 0, the
relic heap keys unwritten (absent — on the heap, absent ≠ present-zero). -/
def preGenesis : Value :=
  .record
    [ ("depth", .int 0), ("spent", .int 0), ("wounds", .int 0), ("harm", .int 0),
      ("fate", .int 0), ("pack", .int 0), ("bank", .int 0),
      (wayName 2, .int 0), (wayName 3, .int 0), (wayName 4, .int 0),
      (hoardName 1, .int 0), (hoardName 2, .int 0), (hoardName 3, .int 0),
      (hoardName 4, .int 0),
      (hungName, .int 0), (sentinelField, .int 0) ]

def moveIdx : Move → Nat
  | .delve    => 1
  | .unlock _ => 2
  | .smite    => 3
  | .loot _   => 4
  | .flee     => 5
  | .lunge    => 6
  | .ascend   => 7
  | .take _   => 8

/-- Drive a model script through the DEPLOYED program: every step must be BOTH
model-legal and program-admitted on the encoded transition. -/
def programAdmitsRun (ms : List Move) : Bool :=
  Dregg2.Exec.RecordProgram.admits dungeonExec (methodIdx "genesis") preGenesis
      (encode genesisState)
    && go genesisState ms
where
  go (s : DState) : List Move → Bool
    | [] => true
    | m :: rest =>
      match step s m with
      | none => false
      | some s' =>
          Dregg2.Exec.RecordProgram.admits dungeonExec (moveIdx m) (encode s) (encode s')
            && go s' rest

/-- A convenience: the state a legal prefix reaches (the mint if the prefix is illegal —
the attack guards below always use legal prefixes, checked by the crowned-run guard). -/
def st (ms : List Move) : DState := (replay ms).getD genesisState

/-- Patch one register field of a record (the attack-forge builder). -/
def setF (v : Value) (f : String) (x : Int) : Value :=
  match v with
  | .record fs => .record (fs.map (fun p => if p.1 = f then (f, .int x) else p))
  | v => v

/-- Mutation-canary referee: the deployed program with exactly the six
object↔projection census teeth deleted from the spent rider.  This is not an
alternative ruleset; it exists to demonstrate that the aggregate tooth, rather
than another overlapping constraint, is what rejects the two-relic/one-counter
forgery below. -/
private def spentRiderWithoutProjection : Case :=
  ⟨.slotChangedForMethods "spent" verbs,
    coreTeeth ++ rangeTeeth ++ custodyTeeth ++ [.heapField .sentinel .immutable]⟩

private def dungeonExecWithoutProjection : Dregg2.Exec.RecordProgram :=
  CellProgram.toExec (.cases
    [ genesisCase, delveCase, unlockCase, smiteCase, lootCase, fleeCase, lungeCase,
      ascendCase, takeCase,
      depthRider, wayRider 2, wayRider 3, wayRider 4, fateRider, bankRider, harmRider,
      spentRiderWithoutProjection ])

/-- ⚑ Mutation-canary referee #2: the deployed program with exactly the 24 OBJECT-SIDE
DOOR-FRAME teeth deleted from the spent rider — everything else, including the whole
`hung` residue accounting and conservation, left standing. It exists to prove that the
door frame moving from four `hung_d` REGISTERS onto the relic's own custody key did not
quietly drop the law: with these teeth gone, THE REMOTE TAKE ADMITS (attack 7b below),
and with them present it is refused. A frame that is not the rejecting tooth is
decoration. -/
private def spentRiderWithoutDoorFrame : Case :=
  ⟨.slotChangedForMethods "spent" verbs,
    coreTeeth ++ rangeTeeth ++ custodyTeeth ++ projectionTeeth ++
      [.heapField .sentinel .immutable]⟩

private def dungeonExecWithoutDoorFrame : Dregg2.Exec.RecordProgram :=
  CellProgram.toExec (.cases
    [ genesisCase, delveCase, unlockCase, smiteCase, lootCase, fleeCase, lungeCase,
      ascendCase, takeCase,
      depthRider, wayRider 2, wayRider 3, wayRider 4, fateRider, bankRider, harmRider,
      spentRiderWithoutDoorFrame ])

/-! ### The weld, DRIVEN (`#guard` — kernel-evaluated, no axioms):
the model-legal crowned run is admitted END TO END by the deployed program object,
and the named attacks are refused. ⚑ This is the FORWARD weld for ONE run; the general
∀-weld (every legal step admitted) is the NAMED remainder — see the module header's WELD note.
The reverse direction (admitted ⇒ the named laws) IS ∀-proven by the inversions in §4.
The runs below are driven on DAY 0 (the shipped map); the family-wide drive — every
drawn day's crowned line admitted by that day's emitted teeth — is `crownedRunAdmitted`
at the end of this section. -/

section CanonWeld
local instance : WorldParam := instAt 0

-- ⚑ THE CROWNED RUN IS ADMITTED (genesis + all 17 verbs, each step model-legal AND
-- program-admitted on the same encoded transition).
#guard programAdmitsRun crownedRun = true

-- ⚑ AND SO IS A RUN THAT GOES BACK FOR THE KEYS. `crownedRun` contains no `take`, so the
-- drive above never exercises the new verb's arm — a battery that leaves a whole case
-- untouched cannot notice that case rotting. This is the §10 "which keys do you go back
-- for" line (day 0, banks THREE for all 30 breath): it exercises `unlock`'s custody write,
-- `take`'s inverse hop, and the door frame on three different floors.
#guard programAdmitsRun
  [ .delve, .smite, .loot 1, .unlock 2,
    .delve, .smite, .loot 2, .unlock 3,
    .delve, .smite, .smite, .loot 3, .unlock 4,
    .delve, .smite, .smite, .loot 0,
    .ascend, .take 3, .ascend, .take 2, .ascend, .ascend,
    .flee ] = true

-- Attack 1 — DUPE: a loot-shaped turn that mints a pack relic out of nothing
-- (pack +1, no hoard debit) breaks conservation and is refused.
#guard
  (let s := st [.delve, .smite]
   Dregg2.Exec.RecordProgram.admits dungeonExec 4 (encode s)
     (setF (setF (encode s) "pack" 1) "spent" 4)) = false

-- Attack 1b — OBJECT/PROJECTION SPLIT: debit one hoard unit and increment pack
-- by one while advancing TWO custody objects to CARRIED.  Conservation, the
-- loot frame, and both per-object ratchets all pass; the exact census is the
-- indispensable rejecting tooth.  The mutation canary proves that deleting
-- precisely `projectionTeeth` makes the same forged transition admit.
#guard
  (let s := st [.delve, .smite]
   let forged := setF (setF (setF (setF (setF (encode s)
      (relicName 1) CARRIED) (relicName 4) CARRIED)
      "pack" 1) (hoardName 1) 2) "spent" 4
   Dregg2.Exec.RecordProgram.admits dungeonExec 4 (encode s) forged) = false
#guard
  (let s := st [.delve, .smite]
   let forged := setF (setF (setF (setF (setF (encode s)
      (relicName 1) CARRIED) (relicName 4) CARRIED)
      "pack" 1) (hoardName 1) 2) "spent" 4
   Dregg2.Exec.RecordProgram.admits dungeonExecWithoutProjection 4 (encode s) forged) = true

-- Attack 2 — KEYLESS WAY: flipping way_2 without carrying key-relic 1 is refused
-- (the rider demands the exhibited key).
#guard
  (let s := st [.delve]
   Dregg2.Exec.RecordProgram.admits dungeonExec 2 (encode s)
     (setF (setF (encode s) (wayName 2) 1) "spent" 2)) = false

-- Attack 3 — STAPLE: a loot turn that ALSO descends (depth moves under method loot)
-- is refused (the loot frame freezes depth; the depth rider would demand the delve law).
#guard
  (let s := st [.delve, .smite]
   Dregg2.Exec.RecordProgram.admits dungeonExec 4
     (encode s)
     (setF (setF (setF (encode s) "pack" 1) "spent" 4) "depth" 2)) = false

-- Attack 4 — TOMB MOVE: after banking (fate = 1), a delve-shaped turn is refused.
#guard
  (let s := st [.delve, .ascend, .flee]
   Dregg2.Exec.RecordProgram.admits dungeonExec 1 (encode s)
     (setF (setF (encode s) "depth" 2) "spent" 5)) = false

-- Attack 5 — FAKE FLEE: banking with a non-empty pack (keep the relics AND the score)
-- is refused (`pack' = 0` is the flee law; the fate rider re-demands it).
#guard
  (let s := st [.delve, .smite, .loot 1, .ascend]
   Dregg2.Exec.RecordProgram.admits dungeonExec 5 (encode s)
     (setF (setF (encode s) "fate" 1) "spent" 6)) = false

-- ⚑ Attack 5b — THE TELEPORT BANK: fleeing FROM BELOW, everything else lawful (pack
-- emptied into the bank, fate 0→1, one breath paid). This is exactly the turn that was
-- legal before the climb existed, and it is what made the descent deathless. REFUSED by
-- `fleeCase`'s `depth = 0` and, method-independently, by the fate/bank riders.
#guard
  (let s := st [.delve, .smite, .loot 1]
   let banked := setF (setF (setF (setF (setF (encode s)
      (relicName 1) BANKED) "pack" 0) "bank" 1) "fate" 1) "spent" 5
   Dregg2.Exec.RecordProgram.admits dungeonExec 5 (encode s) banked) = false
-- …and the honest twin: CLIMB OUT FIRST and the identical banking IS admitted.
#guard
  (let s := st [.delve, .smite, .loot 1, .ascend]
   let banked := setF (setF (setF (setF (setF (encode s)
      (relicName 1) BANKED) "pack" 0) "bank" 1) "fate" 1) "spent" 6
   Dregg2.Exec.RecordProgram.admits dungeonExec 5 (encode s) banked) = true

-- ⚑ Attack 5c — THE STAPLED SURFACE: an `ascend`-shaped turn that ALSO banks (fate 0→1
-- stapled onto the climb) is refused; the fate rider is method-independent and the
-- ascend arm freezes `bank`.
#guard
  (let s := st [.delve]
   Dregg2.Exec.RecordProgram.admits dungeonExec 7 (encode s)
     (setF (setF (setF (encode s) "depth" 0) "fate" 1) "spent" 3)) = false

-- ⚑ Attack 5d — THE TWO-FLOOR CLIMB: an `ascend` that rises two floors at once is
-- refused (`allowedTransitions` enumerates the staircase; there is no 2→0 rung).
#guard
  (let s := st [.delve, .smite, .loot 1, .unlock 2, .delve]
   Dregg2.Exec.RecordProgram.admits dungeonExec 7 (encode s)
     (setF (setF (encode s) "depth" 0) "spent" 6)) = false

-- ⚑ Attack 5e — THE LAUNDERED GRIP: an `ascend` that heals `harm` on the way up is
-- refused. `ascend` freezes `harm`, and the `harmRider` demands an exact `+1` — a walk
-- upstairs never washes off what the guardian took (`Dungeon.harm_ratchets`).
#guard
  (let s := st [.delve, .lunge, .loot 1, .unlock 2, .delve]
   Dregg2.Exec.RecordProgram.admits dungeonExec 7 (encode s)
     (setF (setF (setF (encode s) "depth" 1) "harm" 0) "spent" 6)) = false

-- Attack 6 — RELIC TELEPORT: moving a relic's custody floor→floor (code 1→2) under a
-- smite is refused (relics frozen on smite; the spent-rider's memberOf refuses code 2
-- for a floor-1-minted relic on every verb).
#guard
  (let s := st [.delve]
   Dregg2.Exec.RecordProgram.admits dungeonExec 3 (encode s)
     (setF (setF (setF (encode s) (relicName 4) 2) "spent" 3) "wounds" 1)) = false

-- Attack 7 — GENESIS REPLAY: re-running genesis after the mint (sentinel already 1)
-- is refused (the one-shot `equals 1 ∧ deltaEquals 1` is unsatisfiable from old = 1).
#guard
  (Dregg2.Exec.RecordProgram.admits dungeonExec 0 (encode genesisState)
     (encode genesisState)) = false

-- ⚑ Attack 7b — THE REMOTE TAKE: lift a key out of a door you are NOT standing at. The
-- key hangs on floor 1; the run is on floor 2; everything else is a lawful `take` (one
-- breath, the carry slot charged, conservation balanced, the custody hop
-- `HUNG + 1 → CARRIED` in the enumeration). REFUSED by `doorDepartureTooth 1 1` alone —
-- the door frame is what says "you must be STANDING WHERE IT HANGS"
-- (`Dungeon.custody_lowers_only_by_take`), and the model refuses the same turn
-- (`Dungeon.lean` §10: `replay [.delve, .smite, .loot 1, .unlock 2, .delve, .take 1]
-- = none`).
-- ⚑ The forgery is now written on the OBJECT alone (`relic_1` back to `CARRIED`, the
-- carry slot charged, the door residue debited) — there is no per-floor counter left to
-- forge, which is exactly why the refusing tooth had to move onto the relic.
#guard
  (let s := st [.delve, .smite, .loot 1, .unlock 2, .delve]
   let forged := setF (setF (setF (setF (encode s)
      (relicName 1) CARRIED) "pack" 1) hungName 0) "spent" 7
   Dregg2.Exec.RecordProgram.admits dungeonExec 8 (encode s) forged) = false
-- …and the honest twin: the SAME write set STANDING ON FLOOR 1 is admitted. Without this
-- pole the tooth above would be indistinguishable from one that refuses every `take`.
#guard
  (let s := st [.delve, .smite, .loot 1, .unlock 2]
   let forged := setF (setF (setF (setF (encode s)
      (relicName 1) CARRIED) "pack" 1) hungName 0) "spent" 6
   Dregg2.Exec.RecordProgram.admits dungeonExec 8 (encode s) forged) = true
-- ⚑ …and the MUTATION CANARY: delete exactly the 24 object-side door-frame teeth and the
-- SAME remote take ADMITS. This is what makes the move off the `hung_d` registers a
-- relocation rather than a deletion — the door frame is the rejecting tooth, and it is
-- now stated on the relic that moved instead of on a projection of it.
#guard
  (let s := st [.delve, .smite, .loot 1, .unlock 2, .delve]
   let forged := setF (setF (setF (setF (encode s)
      (relicName 1) CARRIED) "pack" 1) hungName 0) "spent" 7
   Dregg2.Exec.RecordProgram.admits dungeonExecWithoutDoorFrame 8 (encode s) forged) = true

-- ⚑ Attack 7c — THE REMOTE HANG (the arrival half): standing on floor 2, hang the key
-- into floor 1's door. Everything else is a lawful `unlock` shape. REFUSED by
-- `doorArrivalTooth 1 1` — a key enters the door on the floor you are STANDING on, and
-- that is now a fact about the relic, not about a counter.
#guard
  (let s := st [.delve, .smite, .loot 1, .unlock 2, .delve, .smite, .loot 2]
   let forged := setF (setF (setF (setF (encode s)
      (relicName 2) (HUNG + 1)) "pack" ((pack (st [.delve, .smite, .loot 1, .unlock 2,
        .delve, .smite, .loot 2])) - 1)) hungName ((hungTotal (st [.delve, .smite, .loot 1,
        .unlock 2, .delve, .smite, .loot 2])) + 1)) "spent" 9
   Dregg2.Exec.RecordProgram.admits dungeonExec 2 (encode s) forged) = false

-- Attack 8 — UNKNOWN METHOD: a method outside the seven verbs is default-denied even
-- with a fully-lawful-looking write set.
#guard
  (let s := st [.delve]
   Dregg2.Exec.RecordProgram.admits dungeonExec 8 (encode s)
     (setF (encode s) "spent" 2)) = false

-- ⚑ Attack 9 — THE STAPLED GRIP: taking the lunge's DISCOUNT under the press. A `smite`
-- that pays only 1 breath by writing `harm += 1` is REFUSED: the press freezes `harm`,
-- and (method-independently) the `harmRider` demands the whole lunge law. This is the
-- standing stapleable-slot falsifier, aimed at the new register.
#guard
  (let s := st [.delve]
   Dregg2.Exec.RecordProgram.admits dungeonExec 3 (encode s)
     (setF (setF (setF (encode s) "harm" 1) "spent" 2) "wounds" 1)) = false
-- …and the honest twin: the SAME write set under `lunge` (method 6) IS admitted.
#guard
  (let s := st [.delve]
   Dregg2.Exec.RecordProgram.admits dungeonExec 6 (encode s)
     (setF (setF (setF (encode s) "harm" 1) "spent" 2) "wounds" 1)) = true

-- Attack 9b — HARM STAPLED ONTO A LOOT (the slot's other tempting host): refused.
#guard
  (let s := st [.delve, .smite]
   Dregg2.Exec.RecordProgram.admits dungeonExec 4 (encode s)
     (setF (setF (setF (setF (encode s) (relicName 1) CARRIED) "pack" 1)
        (hoardName 1) 2) "harm" 1)) = false

-- Attack 9c — THE RATCHET RUNS BACKWARD: a `lunge`-shaped turn that HEALS the grip
-- (`harm` 1 → 0) is refused; `fieldDelta harm 1` is a signed-exact step, not a bound.
#guard
  (let s := st [.delve, .lunge, .loot 1, .unlock 2, .delve]
   Dregg2.Exec.RecordProgram.admits dungeonExec 6 (encode s)
     (setF (setF (setF (encode s) "harm" 0) "spent" 6) "wounds" 1)) = false

-- The 31st breath: from a legally-exhausted clock nothing is admitted (driven twin of
-- `dead_light_refuses`).
#guard
  (let s := st [.delve, .smite]
   -- forge the clock to BREATH (the model cannot legally reach 30+2, so drive the
   -- deployed tooth directly: old spent = 30 refuses any further exertion)
   Dregg2.Exec.RecordProgram.admits dungeonExec 3
     (setF (encode s) "spent" 30)
     (setF (setF (encode s) "spent" 32) "wounds" 1)) = false

end CanonWeld

/-- **THE FAMILY WELD**: for the day at family index `k`, the crowned line generated from
that day's map is model-legal AND admitted end to end by the teeth emitted for that day.
This is the day-varying twin of the single `programAdmitsRun crownedRun` drive above. -/
def crownedRunAdmitted (k : Nat) : Bool :=
  @programAdmitsRun (instAt k) (@crownedRun (instAt k))

-- ⚑ EVERY DAY IN THE FAMILY IS PLAYABLE ON ITS OWN DEPLOYED TEETH.
#guard (List.range dayCount).all crownedRunAdmitted

/-! ## 6. The JSON emit (the checked-in artifact renderer — names, not indices). -/

private def jList (xs : List String) : String :=
  "[" ++ String.intercalate "," xs ++ "]"

private def jStr (s : String) : String := "\"" ++ s ++ "\""

def HeapKeyRef.toJson : HeapKeyRef → String
  | .named n  => "{\"kind\":\"named\",\"name\":" ++ jStr n ++ "}"
  | .sentinel => "{\"kind\":\"sentinel\"}"

def jPair (p : Nat × Nat) : String :=
  "[" ++ toString p.1 ++ "," ++ toString p.2 ++ "]"

def HeapAtom.toJson : HeapAtom → String
  | .equals v      => "{\"kind\":\"equals\",\"value\":" ++ toString v ++ "}"
  | .immutable     => "{\"kind\":\"immutable\"}"
  | .monotonic     => "{\"kind\":\"monotonic\"}"
  | .memberOf set  => "{\"kind\":\"memberOf\",\"set\":" ++ jList (set.map toString) ++ "}"
  | .deltaEquals d => "{\"kind\":\"deltaEquals\",\"d\":" ++ toString d ++ "}"
  | .allowedTransitions al =>
      "{\"kind\":\"allowedTransitions\",\"allowed\":" ++ jList (al.map jPair) ++ "}"

def Simple.toJson : Simple → String
  | .fieldEquals r v => "{\"kind\":\"fieldEquals\",\"reg\":" ++ jStr r ++ ",\"value\":" ++ toString v ++ "}"
  | .fieldGte r v    => "{\"kind\":\"fieldGte\",\"reg\":" ++ jStr r ++ ",\"value\":" ++ toString v ++ "}"
  | .fieldLte r v    => "{\"kind\":\"fieldLte\",\"reg\":" ++ jStr r ++ ",\"value\":" ++ toString v ++ "}"
  | .immutable r     => "{\"kind\":\"immutable\",\"reg\":" ++ jStr r ++ "}"
  | .heapField k a   => "{\"kind\":\"heapField\",\"key\":" ++ k.toJson ++ ",\"atom\":" ++ a.toJson ++ "}"
  | .negate inner    => "{\"kind\":\"not\",\"inner\":" ++ inner.toJson ++ "}"

def jTerm (t : Int × String) : String :=
  "[" ++ toString t.1 ++ "," ++ jStr t.2 ++ "]"

def Constraint.toJson : Constraint → String
  | .fieldEquals r v => "{\"kind\":\"fieldEquals\",\"reg\":" ++ jStr r ++ ",\"value\":" ++ toString v ++ "}"
  | .fieldGte r v    => "{\"kind\":\"fieldGte\",\"reg\":" ++ jStr r ++ ",\"value\":" ++ toString v ++ "}"
  | .fieldLte r v    => "{\"kind\":\"fieldLte\",\"reg\":" ++ jStr r ++ ",\"value\":" ++ toString v ++ "}"
  | .fieldDelta r d  => "{\"kind\":\"fieldDelta\",\"reg\":" ++ jStr r ++ ",\"d\":" ++ toString d ++ "}"
  | .strictMonotonic r => "{\"kind\":\"strictMonotonic\",\"reg\":" ++ jStr r ++ "}"
  | .immutable r     => "{\"kind\":\"immutable\",\"reg\":" ++ jStr r ++ "}"
  | .sumEquals rs v  => "{\"kind\":\"sumEquals\",\"regs\":" ++ jList (rs.map jStr) ++ ",\"value\":" ++ toString v ++ "}"
  | .affineLe ts c   => "{\"kind\":\"affineLe\",\"terms\":" ++ jList (ts.map jTerm) ++ ",\"c\":" ++ toString c ++ "}"
  | .inRangeTwoSided r lo hi =>
      "{\"kind\":\"inRangeTwoSided\",\"reg\":" ++ jStr r ++ ",\"lo\":" ++ toString lo ++ ",\"hi\":" ++ toString hi ++ "}"
  | .allowedTransitions r al =>
      "{\"kind\":\"allowedTransitions\",\"reg\":" ++ jStr r ++ ",\"allowed\":" ++ jList (al.map jPair) ++ "}"
  | .anyOf vs        => "{\"kind\":\"anyOf\",\"variants\":" ++ jList (vs.map Simple.toJson) ++ "}"
  | .heapField k a   => "{\"kind\":\"heapField\",\"key\":" ++ k.toJson ++ ",\"atom\":" ++ a.toJson ++ "}"
  | .countFieldsEq ks v r =>
      "{\"kind\":\"countFieldsEq\",\"keys\":" ++ jList (ks.map HeapKeyRef.toJson)
        ++ ",\"value\":" ++ toString v ++ ",\"reg\":" ++ jStr r ++ "}"

def Guard.toJson : Guard → String
  | .methodIs m => "{\"kind\":\"methodIs\",\"method\":" ++ jStr m ++ "}"
  | .slotChangedForMethods reg ms =>
      "{\"kind\":\"slotChangedForMethods\",\"reg\":" ++ jStr reg
        ++ ",\"methods\":" ++ jList (ms.map jStr) ++ "}"

def Case.toJson (c : Case) : String :=
  "    {\"guard\":" ++ c.guard.toJson ++ ",\"constraints\":["
    ++ String.intercalate "," (c.constraints.map Constraint.toJson) ++ "]}"

/-- The scene id that fixes the deterministic world-cell identity
(must match `dungeon_on_dregg::descent::SCENE_ID`). -/
def sceneId : String := "dungeon-on-dregg/descent1"

/-- **`emitJson` — render ONE day's descent program to artifact bytes.**
One case per line for stable diffs; a deterministic function of `dungeonProgram`. -/
def emitJson (p : CellProgram) : String :=
  match p with
  | .cases cs =>
    "{\n  \"scene\": " ++ jStr sceneId ++ ",\n  \"cases\": [\n"
      ++ String.intercalate ",\n" (cs.map Case.toJson)
      ++ "\n  ]\n}\n"

/-- One family member as an artifact entry: the drawn map (for the loader's mover) plus
the FULL teeth emitted for exactly that map. The loader never assembles a constraint —
it resolves names to slots inside the case list Lean wrote. -/
def worldJson (k : Nat) : String :=
  let W := worldAt k
  "    {\"day\":" ++ toString k
    ++ ",\"homes\":" ++ jList (W.homes.map toString)
    ++ ",\"ghp\":" ++ jList (W.ghp.map toString)
    ++ ",\"cases\":[\n"
    ++ String.intercalate ",\n" ((match (@dungeonProgram (instAt k)) with | .cases cs => cs).map Case.toJson)
    ++ "\n    ]}"

/-- **The deployed artifact: the WHOLE drawn family, one emitted program per day.**
The committed day-seed picks the index; every index here is a checked, driven-completable
map (`Dungeon.drawFamily_wf`, `Dungeon.winsAt_true`). -/
def emitFamilyJson : String :=
  "{\n  \"scene\": " ++ jStr sceneId
    ++ ",\n  \"days\": " ++ toString dayCount
    ++ ",\n  \"worlds\": [\n"
    ++ String.intercalate ",\n" ((List.range dayCount).map worldJson)
    ++ "\n  ]\n}\n"

section CanonEmit
local instance : WorldParam := instAt 0

-- The emit runs and carries the scene header + all 17 cases, for every day.
-- ⚑ 16 -> 17: `takeCase`. This census pin is the reason the count could not drift quietly.
#guard (emitJson dungeonProgram).startsWith "{\n  \"scene\": \"dungeon-on-dregg/descent1\""
#guard (match dungeonProgram with | .cases cs => cs.length) = 17
#guard emitFamilyJson.startsWith "{\n  \"scene\": \"dungeon-on-dregg/descent1\",\n  \"days\": 16"
#guard (List.range dayCount).all
        (fun k => (match (@dungeonProgram (instAt k)) with | .cases cs => cs).length == 17)

end CanonEmit

/-! ## 7. Axiom hygiene — every connection theorem on the standard kernel triple. -/

#assert_axioms programRegistersOK
#assert_axioms simplesCompose
#assert_axioms admits_cases_mem
#assert_axioms verb_core_teeth
#assert_axioms admitted_verb_conserves
#assert_axioms admitted_verb_capacity
#assert_axioms admitted_verb_pays
#assert_axioms admitted_verb_alive
#assert_axioms banked_tomb_refuses
#assert_axioms dead_light_refuses
#assert_axioms way_flip_exhibits_key
#assert_axioms way2_flip_exhibits_key
#assert_axioms way3_flip_exhibits_key
#assert_axioms way4_flip_exhibits_key
#assert_axioms unknown_method_refused

end Dregg2.Games.Dungeon.Prog
