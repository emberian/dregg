/-
# Vent Crawl — one more rung, or come up with what you carry

Substrate note: this is Lean-authored game semantics.  Nothing here is an AIR, a
constraint system or a gadget.  Rust and the browser dispatch the table
`VentCrawlEmit` renders out of this module; they carry no second copy of the
rules.

## The shape

Two verbs.  From the mouth of a vent shaft you either **crawl** one rung deeper —
the salvage on the next rung is worth more and the water is closer — or you
**bank**, climbing out with everything in the sling.  A rung that floods takes
the whole unbanked sling.  A session is about two minutes.

## The two hidden things, and why they are different

Push-your-luck dies the moment the arithmetic is flat: if the multiplier always
outruns the hazard the answer is always CRAWL, and if it never does the answer is
always BANK.  Either way there is no game, only a ritual.  What keeps the
arithmetic live here is that the reward is drawn and the risk is not.

* **The hazard is PUBLIC, and it escalates.**  Entering rung `d` floods when the
  crawler's own draw falls below `d - 1` out of `FACES = 8`.  That number is in
  the descriptor, in every emitted row, and on the client before the choice is
  made: 1/8 into rung 2, rising to 5/8 into rung 6.  A player who wants to know
  the odds of the next rung is told the odds of the next rung.  There is no
  hidden die feel, because the die is not hidden — only its result is.
* **The reward is HIDDEN and SHARED.**  Which of eight `Vein`s the shaft is
  running today is drawn once per slot from the curator's slot secret, and it is
  the same vein for every crawler in that slot.  A run reads it the only way
  there is: by going down and looking at what the rungs pay.

That split is what this game is for.  The risk you can price exactly; the prize
you have to pay risk to learn.

## Two hidden things in the reward, and the second one is never free

The eight veins are four SEAMS crossed with what the bottom does.  A seam —
`barren`, `patchy`, `layered`, `lode` — is what rungs 2 to 5 pay, and it is
readable: the carries separate the four seams at rung 3.  The BOTTOM is the
second bit, and no rung before the bottom pays differently for it: the shaft
either PINCHES (`barren`, `patchy`, `layered`, `fools-lode`) or opens into a
POCKET (`barren-pocket`, `patchy-pocket`, `layered-pocket`, `motherlode`).

⚑ So there is no state in this game with nothing left to learn.  A crawler who
has read the seam is standing in front of the last rung holding exactly one
undecided bit, and it is the bit that pays the most — `the_bottom_rung_is_a_coin_flip_on_every_seam`
says the two veins still standing at every deepest decision WANT OPPOSITE MOVES.
`fools-lode` is what that costs: five rungs indistinguishable from the
motherlode, and then the seam closes to one.

## What the shared table buys, socially

Because the vein is one draw for the whole slot, a banked total is EVIDENCE.
`carriedAt 3` separates the four seams (`the_day_is_read_in_two_instalments`), so
the first crew to bank out of rung 3 has told the whole ship what kind of day it
is.  Nobody had to be given a channel for that; it falls out of the shape.  What
that crew CANNOT tell them is the bottom: only a transcript that reached rung 6
carries that, so the last rung is the one piece of news the wardroom board has to
buy at full price.

⚠ Two residuals, named rather than smoothed over:

* **A drowned run is under-reported.**  Nothing compels a crawler to submit a
  flooded transcript.  The consolation payout — the map, `intel`, because you
  mapped the shaft even if the water took the sling — exists so that submitting a
  drowning is worth the carrying turn, but it is an incentive and not a
  guarantee, and the public record therefore skews upward.

  ⚑ The map is PRICED, and this is the fix for a real defect: a consolation that
  paid a full rung of `intel` per rung reached and subtracted nothing made
  drowning STRICTLY BETTER than banking for anyone who wanted the map, so the
  deepest crawl was a free roll and there was no wager in the game at all for
  that player.  A run that comes home keeps its whole map (`mapBanked d = d`); a
  run the water takes keeps half of it (`mapDrowned d = d / 2`).  Half is still
  worth the carrying turn at every reachable drowning
  (`a_drowned_run_is_always_worth_submitting`) and it is never worth more than
  climbing out from where you stood (`the_map_that_drowns_is_never_worth_more`),
  which is exactly the property "the loss is a loss" the design gate rebuilds
  from the emitted ladders.
* **The late crawler free-rides.**  Whoever banks out of rung 3 first paid two
  rungs of hazard for the information; whoever reads the wardroom board gets it
  for nothing.  That is a real asymmetry and the deepening that closes it is a
  per-crawler perturbation of the vein — see the parameters section.

## Per-player, per-slot, per-mission — and the sentinel

The two draws come from the same commitment and the same sponge:

* the **vein** from `daySeedFor`, which is `HiddenInstance.runSeedFor` under a
  fixed sentinel player key `DAY_TABLE_KEY`, so it depends on the slot secret,
  the slot and the mission and NOT on who is crawling;
* the **flood tape** from `mission.runSeed`, which admission pins to
  `HiddenInstance.runSeedFor` for THIS player, so two crawlers on one vein still
  drown on different rungs.

⚠ The sentinel is a CONVENTION, not a proof.  A crawler whose signing-key digest
equalled `DAY_TABLE_KEY` would draw the day's vein as their own flood tape and
could read the vein off it.  That is a 256-bit constant collision against a value
nobody chose adversarially, and `the_day_table_is_not_a_player_stream` exhibits
the separation on a fixture rather than asserting it in general.  The structural
fix — a distinct sponge domain — belongs in `HiddenInstance`, which is not this
module's to edit this cycle.

## Toy parameters, and what deepening looks like

Every number below is v1-SMALL ON PURPOSE.  The shape is what is being claimed;
the size is not.

| parameter        | v1 | what deepening buys |
| ---------------- | -- | ------------------- |
| `DEPTH_CAP`      | 6  | more rungs = a longer tail and a finer stopping curve; the hazard formula already extends, but `floodBelow 9 = 8 = FACES` is certain death, so past rung 8 the ladder needs a second face count |
| `FACES`          | 8  | a wider die makes the hazard curve smoother and the near-misses finer-grained; 8 is chosen because it divides 256, so `SeedDraw.drawBelow?` never rejects a byte (`draw_below_eight_never_rejects`, an instance of `a_full_ceiling_never_rejects`) |
| veins            | 8  | more veins = more bits to learn and a slower collapse to certainty.  Eight is four seams times what the bottom does, which is the smallest family that keeps SOME question open at EVERY decision — and, like `FACES`, 8 divides 256 so the vein draw never rejects either.  The next size that keeps that is 16 |
| yield tables     | authored | the first thing to make drawn rather than authored: a per-rung yield draw would stop `carried` from being a function of `(depth, vein)` and would decouple two crawlers on one vein |
| the mouth cache  | 2  | a bigger mouth cache raises the stake of the very first crawl |

**The deepening I would do first** is the per-crawler vein perturbation: give each
crawler a private ±1 on the deep rungs, drawn from their own seed.  It costs one
more draw off a stream that already has 26 bytes spare, it breaks the free-ride
above, and it stops `carried` from being a public function of `(depth, vein)`.

## Hard facts respected

`Poseidon2BabyBearW16.perm` reduces exponentially, and `HiddenInstance.commit`,
`runSeedFor` and `practiceRunSeed` are `@[irreducible]` because of it.  Nothing in
this file `decide`s or `rfl`s through `daySeedFor`; the fixture checks that mention
it are evaluated only under `native_decide`, in `VentCrawlFixtures.lean`.

`SeedDraw.drawBelow?` is the only draw used.  `SalvageCrate.unbiasedIndex?`
cannot stream — its `find?` then modulo re-reads the same byte — and nothing here
calls it.
-/
import Dregg2.Games.PathOfAngels.Core
import Dregg2.Games.PathOfAngels.SeedDraw
import Dregg2.Games.PathOfAngels.HiddenInstance
import Dregg2.Games.PathOfAngels.DayWater
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.VentCrawl

open Dregg2.Games.PathOfAngels

set_option autoImplicit false

/-! ## Parameters — all v1-small, see the table in the docblock -/

/-- The deepest rung.  A run starts at rung 1 and can reach rung `DEPTH_CAP`. -/
abbrev DEPTH_CAP : Nat := 6

/-- The hazard die.  8 divides 256, so `SeedDraw.drawBelow? FACES` never rejects
a byte and a 32-byte seed always yields the whole tape. -/
abbrev FACES : Nat := 8

/-- The plate at the mouth.  It is the same on every vein, so a run's opening
position carries no information about the day and rung 1 is not a draw. -/
abbrev MOUTH_SALVAGE : Nat := 2

/-! ## The hazard — public, escalating, and printed on the row

`floodBelow d` is how many of the `FACES` outcomes drown a crawler entering rung
`d`.  It is a function of the rung ALONE: not of the vein, not of the player, not
of anything a descriptor could be hiding. -/

/-- Entering rung `d` floods on a draw below `d - 1`. -/
def floodBelow (rung : Nat) : Nat := rung - 1

/-- ⚑ **The hazard escalates, rung by rung, and the player can read it.**  These
are the exact numerators the descriptor publishes and the client renders beside
the crawl button. -/
theorem the_hazard_escalates :
    (List.range DEPTH_CAP).map (fun i => floodBelow (i + 1)) = [0, 1, 2, 3, 4, 5] := by
  decide

/-- No rung is certain death: the deepest is 5 in 8, so the bottom of the shaft
is a wager and not a wall. -/
theorem the_hazard_is_never_certain :
    (List.range DEPTH_CAP).all (fun i => decide (floodBelow (i + 1) < FACES)) = true := by
  decide

/-- Rung 1 is where a run starts, so its hazard is never consulted.  Stated so a
reader does not have to wonder whether the mouth is a free crawl. -/
theorem the_mouth_is_not_entered_by_a_crawl : floodBelow 1 = 0 := by decide

/-! ## The vein — the shared daily table

Eight veins: four SEAMS by two BOTTOMS.  They agree at the mouth, split in two at
rung 2, separate into the four seams at rung 3 — and then hold there.  A seam's
two veins pay the SAME thing on rungs 2 through 5 and different things at rung 6,
so no carry short of the bottom can tell them apart.

That is the whole information design.  Rung 2 is a bet made blind; rung 3 buys
the seam; rungs 4 and 5 are priced against a seam that is known and a bottom that
is not; and rung 6 is the bit the crawler has to pay the deepest hazard to
collect.  ⚑ `VEINS = 8` is exactly the number of leaves that arrangement has, and
it divides 256 for the same reason `FACES` does. -/

inductive Vein where
  /-- A bust day, and the bottom is a bust too. -/
  | barren
  /-- A bust day with one plate at the bottom. -/
  | barrenPocket
  /-- Thin and honest, closing at the bottom. -/
  | patchy
  /-- Thin and honest, opening at the bottom. -/
  | patchyPocket
  /-- Real seams, pinching at the bottom. -/
  | layered
  /-- Real seams, opening at the bottom. -/
  | layeredPocket
  /-- ⚑ The fool's lode: five rungs of motherlode and then the seam closes to
  one.  This is the vein that makes the last rung a wager rather than a sum. -/
  | foolsLode
  /-- The one everybody is down there for. -/
  | motherlode
deriving Repr, DecidableEq

/-- ⚑ Order matters on the wire: `still_possible` and the haul list of every
wager row are rendered in THIS order, so it is part of the descriptor.  Seams run
shallow to deep, and within a seam the pinch comes before the pocket. -/
def allVeins : List Vein :=
  [.barren, .barrenPocket, .patchy, .patchyPocket,
   .layered, .layeredPocket, .foolsLode, .motherlode]

/-- How many veins the day is drawn from.  ⚠ Not a second constant: `VEINS_is_the_family`
is the check that it is `allVeins.length`, and the draw below uses THIS one. -/
abbrev VEINS : Nat := 8

theorem allVeins_complete (v : Vein) : v ∈ allVeins := by
  cases v <;> simp [allVeins]

theorem allVeins_length : allVeins.length = VEINS := rfl

theorem VEINS_is_the_family : VEINS = allVeins.length := rfl

theorem allVeins_nodup : allVeins.Nodup := by decide

def veinAt (i : Fin VEINS) : Vein := allVeins.get (Fin.cast allVeins_length.symm i)

theorem veinAt_injective : ∀ i j : Fin VEINS, veinAt i = veinAt j → i = j := by decide

def Vein.tag : Vein → String
  | .barren => "barren"
  | .barrenPocket => "barren-pocket"
  | .patchy => "patchy"
  | .patchyPocket => "patchy-pocket"
  | .layered => "layered"
  | .layeredPocket => "layered-pocket"
  | .foolsLode => "fools-lode"
  | .motherlode => "motherlode"

theorem vein_tags_are_distinct :
    (allVeins.map Vein.tag).eraseDups = allVeins.map Vein.tag := by decide

/-- What rungs 2 through `DEPTH_CAP` pay, per vein.  Rung 1 is `MOUTH_SALVAGE`
for every vein and is therefore not in these lists.

⚑ Read them in pairs: the two veins of a seam agree on the first FOUR entries and
differ only on the last.  That is what makes the bottom a hidden bit rather than
a bigger number.

⚑ The four POCKET carries are not free numbers either: each sits just above its
seam's break-even at the last rung, `c₆ > (8/3)·c₅`, which is what makes
`the_bottom_rung_is_a_coin_flip_on_every_seam` true rather than decorative.  A
pocket one unit smaller would make the last rung a plain refusal on both veins of
that seam and the bottom would stop being a decision.

⚑ And read `motherlode`'s 139 as a PRICE, not a jackpot.  When the seam and the
bottom were the same draw, a crawler standing on rung 5 of a known motherlode
crawled into a 3-in-8 shot at 108, worth 40.5.  Hiding the bottom put a fool's
lode on the other side of that wager; 139 is the number that makes the
BELIEF-AVERAGED last rung worth 40.5 again — `(3/8) · (177 + 39)/2 = (3/8) · 108`.
The deepest wager is worth exactly what it was worth when it could be seen. -/
def Vein.deepYields : Vein → List Nat
  | .barren        => [2, 1, 1, 1, 1]
  | .barrenPocket  => [2, 1, 1, 1, 12]
  | .patchy        => [2, 3, 4, 5, 6]
  | .patchyPocket  => [2, 3, 4, 5, 27]
  | .layered       => [3, 4, 6, 8, 12]
  | .layeredPocket => [3, 4, 6, 8, 39]
  | .foolsLode     => [3, 5, 8, 20, 1]
  | .motherlode    => [3, 5, 8, 20, 139]

theorem deepYields_are_full_length :
    allVeins.all (fun v => decide (v.deepYields.length = DEPTH_CAP - 1)) = true := by
  decide

/-- What rung `depth` pays on this vein.  Total: a rung outside `1 … DEPTH_CAP`
pays nothing. -/
def Vein.yieldAt (v : Vein) (depth : Nat) : Nat :=
  match depth with
  | 0 => 0
  | 1 => MOUTH_SALVAGE
  | d + 2 => (v.deepYields[d]?).getD 0

/-- What a crawler is carrying having reached `depth` on this vein and taken
every rung on the way.  There is no choice about lifting: a rung you are standing
on is a rung you took. -/
def Vein.carriedAt (v : Vein) : Nat → Nat
  | 0 => 0
  | d + 1 => v.carriedAt d + v.yieldAt (d + 1)

/-- ⚑ **The multiplier rises.**  Every vein pays strictly more the deeper it is
carried, so "one more rung" is always worth something and the only question is
whether it is worth the water. -/
theorem the_carry_rises_with_the_rung :
    allVeins.all (fun v =>
      (List.range DEPTH_CAP).all (fun i =>
        decide (v.carriedAt i < v.carriedAt (i + 1)))) = true := by
  decide

/-- ⚑ **The day is read in two instalments and the second one is the bottom.**
One carry at the mouth, two at rung 2, four from rung 3 on — the four seams — and
eight only at rung 6.  The seam is settled in the middle of the shaft; the rest
of the day is not settled anywhere a crawler can bank from.

⚠ The four in the middle is the point.  It does NOT rise at rungs 4 and 5: those
rungs pay the same on both veins of a seam, so a crawler who has read the seam is
still holding one live bit at every decision they meet. -/
theorem the_day_is_read_in_two_instalments :
    (List.range DEPTH_CAP).map (fun i =>
      (allVeins.map (fun v => v.carriedAt (i + 1))).eraseDups.length)
      = [1, 2, 4, 4, 4, 8] := by
  decide

/-- The measured carry ladder, so the numbers in the docblock are checked rather
than asserted.  Seam-mates are adjacent rows and differ in the last column
only. -/
theorem the_carry_ladder_is_measured :
    allVeins.map (fun v => (List.range (DEPTH_CAP + 1)).map v.carriedAt) =
      [ [0, 2, 4, 5, 6, 7, 8]
      , [0, 2, 4, 5, 6, 7, 19]
      , [0, 2, 4, 7, 11, 16, 22]
      , [0, 2, 4, 7, 11, 16, 43]
      , [0, 2, 5, 9, 15, 23, 35]
      , [0, 2, 5, 9, 15, 23, 62]
      , [0, 2, 5, 10, 18, 38, 39]
      , [0, 2, 5, 10, 18, 38, 177] ] := by
  decide

/-- ⚑ **The state IS the posterior, and this is why.**  Two veins that agree at a
depth agree at every shallower one, so a carry names the whole path that produced
it: there is nothing a crawler saw on the way down that `(depth, carried)` has
forgotten.  Without this, `consistentVeins` would over-report — the emitted
`still_possible` would name days the crawler had already ruled out on an earlier
rung — and the design gate's backward induction over the emitted state would be
solving a different game from the one being played. -/
theorem the_carry_path_is_its_endpoint :
    allVeins.all (fun v => allVeins.all (fun w =>
      (List.range (DEPTH_CAP + 1)).all (fun d =>
        !decide (v.carriedAt d = w.carriedAt d) ||
          (List.range d).all (fun e => decide (v.carriedAt e = w.carriedAt e))))) = true := by
  decide

/-- Which veins are still consistent with standing at `depth` holding `carried`.
This is computed from the state ALONE — it is what the crawler knows, and it is
what the emitted row enumerates. -/
def consistentVeins (depth carried : Nat) : List Vein :=
  allVeins.filter (fun v => decide (v.carriedAt depth = carried))

theorem consistentVeins_at_the_mouth :
    consistentVeins 1 MOUTH_SALVAGE = allVeins := by decide

/-! ## The risk-neutral comparison, in exact integers

Everything below is scaled by `FACES` so that the crawl/bank comparison is
ordinary `Nat` arithmetic.  No rational and no float enters the kernel; the
BACKWARD INDUCTION over the belief state (which needs both) lives in
`scripts/poa-design-gate.py`, where it is computed independently of these
definitions and compared against them. -/

/-- Banking here, scaled by `FACES`. -/
def bankValueScaled (v : Vein) (depth : Nat) : Nat := FACES * v.carriedAt depth

/-- Crawling one rung and banking there, scaled by `FACES`: the survival count
out of `FACES`, times what the next rung would leave in the sling. -/
def crawlValueScaled (v : Vein) (depth : Nat) : Nat :=
  (FACES - floodBelow (depth + 1)) * v.carriedAt (depth + 1)

/-- The shallowest rung at which the one-step comparison says stop, on a vein
that is already known.  `DEPTH_CAP` means "it never says stop". -/
def oneStepBankDepth (v : Vein) : Nat :=
  ((List.range DEPTH_CAP).filter (fun d =>
    decide (0 < d) && decide (crawlValueScaled v d ≤ bankValueScaled v d))).headD DEPTH_CAP

/-- ⚑ **The veins want five different depths.**  This is the single fact that
makes the game a game: there is no rung `k` such that "bank at `k`" is right,
because the right `k` is 2, 3, 4, 5 or 6 and which one it is is exactly what is
hidden.  ⚠ Seam-mates share the first four comparisons, so a seam can only split
its own answer at the LAST rung — and the lode seam does: `fools-lode` wants 5 and
`motherlode` wants 6, at a state where the crawler cannot tell which they are
on. -/
theorem the_veins_want_five_different_depths :
    allVeins.map oneStepBankDepth = [2, 2, 3, 3, 4, 4, 5, 6] ∧
    (allVeins.map oneStepBankDepth).eraseDups.length = 5 := by decide

/-- ⚑ **The same state wants opposite moves.**  Standing on rung 2 with 4 in the
sling, the veins still consistent with that disagree: on `barren` crawling is a
loss and on `patchy` it is a gain.  The crawler cannot tell them apart — that is
the bet, and it is a bet a coin could not settle for them. -/
theorem the_second_rung_is_a_coin_flip :
    consistentVeins 2 4 =
      [Vein.barren, Vein.barrenPocket, Vein.patchy, Vein.patchyPocket] ∧
    crawlValueScaled Vein.barren 2 < bankValueScaled Vein.barren 2 ∧
    bankValueScaled Vein.patchy 2 < crawlValueScaled Vein.patchy 2 := by
  decide

/-- ⚑ **And so does the last one, on every seam.**  At the deepest decision the
crawler has read the seam and is holding exactly two candidate days — and those
two want OPPOSITE verbs, on all four seams.  This is the fact the eight-vein
family exists to produce: the tensest rung in the shaft, the one with 5-in-8
water, is also a rung with news in it.

⚠ Stated over `consistentVeins` — the posterior a client is actually handed — and
not over a hand-listed pair, so it is a claim about every deepest decision state
in the emitted table rather than about four rows someone chose. -/
theorem the_bottom_rung_is_a_coin_flip_on_every_seam :
    allVeins.all (fun v =>
      let d := DEPTH_CAP - 1
      let cs := consistentVeins d (v.carriedAt d)
      decide (cs.length = 2) &&
      cs.any (fun w => decide (crawlValueScaled w d < bankValueScaled w d)) &&
      cs.any (fun w => decide (bankValueScaled w d < crawlValueScaled w d))) = true := by
  decide

/-- The same, one stage earlier: rung 2 is entered blind by everyone, because the
mouth cache is the same on all four veins. -/
theorem the_first_crawl_is_made_blind :
    consistentVeins 1 MOUTH_SALVAGE = allVeins ∧
    allVeins.all (fun v =>
      decide (bankValueScaled v 1 < crawlValueScaled v 1)) = true := by
  decide

/-- ⚑ **The three thinnest calls, measured.**  One part in fifty-six the wrong
way, one part in fifty-six the right way, and two parts in a hundred and
eighty-four: these are the rungs where the crawler who is right and the crawler
who is wrong made the same choice.

⚠ Two of the three are at the BOTTOM, which is new and is the point of the
pockets: each pocket carry sits just over its seam's break-even, so the last rung
is a hair's-breadth call in one direction and a plain refusal in the other, and
the crawler cannot see which.  And a thin call at rung 3 is thin for BOTH veins
of a seam at once, because the comparison there cannot see the bottom. -/
theorem the_thin_calls_are_thin :
    (bankValueScaled Vein.patchy 3, crawlValueScaled Vein.patchy 3) = (56, 55) ∧
    (bankValueScaled Vein.barrenPocket 5, crawlValueScaled Vein.barrenPocket 5)
      = (56, 57) ∧
    (bankValueScaled Vein.layeredPocket 5, crawlValueScaled Vein.layeredPocket 5)
      = (184, 186) := by
  decide

/-- ⚑ **Neither verb is dominated.**  Each of the two is strictly right somewhere
a crawler can actually stand, so a client that greyed either one out would be
hiding a move that wins. -/
theorem neither_verb_is_dominated :
    bankValueScaled Vein.patchy 2 < crawlValueScaled Vein.patchy 2 ∧
    crawlValueScaled Vein.barren 2 < bankValueScaled Vein.barren 2 := by
  decide

/-! ## Drawing the two hidden things -/

/-- The crawler's own rung draws.  Six of them, one per rung, each below `FACES`
and each a CONSUMING read off one stream — so rung 4's water is not rung 3's byte
wearing a second hat. -/
structure FloodTape where
  r1 : Fin FACES
  r2 : Fin FACES
  r3 : Fin FACES
  r4 : Fin FACES
  r5 : Fin FACES
  r6 : Fin FACES
deriving Repr, DecidableEq

def calmTape : FloodTape :=
  { r1 := ⟨7, by decide⟩, r2 := ⟨7, by decide⟩, r3 := ⟨7, by decide⟩
    r4 := ⟨7, by decide⟩, r5 := ⟨7, by decide⟩, r6 := ⟨7, by decide⟩ }

def FloodTape.rung (t : FloodTape) : Nat → Fin FACES
  | 1 => t.r1
  | 2 => t.r2
  | 3 => t.r3
  | 4 => t.r4
  | 5 => t.r5
  | 6 => t.r6
  | _ => ⟨0, by decide⟩

/-- ⚑ **A bound whose ceiling is the whole byte range never rejects.**  The
general fact, stated once: `drawBelow?` rejects exactly the bytes at or above
`ceilingFor bound`, so a bound that divides 256 leaves nothing to reject and the
draw is a single consuming read.  Both draws this module makes are instances —
the hazard at `FACES` and the day at `VEINS` — and stating it generally is what
stops the second one from being a second proof of the same arithmetic. -/
theorem a_full_ceiling_never_rejects (bound : Nat) (hb : 0 < bound)
    (hceil : SeedDraw.ceilingFor bound = 256) (b : Fin 256) (rest : List (Fin 256)) :
    SeedDraw.drawBelow? bound hb (b :: rest)
      = some (⟨b.val % bound, Nat.mod_lt _ hb⟩, rest) := by
  simp [SeedDraw.drawBelow?, hceil, b.isLt]

/-- A bound of 8 divides 256, so `ceilingFor 8 = 256` and no byte is ever
rejected: the whole tape comes off the first six bytes of a 32-byte seed. -/
theorem draw_below_eight_never_rejects (b : Fin 256) (rest : List (Fin 256)) :
    SeedDraw.drawBelow? FACES (by decide) (b :: rest)
      = some (⟨b.val % FACES, Nat.mod_lt _ (by decide)⟩, rest) :=
  a_full_ceiling_never_rejects FACES (by decide) (by decide) b rest

/-- And the day's draw likewise: `VEINS = 8` divides 256, so the vein comes off
the first byte of the day seed and the `getD` below is dead code for this
bound. -/
theorem draw_below_the_vein_count_never_rejects (b : Fin 256) (rest : List (Fin 256)) :
    SeedDraw.drawBelow? VEINS (by decide) (b :: rest)
      = some (⟨b.val % VEINS, Nat.mod_lt _ (by decide)⟩, rest) :=
  a_full_ceiling_never_rejects VEINS (by decide) (by decide) b rest

/-- `none` only if the seed runs out of acceptable bytes, which
`draw_below_eight_never_rejects` says cannot happen for a 32-byte seed.
`floodTapeFromRunSeed` falls closed to the calm tape and the theorem above
records that the fallback is dead code for the bound actually used. -/
def floodTapeFromRunSeed? (runSeed : Digest32) : Option FloodTape := do
  let (a, s₁) ← SeedDraw.drawBelow? FACES (by decide) runSeed.bytes
  let (b, s₂) ← SeedDraw.drawBelow? FACES (by decide) s₁
  let (c, s₃) ← SeedDraw.drawBelow? FACES (by decide) s₂
  let (d, s₄) ← SeedDraw.drawBelow? FACES (by decide) s₃
  let (e, s₅) ← SeedDraw.drawBelow? FACES (by decide) s₄
  let (f, _) ← SeedDraw.drawBelow? FACES (by decide) s₅
  some { r1 := a, r2 := b, r3 := c, r4 := d, r5 := e, r6 := f }

def floodTapeFromRunSeed (runSeed : Digest32) : FloodTape :=
  (floodTapeFromRunSeed? runSeed).getD calmTape

/-- Which SEAM the day is running.  ⚑ This used to be a single `drawBelow? VEINS`
that drew the whole vein; the BOTTOM has left it — see below. -/
abbrev SEAMS : Nat := DayWater.SEAM_COUNT

theorem the_family_is_the_seams_and_the_bottom : VEINS = SEAMS * 2 := by decide

/-- ⚑ **The bottom of the shaft is the SHIP'S bit, not the vent's.**  A wet bilge
means the shaft bottoms out in water that is already in the ship and the last
rung pays its seam's PINCH; a dry one means it opens into the POCKET.  The seam
is still the day's own draw, so the eight-vein family is exactly what it was —
`the_day_and_the_bilge_name_every_vein` — but one of its three bits is now a fact
Deck Descent's mouth also reads.

⚠ This is the only place in the seven-game rack where two DIFFERENT GAMES read
one draw.  `DayWater` carries the calibration, both posteriors, and the proof
that neither family moved.

⚑ **CHANGED: the SEAM moved too, and it had to.**  Both bits now come off the
ship's own draw as one `DayWater.ShipDay`.  The seam used to be drawn from
`daySeedFor` — `HiddenInstance.runSeedFor` under the sentinel player key
`DAY_TABLE_KEY` — and that seed's header block carries the MISSION ID in lane 3,
so the "day's shared table" was shared only among crawlers of THIS mission.  The
descriptor's `vein_scope = "per-slot-shared"` said more than the derivation did.
`DayWater.the_ship_day_is_not_scoped_to_a_mission` is the defect as arithmetic on
the two header blocks, and `DayWater.the_day_carries_the_same_bilge` is the proof
that repairing it moved nothing about the coupling that already ships. -/
def veinFromShipDay (day : DayWater.ShipDay) : Vein :=
  veinAt (DayWater.veinIndexOfDay day)

/-- ⚑ **The eight days name the eight published veins, one apiece.**  The same
statement `the_day_and_the_bilge_name_every_vein` makes about the two separate
draws, now about the assembled object the judge actually hands over. -/
theorem the_ship_day_names_every_vein :
    allVeins.all (fun v =>
      decide ((DayWater.allShipDays.filter fun d => veinFromShipDay d = v).length = 1))
      = true := by
  decide

/-- ⚑ **The family did not move.**  The eight `(seam, bilge)` pairs name the eight
published veins, in the published order, one apiece.  So a crawler who knows
nothing about the day is drawing from exactly the distribution the single
`drawBelow? 8` gave — the coupling is a relabelling of where one bit comes from
and not a reweighting of the day. -/
theorem the_day_and_the_bilge_name_every_vein :
    allVeins.all (fun v =>
      decide ((DayWater.allVeinDraws.filter fun t =>
        veinAt (DayWater.veinIndexFrom t.1 t.2) = v).length = 1)) = true := by
  decide

/-- The other half of the bijection, so that "exactly one preimage each" is not
resting on the two lists happening to be the same length: the eight draws land on
eight DISTINCT veins.  Together with `allVeins_complete` this is a bijection onto
the whole `Vein` type, not merely onto a list. -/
theorem the_day_and_the_bilge_collide_on_nothing :
    (DayWater.allVeinDraws.map fun t =>
      veinAt (DayWater.veinIndexFrom t.1 t.2)).eraseDups.length = VEINS := by
  decide

/-- ⚠ **AND THE STATEMENT THAT IS FALSE, kept refuted rather than deleted.**

The first draft of the theorem above asserted LIST EQUALITY — that mapping the
eight `(seam, bilge)` pairs yields `allVeins` itself — and `decide` proved its
NEGATION.  That refutation is recorded here because the reason is a trap: it is
not that the bijection fails, it is that two enumerations disagree on ORDER.
`DayWater.allBilge` lists the dry night first, while a WET night is the PINCH and
therefore index 0, so the flatMap emits each seam's POCKET before its PINCH and
`allVeins` lists them the other way round.

The distinction matters because `allVeins` order IS load-bearing on the wire —
`still_possible` and every wager row's haul list are rendered in it — while
`DayWater.allVeinDraws` is a proof-side enumeration that is rendered nowhere.  A
reader who saw the failed equality and concluded the coupling was unsupported
would be reading an ordering accident as a mechanism failure. -/
theorem the_draw_order_is_not_the_wire_order :
    (DayWater.allVeinDraws.map fun t => veinAt (DayWater.veinIndexFrom t.1 t.2))
      ≠ allVeins := by
  decide

/-- Which side of its seam a vein is: `true` is the POCKET, and it is exactly the
bit a dry bilge names. -/
def Vein.opensAtTheBottom : Vein → Bool
  | .barren | .patchy | .layered | .foolsLode => false
  | .barrenPocket | .patchyPocket | .layeredPocket | .motherlode => true

theorem the_bilge_is_the_bottom :
    ∀ (seam : Fin SEAMS) (bilge : Bool),
      (veinAt (DayWater.veinIndexFrom seam bilge)).opensAtTheBottom = !bilge := by
  decide

/-- ⚑ **THE COUPLING IS USABLE, which is a different claim from being real.**
`the_bottom_rung_is_a_coin_flip_on_every_seam` says the crawler at the deepest
decision holds exactly TWO candidate veins that want OPPOSITE verbs.  This says
the day's water names WHICH of the two — at every seam, exactly one of the two
survivors agrees with the bilge.  The bit that is undecided inside this game is
decided outside it, and that is the whole content of "information earned in one
game is usable in another". -/
theorem the_bilge_settles_the_bottom_rung :
    allVeins.all (fun v =>
      let d := DEPTH_CAP - 1
      let cs := consistentVeins d (v.carriedAt d)
      decide (cs.length = 2) &&
      decide ((cs.filter (fun w =>
        w.opensAtTheBottom = v.opensAtTheBottom)).length = 1)) = true := by
  decide

/-! ### ⚑ DELETED: `DAY_TABLE_KEY` and `daySeedFor`

The day's table used to be drawn by handing `HiddenInstance.runSeedFor` a
reserved sentinel PLAYER key.  Two things were wrong with it and only one was
written down.

The written one: a crawler whose signing-key digest equalled the sentinel would
draw the day's table as their own stream, and the docblock said "the structural
fix — a distinct sponge domain — belongs in `HiddenInstance`".
`DayWater.SHIP_DOMAIN` is that domain, and `the_ship_draw_is_not_a_player_draw`
is the separation as a fact about the preimage rather than about a constant
nobody chose adversarially.

⚠ The unwritten one, which is worse: `runSeedFor` goes through
`HiddenInstance.headerBlock`, whose lane 3 is the MISSION ID.  So the day's
"shared" table was scoped to a slot AND a mission, and could never have been read
by a second game even in principle.  `DayWater.the_ship_day_is_not_scoped_to_a_mission`.

Both are gone: the day is `DayWater.shipDayFor secret slot federationId
contentSession`, which takes no mission and no player. -/

/-! ## State -/

inductive Outcome where
  /-- Still in the shaft. -/
  | crawling
  /-- Came up the way you went in, sling full. -/
  | banked
  /-- The rung flooded. -/
  | drowned
deriving Repr, DecidableEq

def Outcome.tag : Outcome → String
  | .crawling => "crawling"
  | .banked => "banked"
  | .drowned => "drowned"

/-- Where a run is.  `carried` is what is in the sling and NOT yet banked; a
flood sets it to zero, which is the whole of "you lose what you carry". -/
structure State where
  depth : Nat
  carried : Nat
  outcome : Outcome
deriving Repr, DecidableEq

/-- A run starts already at the mouth, holding the mouth cache.  There is no rung
zero: the descent into the shaft is the fiction's entry, not a move, and starting
at rung 1 is what keeps every crawl row a genuine wager (`floodBelow 1 = 0` is
never consulted). -/
def initialState : State :=
  { depth := 1, carried := MOUTH_SALVAGE, outcome := .crawling }

def State.over (s : State) : Bool :=
  match s.outcome with
  | .crawling => false
  | _ => true

/-- The consistency invariant: a crawling run's `carried` is exactly what its
vein pays down to its depth.  Terminal states carry no claim — a drowned sling is
empty whatever the vein said. -/
def consistentB (v : Vein) (s : State) : Bool :=
  match s.outcome with
  | .crawling => decide (v.carriedAt s.depth = s.carried)
  | _ => true

theorem initialState_is_consistent (v : Vein) : consistentB v initialState = true := by
  cases v <;> decide

/-! ## Actions and the transition -/

inductive Action where
  /-- One rung deeper.  Costs nothing but the water. -/
  | crawl
  /-- Climb out with the sling.  Terminal. -/
  | bank
deriving Repr, DecidableEq

def allActions : List Action := [.crawl, .bank]

theorem allActions_complete (a : Action) : a ∈ allActions := by
  cases a <;> simp [allActions]

def Action.tag : Action → String
  | .crawl => "crawl"
  | .bank => "bank"

def Action.label : Action → String
  | .crawl => "Crawl one rung deeper"
  | .bank => "Bank the sling"

theorem action_tags_are_distinct :
    (allActions.map Action.tag).eraseDups = allActions.map Action.tag := by decide

/-- Openness.  ⚠ `bank` asks only that the run is live: there is no depth
condition, because a run starts at rung 1 already holding the mouth cache and
there is no reachable state with an empty sling.  A `nothing-carried` refusal
would be a declared reason that can never fire, and a refusal that cannot fire is
a lie the client renders. -/
def openB (s : State) (a : Action) : Bool :=
  match a with
  | .crawl => decide (s.outcome = Outcome.crawling) && decide (s.depth < DEPTH_CAP)
  | .bank => decide (s.outcome = Outcome.crawling)

/-- The successor of a crawl that floods: one rung deeper, and nothing. -/
def floodSuccessor (s : State) : State :=
  { depth := s.depth + 1, carried := 0, outcome := .drowned }

/-- The successor of a crawl that holds, on a given vein. -/
def haulSuccessor (v : Vein) (s : State) : State :=
  { depth := s.depth + 1
    carried := s.carried + v.yieldAt (s.depth + 1)
    outcome := .crawling }

def bankSuccessor (s : State) : State := { s with outcome := .banked }

/-- The effect of an action with openness already decided.  The vein enters at
exactly one place — what a surviving rung pays — and the tape at exactly one
other — whether it survives. -/
def transitionB (v : Vein) (t : FloodTape) (s : State) (a : Action) : State :=
  match a with
  | .crawl =>
      if (t.rung (s.depth + 1)).val < floodBelow (s.depth + 1) then floodSuccessor s
      else haulSuccessor v s
  | .bank => bankSuccessor s

def stepB (v : Vein) (t : FloodTape) (s : State) (a : Action) : Option State :=
  if openB s a then some (transitionB v t s a) else none

def replayB (v : Vein) (t : FloodTape) : State → List Action → Option State
  | s, [] => some s
  | s, a :: as =>
      match stepB v t s a with
      | none => none
      | some s' => replayB v t s' as

/-! ### Reading the transition back out -/

theorem step_some_open (v : Vein) (t : FloodTape) (s s' : State) (a : Action)
    (h : stepB v t s a = some s') : openB s a = true := by
  simp only [stepB] at h
  split at h
  · assumption
  · exact absurd h (by simp)

theorem step_eq_transition (v : Vein) (t : FloodTape) (s s' : State) (a : Action)
    (h : stepB v t s a = some s') : transitionB v t s a = s' := by
  simp only [stepB] at h
  split at h
  · simp only [Option.some.injEq] at h; exact h
  · exact absurd h (by simp)

theorem step_some_live (v : Vein) (t : FloodTape) (s s' : State) (a : Action)
    (h : stepB v t s a = some s') : s.outcome = Outcome.crawling := by
  have hopen := step_some_open v t s s' a h
  cases a <;> simp only [openB, Bool.and_eq_true, decide_eq_true_eq] at hopen
  · exact hopen.1
  · exact hopen

/-- ⚑ **A flood takes the whole sling.**  There is no partial loss and no
insurance: the only two things a crawl can produce are one more rung of salvage
and nothing at all. -/
theorem a_flood_takes_everything (v : Vein) (t : FloodTape) (s s' : State)
    (h : stepB v t s Action.crawl = some s') (hd : s'.outcome = Outcome.drowned) :
    s'.carried = 0 ∧ s'.depth = s.depth + 1 := by
  have ht := step_eq_transition v t s s' Action.crawl h
  simp only [transitionB] at ht
  split at ht
  · subst ht; exact ⟨rfl, rfl⟩
  · subst ht; simp only [haulSuccessor] at hd; exact absurd hd (by simp)

/-- Banking keeps exactly what is in the sling and moves nothing else. -/
theorem banking_keeps_the_sling (v : Vein) (t : FloodTape) (s s' : State)
    (h : stepB v t s Action.bank = some s') :
    s'.carried = s.carried ∧ s'.depth = s.depth ∧ s'.outcome = Outcome.banked := by
  have ht := step_eq_transition v t s s' Action.bank
  simp only [transitionB, bankSuccessor] at ht
  have := ht h
  subst this
  exact ⟨rfl, rfl, rfl⟩

/-- A crawl advances exactly one rung, whichever way it goes. -/
theorem a_crawl_is_exactly_one_rung (v : Vein) (t : FloodTape) (s s' : State)
    (h : stepB v t s Action.crawl = some s') : s'.depth = s.depth + 1 := by
  have ht := step_eq_transition v t s s' Action.crawl h
  simp only [transitionB] at ht
  split at ht <;> (subst ht; rfl)

/-- ⚑ **The invariant that makes the emitted table honest.**  A crawling run's
sling is exactly what its vein pays to its depth, so the veins a row enumerates
from `(depth, carried)` really are the veins the run could be on. -/
theorem step_preserves_consistency (v : Vein) (t : FloodTape) (s s' : State)
    (a : Action) (hc : consistentB v s = true) (h : stepB v t s a = some s') :
    consistentB v s' = true := by
  have ht := step_eq_transition v t s s' a h
  have hlive := step_some_live v t s s' a h
  simp only [consistentB, hlive] at hc
  cases a
  · simp only [transitionB] at ht
    split at ht
    · subst ht; rfl
    · subst ht
      simp only [consistentB, haulSuccessor, decide_eq_true_eq]
      simp only [decide_eq_true_eq] at hc
      simp only [Vein.carriedAt, hc, decide_true]
  · simp only [transitionB, bankSuccessor] at ht
    subst ht
    rfl

theorem replay_preserves_consistency (v : Vein) (t : FloodTape) (acts : List Action) :
    ∀ (s s' : State), consistentB v s = true → replayB v t s acts = some s' →
      consistentB v s' = true := by
  induction acts with
  | nil =>
      intro s s' hc h
      simp only [replayB, Option.some.injEq] at h
      subst h
      exact hc
  | cons a as ih =>
      intro s s' hc h
      simp only [replayB] at h
      split at h
      · contradiction
      · rename_i s₁ hstep
        exact ih s₁ s' (step_preserves_consistency v t s s₁ a hc hstep) h

/-! ### The clock, which is the depth and nothing else

There is no separate action budget.  Every accepted action either goes one rung
deeper or ends the run, so the length of an accepted transcript is bounded by the
shaft itself. -/

/-- What is left: rungs still enterable, plus the bank that ends it. -/
def fuel (s : State) : Nat :=
  match s.outcome with
  | .crawling => DEPTH_CAP + 1 - s.depth
  | _ => 0

/-- The longest a run can be. -/
abbrev ACTION_LIMIT : Nat := DEPTH_CAP

theorem initial_fuel : fuel initialState = ACTION_LIMIT := by decide

theorem step_decreases_fuel (v : Vein) (t : FloodTape) (s s' : State) (a : Action)
    (hd : s.depth ≤ DEPTH_CAP) (h : stepB v t s a = some s') : fuel s' < fuel s := by
  have hopen := step_some_open v t s s' a h
  have ht := step_eq_transition v t s s' a h
  have hlive := step_some_live v t s s' a h
  cases a
  · simp only [openB, Bool.and_eq_true, decide_eq_true_eq] at hopen
    obtain ⟨-, hlt⟩ := hopen
    simp only [transitionB] at ht
    split at ht
    · subst ht
      simp only [fuel, floodSuccessor, hlive]
      omega
    · subst ht
      simp only [fuel, haulSuccessor, hlive]
      omega
  · simp only [transitionB, bankSuccessor] at ht
    subst ht
    simp only [fuel, hlive]
    omega

theorem step_depth_le (v : Vein) (t : FloodTape) (s s' : State) (a : Action)
    (hd : s.depth ≤ DEPTH_CAP) (h : stepB v t s a = some s') : s'.depth ≤ DEPTH_CAP := by
  have hopen := step_some_open v t s s' a h
  have ht := step_eq_transition v t s s' a h
  cases a
  · simp only [openB, Bool.and_eq_true, decide_eq_true_eq] at hopen
    simp only [transitionB] at ht
    split at ht <;> (subst ht; simp only [floodSuccessor, haulSuccessor]; omega)
  · simp only [transitionB, bankSuccessor] at ht
    subst ht
    exact hd

theorem replayB_length_le_fuel (v : Vein) (t : FloodTape) (acts : List Action) :
    ∀ (s s' : State), s.depth ≤ DEPTH_CAP → replayB v t s acts = some s' →
      acts.length + fuel s' ≤ fuel s := by
  induction acts with
  | nil =>
      intro s s' _ h
      simp only [replayB, Option.some.injEq] at h
      subst h
      simp
  | cons a as ih =>
      intro s s' hd h
      simp only [replayB] at h
      split at h
      · contradiction
      · rename_i s₁ hstep
        have h1 := step_decreases_fuel v t s s₁ a hd hstep
        have hd1 := step_depth_le v t s s₁ a hd hstep
        have h2 := ih s₁ s' hd1 h
        simp only [List.length_cons]
        omega

/-- ⚑ **An accepted transcript is never longer than the shaft.**  This is what the
emitted `action_limit` IS: not a cap the client enforces, a cap the kernel cannot
exceed. -/
theorem accepted_transcript_within_budget (v : Vein) (t : FloodTape)
    (acts : List Action) (s' : State) (h : replayB v t initialState acts = some s') :
    acts.length ≤ ACTION_LIMIT := by
  have := replayB_length_le_fuel v t acts initialState s' (by decide) h
  rw [initial_fuel] at this
  omega

/-! ## Refusals — each emitted reason is a theorem, and each one fires -/

/-- Why an action is refused here.  Tested in the SAME order `openB` tests its
conjuncts, so the reason a client renders is the first thing that actually
failed. -/
def refusalReason (s : State) (a : Action) : String :=
  match s.outcome with
  | .banked => "run-banked"
  | .drowned => "run-drowned"
  | .crawling =>
      match a with
      | .crawl => "at-the-bottom"
      | .bank => "unreachable-bank-refusal"

/-- The reasons this module declares.  ⚠ `unreachable-bank-refusal` is
DELIBERATELY not in it: `openB` never refuses a bank on a crawling run, so that
branch of `refusalReason` is dead and naming it would be declaring a refusal that
cannot fire.  `every_declared_reason_fires` below is the check. -/
def declaredReasons : List String := ["run-banked", "run-drowned", "at-the-bottom"]

theorem not_open_refuses (v : Vein) (t : FloodTape) (s : State) (a : Action)
    (h : openB s a = false) : stepB v t s a = none := by
  simp [stepB, h]

theorem banked_refuses_everything (v : Vein) (t : FloodTape) (s : State) (a : Action)
    (h : s.outcome = Outcome.banked) : stepB v t s a = none := by
  refine not_open_refuses v t s a ?_
  cases a <;> simp [openB, h]

theorem drowned_refuses_everything (v : Vein) (t : FloodTape) (s : State) (a : Action)
    (h : s.outcome = Outcome.drowned) : stepB v t s a = none := by
  refine not_open_refuses v t s a ?_
  cases a <;> simp [openB, h]

theorem the_bottom_refuses_a_crawl (v : Vein) (t : FloodTape) (s : State)
    (h : DEPTH_CAP ≤ s.depth) : stepB v t s Action.crawl = none := by
  refine not_open_refuses v t s Action.crawl ?_
  simp [openB, Nat.not_lt.mpr h]

/-- ⚑ **A live run can always climb out.**  Bank is open at every crawling state,
so a crawler is never trapped and the choice is always genuinely two-sided while
the run is alive. -/
theorem a_live_run_can_always_bank (s : State) (h : s.outcome = Outcome.crawling) :
    openB s Action.bank = true := by
  simp [openB, h]

/-- ⚑ **Both verbs are open above the bottom.**  There is no reachable rung where
the crawler is only being shown one button. -/
theorem both_verbs_are_open_above_the_bottom (s : State)
    (hlive : s.outcome = Outcome.crawling) (hd : s.depth < DEPTH_CAP) :
    openB s Action.crawl = true ∧ openB s Action.bank = true := by
  refine ⟨?_, a_live_run_can_always_bank s hlive⟩
  simp [openB, hlive, hd]

/-! ## The parametric table — the rules without the day

A descriptor cannot carry the vein.  What it carries instead is a table in which
every crawl row names its exact flood odds, its flood successor, and ONE
SUCCESSOR PER STILL-POSSIBLE VEIN.  `step_lands_in_the_named_successors` is the
fact that makes that honest: whatever the day is, the real move is one of the
moves the row already named, and the descriptor still has not said which. -/

/-- A row of the emitted table.  `refuse` carries a named reason; `advance` is a
bank, which consults nothing; `wager` is a crawl, which consults the tape (its
odds are public) and the vein (its odds are not). -/
inductive Row where
  | refuse (reason : String)
  | advance (next : State)
  | wager (floodBelow : Nat) (onFlood : State) (hauls : List (Vein × State))
deriving Repr, DecidableEq

/-- One successor per vein still consistent with what the crawler is holding. -/
def haulsAt (s : State) : List (Vein × State) :=
  (consistentVeins s.depth s.carried).map (fun v => (v, haulSuccessor v s))

def rowFor (s : State) (a : Action) : Row :=
  if openB s a then
    match a with
    | .bank => .advance (bankSuccessor s)
    | .crawl => .wager (floodBelow (s.depth + 1)) (floodSuccessor s) (haulsAt s)
  else .refuse (refusalReason s a)

def rowSuccessors (s : State) (a : Action) : List State :=
  match rowFor s a with
  | .refuse _ => []
  | .advance n => [n]
  | .wager _ onFlood hauls => onFlood :: hauls.map Prod.snd

/-- ⚑ **The row names the real move.**  For every vein consistent with the state,
every tape, and every action, the transition the kernel takes is one of the
successors the emitted row already declared.  A client that renders the whole row
has rendered every outcome that can occur — and the descriptor has still not said
which one will. -/
theorem step_lands_in_the_named_successors (v : Vein) (t : FloodTape) (s s' : State)
    (a : Action) (hc : consistentB v s = true) (h : stepB v t s a = some s') :
    s' ∈ rowSuccessors s a := by
  have hopen := step_some_open v t s s' a h
  have ht := step_eq_transition v t s s' a h
  have hlive := step_some_live v t s s' a h
  simp only [rowSuccessors, rowFor, hopen, ↓reduceIte]
  cases a
  · simp only [transitionB] at ht
    split at ht
    · subst ht; exact List.mem_cons_self ..
    · subst ht
      refine List.mem_cons_of_mem _ ?_
      simp only [haulsAt, List.map_map, List.mem_map]
      refine ⟨v, ?_, rfl⟩
      simp only [consistentVeins, List.mem_filter]
      simp only [consistentB, hlive, decide_eq_true_eq] at hc
      exact ⟨allVeins_complete v, by simp [hc]⟩
  · simp only [transitionB] at ht
    subst ht
    exact List.mem_cons_self ..

/-- A refused row names no successor at all, so a client that greys an action out
is not guessing about a move it could not see. -/
theorem a_refusal_names_nothing (s : State) (a : Action) (r : String)
    (h : rowFor s a = .refuse r) : rowSuccessors s a = [] := by
  simp [rowSuccessors, h]

/-- ⚑ **A wager row publishes its own odds.**  The numerator a client renders IS
the numerator the transition compares against; there is no second hazard table. -/
theorem the_wager_publishes_the_real_odds (s : State) (fb : Nat) (onFlood : State)
    (hauls : List (Vein × State)) (h : rowFor s Action.crawl = .wager fb onFlood hauls) :
    fb = floodBelow (s.depth + 1) ∧ onFlood = floodSuccessor s := by
  simp only [rowFor] at h
  split at h
  · simp only [Row.wager.injEq] at h
    exact ⟨h.1.symm, h.2.1.symm⟩
  · exact absurd h (by simp)

/-! ## The reachable closure

Both branches of every wager are followed, so the closure is the set of states
reachable on SOME vein against SOME tape — exactly what a descriptor naming every
branch has to declare.

⚑ **THE MEASUREMENTS NO LONGER EVALUATE IN THIS MODULE (2026-08-08).** This module is in
the `Dregg2.FFI` closure — the crypto archive's build — and a `native_decide` here made
every game-fixture regression a hard failure of every Rust proving target (the
compilation-unit coupling the stale-fixture outage measured). Each measured property —
here, in the census/lines sections below, and the two Poseidon2 sentinel fixtures at the
bottom — stays as an evaluation-free `check_* : Bool` definition (a `def` body elaborates
without running). The EVALUATION — each `check_* = true`, pinned by `native_decide` +
`#assert_compiled` — lives in `VentCrawlFixtures.lean`, rooted in the `PathOfAngelsGuards`
library: a plain `lake build` still runs every pin, and a stale fixture reds the guard
library instead of the archive.

Named residue: NONE. No construction in this module consumes a `native_decide` proof as
data, so every pin moved.  (`by decide` theorems — the carry ladder, the thin calls, the
map discount — never touch a sponge and stay.) -/

def parametricSuccessors (s : State) : List State :=
  allActions.flatMap (rowSuccessors s)

def parametricWithin : Nat → List State
  | 0 => [initialState]
  | fuel + 1 =>
      let prior := parametricWithin fuel
      (prior ++ prior.flatMap parametricSuccessors).eraseDups

def parametricStates : List State := parametricWithin (ACTION_LIMIT + 1)

/-! ### The per-vein census

The tape is the crawler's dice, not the day: enumerating 8^6 tapes would be
enumerating luck.  What IS the instance family is the eight veins, and the census
below walks the real transition on each of them following BOTH outcomes of every
rung — which is exactly the set of positions a crawler on that vein can occupy. -/

/-- ⚑ **The veins are not relabellings of each other.**  The eight hidden draws
produce eight DIFFERENT deepest carries, so the bits that distinguish them buy a
crawler something — including the last bit, which no rung but the bottom pays
differently for.  (The reachable COUNTS coincide — the shaft is the same shaft —
which is why this is stated over the carries and not over the state census.) -/
theorem the_family_does_not_collapse :
    (allVeins.map (fun v => v.carriedAt DEPTH_CAP)).eraseDups.length = VEINS := by
  decide

/-! ### Lines through the shaft, played out -/

/-- All the way to the bottom.  Six actions, the whole shaft. -/
def greedLine : List Action := [.crawl, .crawl, .crawl, .crawl, .crawl, .bank]

theorem the_greed_line_is_the_whole_budget : greedLine.length = ACTION_LIMIT := by decide

/-! ## Rendering names

Ids are semantic, not enumeration indices, so a re-emission that visits states in
a different order produces the same wire. -/

def stateId (s : State) : String :=
  "vc:" ++ toString s.depth ++ ":" ++ toString s.carried ++ ":" ++ s.outcome.tag

/-- What a client may render.  Everything the rules read is here, which is the
property the design gate's differential depends on: it rebuilds every verdict
from these fields alone and refuses on disagreement. -/
def solvedB (s : State) : Bool := decide (s.outcome = Outcome.banked)

def drownedB (s : State) : Bool := decide (s.outcome = Outcome.drowned)

/-! ## Config, judge and receipt

The judged surface is `DeckDescent`'s: a `Config` whose instance field is pinned
to the precommitted run seed by a proof obligation, a `terminalOutput` that fails
closed against the mission's own acceptance predicate, and a `judge` that binds
the transcript into the receipt.

⚠ The one difference, and it is the point of this game: the VEIN is not in the
`Config`.  It arrives in the `JudgeContext`, derived by the node from the slot
secret under `DAY_TABLE_KEY`, so there is no field for a host to set and no claim
for a client to make. -/

structure Config where
  mission : MissionSpec
  /-- The crawler's own rung draws. -/
  floods : FloodTape
  /-- What the bottom of the shaft pays on top of the salvage.  Declared in the
  config and checked against the mission's allowlist, so a run cannot invent a
  relic. -/
  deepRelic : RelicId
  relic_declared : deepRelic ∈ mission.allowedRelics
  /-- ⚑ The tape a run is judged against is the one its precommitted per-player
  seed draws.  A host cannot re-roll the water after reading the transcript. -/
  floods_eq : floods = floodTapeFromRunSeed mission.runSeed

/-- ⚑ The tape a run is judged on is the one its precommitted seed draws. -/
theorem judged_tape_is_the_drawn_tape (cfg : Config) :
    cfg.floods = floodTapeFromRunSeed cfg.mission.runSeed := cfg.floods_eq

/-! ### The map, and what the water does to it

⚑ The `intel` a run pays is the MAP: which rungs of this shaft were seen and what
they held.  Both outcomes pay it, because both outcomes saw the same rungs — and
that is the whole of the fix.  A consolation paid ONLY to a drowned run, or paid
at full rate to one, makes drowning the better outcome for anyone who wants the
map, and a crawler with an unpriced downside is not making a wager: the deepest
rung is a free roll and the game has no second verb for them.

So the map is paid on both and DISCOUNTED by the water.  A run that climbs out
brings its notes with it; a run the water takes leaves half of them in the shaft.
Half is still worth carrying home — that is the residual the consolation exists
for, and `a_drowned_run_is_always_worth_submitting` is the check — and it is
never worth more than climbing out from where you stood, which is
`the_map_that_drowns_is_never_worth_more`. -/

/-- What a run that comes home is paid for the shaft it mapped: one per rung
reached, all of it. -/
def mapBanked (depth : Nat) : Nat := depth

/-- And what survives a drowning: half the notes, rounded down. -/
def mapDrowned (depth : Nat) : Nat := depth / 2

/-- ⚑ **The map that drowns is never worth more than the map that climbs out.**
At every rung a crawler can stand on, drowning into the next one pays strictly
less map than banking right here — so the loss branch of every wager is a loss on
the map exactly as it is on the sling, and no posture is handed a free roll. -/
theorem the_map_that_drowns_is_never_worth_more :
    (List.range DEPTH_CAP).all (fun i =>
      decide (mapDrowned (i + 2) ≤ mapBanked (i + 1))) = true := by decide

/-- And strictly less from the second rung on, where a crawler has anything to
weigh: the tie at the mouth is the one place a drowning costs no map, because
there is no shallower rung to have come home from. -/
theorem the_map_discount_bites_below_the_mouth :
    (List.range (DEPTH_CAP - 1)).all (fun i =>
      decide (mapDrowned (i + 3) < mapBanked (i + 2))) = true := by decide

/-- The wire-shaped payout.  A banked run pays its sling in `supplies` and
`score` and its map in `intel`, and the bottom rung pays the deep relic on top.
A DROWNED run pays the discounted map and nothing else: the sling is gone, and
what is left is what the crawler had already learnt. -/
def Config.rawPayout (cfg : Config) (s : State) : RawContribution :=
  match s.outcome with
  | .banked =>
      { intel := mapBanked s.depth, supplies := s.carried, cohesion := 0
        influence := 0
        score := s.carried
        relics := if s.depth = DEPTH_CAP then [cfg.deepRelic] else [] }
  | .drowned =>
      { intel := mapDrowned s.depth, supplies := 0, cohesion := 0, influence := 0
        score := 0
        relics := [] }
  | .crawling =>
      { intel := 0, supplies := 0, cohesion := 0, influence := 0, score := 0
        relics := [] }

/-- The payout reads the map through the two named ladders and nowhere else, so
the numbers `VentCrawlEmit` renders into `vent.payout` are these ones. -/
theorem the_payout_is_the_map (cfg : Config) (s : State) :
    ((s.outcome = Outcome.banked → (cfg.rawPayout s).intel = mapBanked s.depth) ∧
     (s.outcome = Outcome.drowned → (cfg.rawPayout s).intel = mapDrowned s.depth)) := by
  constructor <;> intro h <;> simp [Config.rawPayout, h]

/-- Fail closed, twice: the payout must validate into the bounded type at all, and
the mission itself must accept it.  There is no branch that widens the
allowlist and none that clamps a meter. -/
def terminalOutput (cfg : Config) (s : State) : Option (Contribution × ArtifactRef) :=
  match s.outcome with
  | .crawling => none
  | _ =>
      match validateContribution (cfg.rawPayout s) with
      | none => none
      | some c =>
          if cfg.mission.acceptsContribution c then some (c, cfg.mission.artifact) else none

theorem terminalOutput_none_while_crawling (cfg : Config) (s : State)
    (h : s.outcome = Outcome.crawling) : terminalOutput cfg s = none := by
  simp [terminalOutput, h]

theorem terminalOutput_is_mission_accepted (cfg : Config) (s : State)
    {out : Contribution × ArtifactRef} (h : terminalOutput cfg s = some out) :
    cfg.mission.acceptsContribution out.1 = true := by
  simp only [terminalOutput] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · simp only [Option.some.injEq] at h
        subst out
        assumption
      · contradiction

theorem terminalOutput_names_exact_artifact (cfg : Config) (s : State)
    {out : Contribution × ArtifactRef} (h : terminalOutput cfg s = some out) :
    out.2 = cfg.mission.artifact := by
  simp only [terminalOutput] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · simp only [Option.some.injEq] at h
        rw [← h]
      · contradiction

theorem terminalOutput_canonical (cfg : Config) (s : State)
    {contribution : Contribution} {artifact : ArtifactRef}
    (h : terminalOutput cfg s = some (contribution, artifact)) :
    terminalOutput cfg s = some (contribution, cfg.mission.artifact) := by
  have hart := terminalOutput_names_exact_artifact cfg s h
  change artifact = cfg.mission.artifact at hart
  rw [hart] at h
  exact h

def step (cfg : Config) (v : Vein) (s : State) (a : Action) : Option State :=
  stepB v cfg.floods s a

def replay (cfg : Config) (v : Vein) : State → List Action → Option State :=
  replayB v cfg.floods

theorem step_eq_stepB (cfg : Config) (v : Vein) (s : State) (a : Action) :
    step cfg v s a = stepB v cfg.floods s a := rfl

theorem replay_eq_replayB (cfg : Config) (v : Vein) (s : State) (acts : List Action) :
    replay cfg v s acts = replayB v cfg.floods s acts := rfl

def byte (n : Nat) : Fin 256 := ⟨n % 256, Nat.mod_lt _ (by omega)⟩

def actionCode : Action → Nat
  | .crawl => 0
  | .bank => 1

theorem actionCode_injective (a a' : Action) (h : actionCode a = actionCode a') :
    a = a' := by
  cases a <;> cases a' <;> simp_all [actionCode]

def actionAt (actions : List Action) (i : Nat) : Nat :=
  match actions[i]? with
  | some a => actionCode a
  | none => 255

def transcriptDigest (actions : List Action) : Digest32 where
  bytes := List.ofFn (fun i : Fin 32 =>
    if i.val = 0 then byte actions.length else byte (actionAt actions (i.val - 1)))
  length_eq := by simp

structure JudgedRun where
  finalState : State
  afterWorld : WorldState
  receipt : RunReceipt

/-- ⚠ Unlike every other POAG1 judge context, this one carries the day.  It has
to: the vein is a per-SLOT draw and the run seed is a per-PLAYER one, so the
shared table cannot arrive through `mission.runSeed`.  `Judged.judgeAdmitted`
builds it with `DayWater.shipDayFor` from the very slot secret that
`admissionChecks` already binds to the published commitment.

⚑ It is ONE field, not two.  It used to be a `daySeed : Digest32` — drawn under a
sentinel player key, and mission-scoped — beside a `bilge : Bool` drawn under the
ship domain.  Two facts about the same night arriving by two derivations with two
different scopes is how the rack ended up with one shareable fact and one that
only looked shareable.  The day arrives as the day.

It arrives here and NOT in the `Config`: a host must not be able to name it,
because Deck Descent's mouth reads the same water. -/
structure JudgeContext where
  actorRoot : Digest32
  playerKey : Digest32
  previousPlayerCounter : Nat
  day : DayWater.ShipDay

/-- The vein a context is judged against.  Named so the derivation is one
function and not an expression repeated at two call sites. -/
def JudgeContext.vein (ctx : JudgeContext) : Vein :=
  veinFromShipDay ctx.day

def judge (cfg : Config) (before : WorldState) (ctx : JudgeContext)
    (actions : List Action) : Option JudgedRun :=
  match replay cfg ctx.vein initialState actions with
  | none => none
  | some finalState =>
      match terminalOutput cfg finalState with
      | none => none
      | some (contribution, _artifact) =>
          match happlied : applyContribution cfg.mission contribution before with
          | none => none
          | some afterWorld =>
              some {
                finalState
                afterWorld
                receipt := {
                  mission := cfg.mission
                  federationId := cfg.mission.federationId
                  contentRoot := cfg.mission.contentRoot
                  activationDigest := cfg.mission.activationDigest
                  contentSession := cfg.mission.contentSession
                  contentEpoch := cfg.mission.epoch
                  actorRoot := ctx.actorRoot
                  playerKey := ctx.playerKey
                  previousPlayerCounter := ctx.previousPlayerCounter
                  playerCounter := ctx.previousPlayerCounter + 1
                  runSeed := cfg.mission.runSeed
                  preWorld := before
                  postWorld := afterWorld
                  contribution
                  transcriptDigest := transcriptDigest actions
                  federation_matches := rfl
                  content_root_matches := rfl
                  activation_matches := rfl
                  content_session_matches := rfl
                  content_epoch_matches := rfl
                  run_seed_matches := rfl
                  player_counter_advances := rfl
                  applied := happlied
                }
              }

theorem judge_some_sound (cfg : Config) (before : WorldState) (ctx : JudgeContext)
    (actions : List Action) {run : JudgedRun} (h : judge cfg before ctx actions = some run) :
    replay cfg ctx.vein initialState actions = some run.finalState ∧
    terminalOutput cfg run.finalState =
      some (run.receipt.contribution, cfg.mission.artifact) ∧
    applyContribution cfg.mission run.receipt.contribution before = some run.afterWorld ∧
    run.receipt.mission = cfg.mission ∧
    run.receipt.transcriptDigest = transcriptDigest actions := by
  unfold judge at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · contradiction
      · simp only [Option.some.injEq] at h
        subst run
        refine ⟨by assumption, ?_, by assumption, rfl, rfl⟩
        apply terminalOutput_canonical
        assumption

theorem judge_receipt_binds_transcript (cfg : Config) (before : WorldState)
    (ctx : JudgeContext) (actions : List Action) {run : JudgedRun}
    (h : judge cfg before ctx actions = some run) :
    run.receipt.transcriptDigest = transcriptDigest actions :=
  (judge_some_sound cfg before ctx actions h).2.2.2.2

/-- ⚑ **A judged run is over.**  There is no rewarded transcript whose final state
is still in the shaft: a run that stopped sending actions without banking and
without drowning is not a run. -/
theorem judged_run_is_terminal (cfg : Config) (before : WorldState)
    (ctx : JudgeContext) (actions : List Action) {run : JudgedRun}
    (h : judge cfg before ctx actions = some run) : run.finalState.over = true := by
  have hsound := judge_some_sound cfg before ctx actions h
  cases ho : run.finalState.outcome with
  | crawling =>
      have hterm := hsound.2.1
      rw [terminalOutput_none_while_crawling cfg _ ho] at hterm
      exact absurd hterm (by simp)
  | banked => simp [State.over, ho]
  | drowned => simp [State.over, ho]

/-- A judged run spent no more than the shaft.  The receipt cannot report a
seven-action crawl. -/
theorem judged_run_within_budget (cfg : Config) (before : WorldState)
    (ctx : JudgeContext) (actions : List Action) {run : JudgedRun}
    (h : judge cfg before ctx actions = some run) : actions.length ≤ ACTION_LIMIT := by
  have hsound := judge_some_sound cfg before ctx actions h
  exact accepted_transcript_within_budget ctx.vein cfg.floods actions run.finalState hsound.1

/-! ## The ship draw, on a fixture

The claim that the SHIP DOMAIN separates the shared draw from a player's own is
made refutable here rather than left in the docblock.  ⚠ Both checks evaluate
Poseidon2 sponges, so they run ONLY under `native_decide` — in
`VentCrawlFixtures.lean`, never in this module — and the elaborator is never
asked to reduce a sponge (the `check_*` bodies below are inert `def`s). -/

#assert_axioms the_family_is_the_seams_and_the_bottom
#assert_axioms the_ship_day_names_every_vein
#assert_axioms the_day_and_the_bilge_name_every_vein
#assert_axioms the_day_and_the_bilge_collide_on_nothing
#assert_axioms the_draw_order_is_not_the_wire_order
#assert_axioms the_bilge_is_the_bottom
#assert_axioms the_bilge_settles_the_bottom_rung
#assert_axioms allVeins_complete
#assert_axioms allVeins_nodup
#assert_axioms veinAt_injective
#assert_axioms vein_tags_are_distinct
#assert_axioms VEINS_is_the_family
#assert_axioms deepYields_are_full_length
#assert_axioms the_hazard_escalates
#assert_axioms the_hazard_is_never_certain
#assert_axioms the_mouth_is_not_entered_by_a_crawl
#assert_axioms the_carry_rises_with_the_rung
#assert_axioms the_day_is_read_in_two_instalments
#assert_axioms the_carry_ladder_is_measured
#assert_axioms the_carry_path_is_its_endpoint
#assert_axioms consistentVeins_at_the_mouth
#assert_axioms the_veins_want_five_different_depths
#assert_axioms the_second_rung_is_a_coin_flip
#assert_axioms the_bottom_rung_is_a_coin_flip_on_every_seam
#assert_axioms the_first_crawl_is_made_blind
#assert_axioms the_thin_calls_are_thin
#assert_axioms neither_verb_is_dominated
#assert_axioms the_family_does_not_collapse
#assert_axioms a_full_ceiling_never_rejects
#assert_axioms draw_below_eight_never_rejects
#assert_axioms draw_below_the_vein_count_never_rejects
#assert_axioms initialState_is_consistent
#assert_axioms allActions_complete
#assert_axioms action_tags_are_distinct
#assert_axioms step_some_open
#assert_axioms step_eq_transition
#assert_axioms step_some_live
#assert_axioms a_flood_takes_everything
#assert_axioms banking_keeps_the_sling
#assert_axioms a_crawl_is_exactly_one_rung
#assert_axioms step_preserves_consistency
#assert_axioms replay_preserves_consistency
#assert_axioms initial_fuel
#assert_axioms step_decreases_fuel
#assert_axioms step_depth_le
#assert_axioms replayB_length_le_fuel
#assert_axioms accepted_transcript_within_budget
#assert_axioms not_open_refuses
#assert_axioms banked_refuses_everything
#assert_axioms drowned_refuses_everything
#assert_axioms the_bottom_refuses_a_crawl
#assert_axioms a_live_run_can_always_bank
#assert_axioms both_verbs_are_open_above_the_bottom
#assert_axioms step_lands_in_the_named_successors
#assert_axioms a_refusal_names_nothing
#assert_axioms the_wager_publishes_the_real_odds
#assert_axioms the_greed_line_is_the_whole_budget
#assert_axioms judged_tape_is_the_drawn_tape
#assert_axioms the_map_that_drowns_is_never_worth_more
#assert_axioms the_map_discount_bites_below_the_mouth
#assert_axioms the_payout_is_the_map
#assert_axioms terminalOutput_none_while_crawling
#assert_axioms terminalOutput_is_mission_accepted
#assert_axioms terminalOutput_names_exact_artifact
#assert_axioms terminalOutput_canonical
#assert_axioms step_eq_stepB
#assert_axioms replay_eq_replayB
#assert_axioms actionCode_injective
#assert_axioms judge_some_sound
#assert_axioms judge_receipt_binds_transcript
#assert_axioms judged_run_is_terminal
#assert_axioms judged_run_within_budget

-- The seventeen measured-design and sentinel pins (`#assert_compiled` + `native_decide`)
-- live in `VentCrawlFixtures.lean`, rooted in `PathOfAngelsGuards` — see the
-- reachable-closure header above.

end Dregg2.Games.PathOfAngels.VentCrawl
