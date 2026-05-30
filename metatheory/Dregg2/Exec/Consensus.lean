/-
# Dregg2.Exec.Consensus — the quorum-finality → finality-tier bridge ON a
network-ordering cell.

This module is the *executable cell* counterpart of the two consensus portals:
  • `World.lean` — the network/clock/randomness oracle, its concrete `quorumReached`
    vote count, the abstract-`Finality.Committed`-instantiating `committedByQuorum`, and
    the PROVED monotonicity facts (`quorum_monotone`, `committedByQuorum_mono`,
    `world_no_downgrade`);
  • `Finality.lean` — the four-tier canonicity lattice (Law 2), the `Tier` `LinearOrder`,
    the cross-tier `crossTierJoin = max`, and `no_downgrade`.

`World.lean` already wires the abstract `Finality.Committed` to a concrete network vote
count; what it does NOT do is put a *tier annotation* on the committed object and tie the
two notions of "committed" together at a single cell. That is this module's job: a
**`NetCell`** — a turn (block) observed by a set of replicas, carrying its quorum evidence
*and* a `Finality.Tier` — together with the bridge theorems that say:

  1. `quorum_reaches_bft_tier` — a turn that is `committedByQuorum` inhabits the
     BFT/quorum finality tier (`Tier.bft`) of the `Finality` lattice: the World "committed"
     and the Finality "committed at tier bft" coincide on a `NetCell`.
  2. `finality_monotone_on_net` / `net_no_downgrade` — once a turn reaches a tier via
     quorum it never drops below it (riding `Finality.no_downgrade` /
     `World.world_no_downgrade` over the cell's finalization run).
  3. `quorum_grows_preserves_finality` — adding replica observations (a larger quorum,
     a later round) only raises/holds the tier, never lowers it (riding
     `committedByQuorum_mono`).
  4. `cross_tier_join_on_net` — a turn observed at two tiers settles at the `max`
     (instantiating `Finality.commit_at_join_of_tiers`).

What stays OPEN (NOT attempted here — they need an adversary / GST model that the bare
`World` interface deliberately omits): Byzantine quorum-intersection safety and post-GST
liveness. `World.lean` already states these as honest `sorry`'d `…_OPEN` theorems; we cite
those rather than restating them. Any genuinely-new obligation is an explicit `-- OPEN:`.

Builds only on existing modules by `import`; defines nothing already taken. All names live
in `namespace Dregg2.Exec.Consensus`.

Axiom-hygiene note (read with the `#assert_axioms` blocks below): theorems whose statements
are *purely* about the tier lattice / the cell record / the World monotonicity facts are
genuinely kernel-clean and are pinned with `#assert_axioms`. `Finality.no_downgrade` and
`World.committedByQuorum_mono` are themselves `sorry`-free, so the theorems riding them are
clean too. We do NOT pin anything that quantifies over (or instantiates) the
`…_OPEN`/`sorry`'d World theorems — there are none here; this module never touches the open
ones except to cite them in prose.
-/
import Dregg2.World
import Dregg2.Finality
import Dregg2.Tactics

namespace Dregg2.Exec.Consensus

open Dregg2
open Dregg2.World (Vote BlockId votersFor quorumReached committedByQuorum)

universe u

/-! ## 1. The network-ordering cell.

A `NetCell` is the executable record of "a turn (block id) as observed by the network at a
given round, annotated with the finality tier it has reached". It is the *cell* the two
portals meet on: `World`'s vote count produces the `committed`/`tier` evidence, `Finality`'s
lattice orders the `tier`.

We model the quorum-finality classifier directly: a block whose distinct-voter count meets
`cfg.threshold` (the lifted `½(n+f)`) is a **BFT-final** turn — tier `Tier.bft`, the τ-BFT
quorum tier of the §2.2 ladder. A block below threshold is at most causal (`Tier.causal`,
the never-blocking add-a-block tier). `tierOfVotes` is that classifier. -/

/-- **The finality tier a network turn has earned from its votes.** The classifier of the
§2.2 ladder restricted to the two tiers the bare quorum count can decide: a block whose
distinct-voter count meets the lifted `½(n+f)` threshold (`quorumReached`) has a τ-BFT
quorum, hence `Tier.bft`; otherwise it sits at the never-blocking causal tier `Tier.causal`.
(Tiers 2/4 — ack-threshold and constitutional — need the ack protocol / the constitution,
which the bare vote count does not carry; they are out of this classifier's range by
construction, not by omission.) -/
def tierOfVotes (votes : List Vote) (cfg : Finality.Config) (block : BlockId) :
    Finality.Tier :=
  if quorumReached votes cfg block = true then Finality.Tier.bft else Finality.Tier.causal

/-- **A network-ordering cell.** A turn (`block`) as observed at network round `round`,
the votes the network had delivered by then (`votes`), the group's quorum `config`, and the
finality `tier` the cell carries — *constrained* (the `tier_sound` field) to be exactly the
tier its votes earn. So a `NetCell` value IS, by construction, a turn whose finality
annotation agrees with its network evidence (the executable analogue of
`FinalityRule.commit_canonical`: the tier is not free, it is what the votes justify). -/
structure NetCell where
  /-- The turn / block id this cell orders. -/
  block : BlockId
  /-- The network round at which the observation was taken. -/
  round : Nat
  /-- The votes the `World` network oracle had delivered by `round` (already extracted to
  the `Vote` payload). -/
  votes : List Vote
  /-- The reference-group quorum configuration (`½(n+f)` lifted into `threshold`). -/
  config : Finality.Config
  /-- The finality tier this cell carries. -/
  tier : Finality.Tier
  /-- **Soundness of the annotation:** the carried `tier` is exactly the tier the votes
  earn under the classifier. A `NetCell` cannot lie about its finality. -/
  tier_sound : tier = tierOfVotes votes config block

/-- **`IsBftFinal c`** — the cell is committed at the BFT/quorum tier: its votes meet the
quorum threshold (equivalently, its carried tier is `Tier.bft`). The cell-level realization
of `World.committedByQuorum` AT a tier. -/
def NetCell.IsBftFinal (c : NetCell) : Prop :=
  quorumReached c.votes c.config c.block = true

instance (c : NetCell) : Decidable c.IsBftFinal := by
  unfold NetCell.IsBftFinal; infer_instance

/-! ## 2. The bridge: quorum-committed ⇒ BFT finality tier.

This is the keystone wiring `World.committedByQuorum` to `Finality`'s `Tier.bft`. We give
both directions, plus the form that lands directly on the abstract `committedByQuorum`
predicate so the two portals' "committed" notions are *literally the same set* on the cell.
-/

/-- The carried tier is `Tier.bft` exactly when the cell is BFT-final (unfold the
classifier + the soundness field). The annotation and the vote evidence coincide. -/
theorem NetCell.tier_eq_bft_iff (c : NetCell) :
    c.tier = Finality.Tier.bft ↔ c.IsBftFinal := by
  rw [c.tier_sound, tierOfVotes, NetCell.IsBftFinal]
  by_cases h : quorumReached c.votes c.config c.block = true
  · simp [h]
  · simp [h]

/-- **`quorum_reaches_bft_tier` (PROVED — KEYSTONE).** A turn that is BFT-final (its
distinct-voter count meets the lifted `½(n+f)` quorum) inhabits the BFT/quorum finality
tier of the `Finality` lattice: its carried `Tier` is exactly `Tier.bft`. This is the
portal join — the `World` notion "a quorum of votes was received" and the `Finality` notion
"committed at the τ-BFT tier" *coincide* on a `NetCell`. Proved from the `tier_sound` field
+ the classifier definition; no sorry, kernel-clean. -/
theorem quorum_reaches_bft_tier (c : NetCell) (h : c.IsBftFinal) :
    c.tier = Finality.Tier.bft :=
  (c.tier_eq_bft_iff).mpr h

/-- **The same bridge stated on the abstract `Finality.Committed`.** For a `World`-driven
extraction `votesOf`, if `World.committedByQuorum` holds for the block at the cell's round
*and the cell's votes ARE that round's extracted votes*, then the cell's tier is `Tier.bft`.
This is the literal identification: `World`'s `committedByQuorum` (the abstract
`Finality.Committed BlockId` instance) ⇒ the cell sits at the Finality `bft` tier. So the
two "committed" predicates name the same set at tier `bft`. -/
theorem committedByQuorum_reaches_bft_tier {Msg : Type} [World.World Msg]
    (votesOf : List Msg → List Vote) (c : NetCell)
    (hvotes : c.votes = votesOf (World.World.recv c.round))
    (hcommit : committedByQuorum votesOf c.round c.config c.block) :
    c.tier = Finality.Tier.bft := by
  apply quorum_reaches_bft_tier
  -- `committedByQuorum` unfolds to `quorumReached (votesOf (recv round)) cfg block = true`;
  -- rewrite the cell's votes to that and we are done.
  unfold committedByQuorum at hcommit
  rw [NetCell.IsBftFinal, hvotes]
  exact hcommit

/-- **Below quorum ⇒ NOT BFT-final (the honest negative).** A cell whose vote count does
*not* meet the threshold carries `Tier.causal`, strictly below `Tier.bft` — there is no
silent over-claim of finality. Confirms the classifier is a genuine gate, not a constant. -/
theorem below_quorum_not_bft (c : NetCell) (h : ¬ c.IsBftFinal) :
    c.tier = Finality.Tier.causal ∧ c.tier < Finality.Tier.bft := by
  rw [NetCell.IsBftFinal] at h
  have ht : c.tier = Finality.Tier.causal := by
    rw [c.tier_sound, tierOfVotes]; simp [h]
  refine ⟨ht, ?_⟩
  rw [ht]
  -- causal.rank = 1 < 3 = bft.rank
  show Finality.Tier.causal.rank < Finality.Tier.bft.rank
  decide

/-! ## 3. Monotonicity / no-downgrade of the net cell's finality.

Two complementary statements, both rejecting a downgrade:
  • `net_no_downgrade` rides `Finality.no_downgrade` (≡ `World.world_no_downgrade`) over the
    cell's finalization-event run: along ANY sequence of re-finalization events the tier
    only keeps-or-strengthens.
  • `finality_monotone_on_net` is the *direct cell-level* statement under the network's
    append-only delivery: re-observing the same block at a later round (more votes) cannot
    lower its tier.
-/

/-- **`net_no_downgrade` (PROVED — KEYSTONE).** The finality of a network cell never
downgrades along its finalization-event run. We model the cell's commit history as an
`Execution.Run Finality.finalitySystem` over the carried `Tier` (each event may only
keep-or-strengthen the tier, per `finalitySystem.Step = (· ≤ ·)`); the endpoint tier is no
weaker than the start tier. A thin relay of `Finality.no_downgrade` (equivalently
`World.world_no_downgrade`) onto the `NetCell` tier. Kernel-clean (rides a `sorry`-free
lemma). -/
theorem net_no_downgrade {t₀ t : Finality.Tier}
    (hrun : Execution.Run Finality.finalitySystem t₀ t) : t₀ ≤ t :=
  Finality.no_downgrade hrun

/-- The same no-downgrade stated via the `World` relay (definitionally `net_no_downgrade`),
recorded to make the portal provenance explicit: the network can deliver more votes, advance
the clock, re-run leader election — never downgrade a value's finality. -/
theorem net_no_downgrade_via_world {Msg : Type} [World.World Msg] {t₀ t : Finality.Tier}
    (hrun : Execution.Run Finality.finalitySystem t₀ t) : t₀ ≤ t :=
  World.world_no_downgrade (Msg := Msg) hrun

/-- **`finality_monotone_on_net` (PROVED — KEYSTONE).** The direct cell-level monotonicity:
take a cell `c₁` and a later cell `c₂` for the *same block and config*, where `c₂`'s votes
are a superlist of `c₁`'s (the network's append-only delivery: `recv` only adds). Then
`c₂`'s tier is no weaker than `c₁`'s. Once a turn reaches a finality tier via quorum it
stays there as the network log grows — the no-downgrade *safety* property at the cell level.
Proved by case-split on whether `c₁` had a quorum: if it did, `quorum_monotone` keeps it
(both at `bft`); if not, `c₁` is at `causal`, the bottom of the range, so anything is ≥. -/
theorem finality_monotone_on_net (c₁ c₂ : NetCell)
    (hblock : c₁.block = c₂.block) (hconfig : c₁.config = c₂.config)
    (hgrow : List.Sublist c₁.votes c₂.votes) :
    c₁.tier ≤ c₂.tier := by
  by_cases hq : c₁.IsBftFinal
  · -- c₁ is bft; quorum survives ⇒ c₂ is bft; bft ≤ bft.
    have h1 : c₁.tier = Finality.Tier.bft := quorum_reaches_bft_tier c₁ hq
    have hq2 : c₂.IsBftFinal := by
      rw [NetCell.IsBftFinal, ← hblock, ← hconfig]
      exact World.quorum_monotone hgrow c₁.config c₁.block hq
    have h2 : c₂.tier = Finality.Tier.bft := quorum_reaches_bft_tier c₂ hq2
    rw [h1, h2]
  · -- c₁ is causal (rank 1) ⇒ ≤ anything.
    have h1 := (below_quorum_not_bft c₁ hq).1
    rw [h1]
    show Finality.Tier.causal.rank ≤ c₂.tier.rank
    cases c₂.tier <;> decide

/-- **`quorum_grows_preserves_finality` (PROVED — KEYSTONE).** Adding more replica
observations only RAISES or HOLDS the tier, never lowers it: a cell `c'` whose votes are a
superlist of an already-BFT-final cell `c` (same block/config) is itself BFT-final, so its
tier equals `c`'s (both `bft`). The "growing the quorum holds the tier" guarantee. A direct
corollary of `World.quorum_monotone`; kernel-clean. -/
theorem quorum_grows_preserves_finality (c c' : NetCell)
    (hblock : c.block = c'.block) (hconfig : c.config = c'.config)
    (hgrow : List.Sublist c.votes c'.votes) (hfinal : c.IsBftFinal) :
    c'.tier = c.tier := by
  have hc : c.tier = Finality.Tier.bft := quorum_reaches_bft_tier c hfinal
  have hf' : c'.IsBftFinal := by
    rw [NetCell.IsBftFinal, ← hblock, ← hconfig]
    exact World.quorum_monotone hgrow c.config c.block hfinal
  rw [hc, quorum_reaches_bft_tier c' hf']

/-- **The round-indexed form (PROVED).** Riding `World.committedByQuorum_mono`: if a block
is `committedByQuorum` at round `r`, it is still committed at any later round `r' ≥ r` (for a
sublist-respecting `votesOf`), so its finality tier holds. This is the network-time version
of `quorum_grows_preserves_finality` — the network advancing the round cannot un-finalize. -/
theorem committed_holds_along_rounds {Msg : Type} [World.World Msg]
    (votesOf : List Msg → List Vote)
    (hvotesOf : ∀ {m₁ m₂ : List Msg}, List.Sublist m₁ m₂ →
      List.Sublist (votesOf m₁) (votesOf m₂))
    {r r' : Nat} (hrr : r ≤ r') (cfg : Finality.Config) (block : BlockId)
    (hc : committedByQuorum votesOf r cfg block) :
    committedByQuorum votesOf r' cfg block :=
  World.committedByQuorum_mono votesOf hvotesOf hrr cfg block hc

/-! ## 4. Cross-tier join on the net cell.

A turn observed at two tiers (e.g. a tier-1 fast-path cell touched in the same turn as a
tier-3 BFT cell) settles at the `max` of the two — the stronger requirement dominates. We
instantiate `Finality.commit_at_join_of_tiers` directly on the `NetCell` tiers.
-/

/-- **`cross_tier_join_on_net` (PROVED — KEYSTONE).** A turn observed across the tiers of a
nonempty list of net cells commits at the `crossTierJoin`-fold (`max`) of their tiers, and —
given a join-tier rule that has committed the block — that join tier dominates every cell's
tier and the block is canonical at it. A direct instantiation of
`Finality.commit_at_join_of_tiers` over the `NetCell` tier list (`cells.map (·.tier)`). The
stronger finality requirement of any touched cell swallows the weaker ones (a tier-1 cell
touched with a tier-3 cell inherits tier-3 for the turn). -/
theorem cross_tier_join_on_net {H : Type u}
    (cells : List NetCell) (hne : cells ≠ [])
    (joinTier : Finality.Tier)
    (hjoin : joinTier =
      (cells.map (·.tier)).foldr Finality.crossTierJoin (cells.map (·.tier)).head!)
    (rule : Finality.FinalityRule H) (hrule : rule.tier = joinTier)
    (h : H) (hcommit : rule.committed h) :
    (∀ c ∈ cells, c.tier ≤ joinTier) ∧ rule.canonical h := by
  -- Instantiate the Finality lemma on the projected tier list, then transport the
  -- per-tier conclusion back to a per-cell one.
  have hmapne : cells.map (·.tier) ≠ [] := by
    simpa [List.map_eq_nil_iff] using hne
  obtain ⟨hdom, hcanon⟩ :=
    Finality.commit_at_join_of_tiers (cells.map (·.tier)) hmapne joinTier hjoin rule hrule h
      hcommit
  refine ⟨?_, hcanon⟩
  intro c hc
  exact hdom c.tier (List.mem_map_of_mem hc)

/-! ## 5. The Byzantine-safety / GST-liveness frontier — cited, not re-stated.

The two DEEP theorems are genuinely open research; they need an adversary model (which
voters are Byzantine), a conflict relation on blocks, and a partial-synchrony / GST bound —
none of which the bare `World` interface commits to. `World.lean` already states them as
honest `sorry`'d obligations; this module does NOT attempt them and does NOT re-introduce a
`sorry`. We name the existing OPEN theorems here so the frontier is explicit:

  • `Dregg2.World.quorum_intersection_safety_OPEN` — two quorums for conflicting blocks
    must intersect (the `n > 3f` BFT-safety seed). OPEN: needs the honest-set / conflict
    model.
  • `Dregg2.World.liveness_after_gst_OPEN` — after GST some block's quorum forms (τ-BFT
    progress). OPEN: needs the GST + honest-supermajority model.

-- OPEN: a *cell-level* Byzantine safety theorem ("no two `NetCell`s for conflicting blocks
-- are both `IsBftFinal` under an honest majority") would be the natural next obligation on
-- this cell. It is NOT provable here for the same reason as `quorum_intersection_safety_OPEN`
-- (no adversary/honesty model on `Vote`), so it is deliberately left unstated rather than
-- stubbed with a `sorry`. It belongs with the τ-BFT protocol layer, not the ordering cell.
-/

/-! ## 6. A reference cell + `#eval` demos.

Built over `World.Reference` (the trivial lawful `World` over `Msg = Vote`): its
`fixedVotes` schedule delivers voters 0,1,2 (and a duplicate 0) for block 7. With a config
whose `threshold = 3`, round 3 reaches quorum; round 2 does not. We `mkNetCell` from the
reference world and demonstrate the three headline behaviours. -/

/-- A config with three participants and a commit threshold of 3 (the lifted majority). -/
def demoCfg : Finality.Config := ⟨3, 0, 3⟩

/-- Build a `NetCell` from the reference `World` at a round (votes := what `recv` delivered;
tier := the classifier's verdict, so `tier_sound` holds by `rfl`). -/
def mkNetCell (round : Nat) (block : BlockId) : NetCell where
  block := block
  round := round
  votes := World.World.recv (Msg := World.Reference.M) round
  config := demoCfg
  tier := tierOfVotes (World.World.recv (Msg := World.Reference.M) round) demoCfg block
  tier_sound := rfl

/-- Round 2: only voters 0,1 delivered for block 7 ⇒ below threshold 3 ⇒ NOT BFT-final. -/
def cellAtRound2 : NetCell := mkNetCell 2 7
/-- Round 3: voters 0,1,2 delivered for block 7 ⇒ meets threshold 3 ⇒ BFT-final. -/
def cellAtRound3 : NetCell := mkNetCell 3 7
/-- Round 4: an extra (duplicate-voter) vote delivered ⇒ quorum HELD ⇒ still BFT-final. -/
def cellAtRound4 : NetCell := mkNetCell 4 7

-- DEMO 1 — a turn below quorum is NOT BFT-final (tier is the never-blocking causal tier).
#eval (cellAtRound2.tier, decide cellAtRound2.IsBftFinal)
-- expected: (Dregg2.Finality.Tier.causal, false)

-- DEMO 2 — reaching quorum makes the turn BFT-final (tier rises to the τ-BFT tier).
#eval (cellAtRound3.tier, decide cellAtRound3.IsBftFinal)
-- expected: (Dregg2.Finality.Tier.bft, true)

-- DEMO 3 — growing the quorum (round 4, more votes) HOLDS the BFT tier (no downgrade).
#eval (cellAtRound4.tier, decide cellAtRound4.IsBftFinal)
-- expected: (Dregg2.Finality.Tier.bft, true)

-- DEMO 4 — the tier order witnesses the rise then hold: causal < bft = bft.
#eval (decide (cellAtRound2.tier < cellAtRound3.tier),
       decide (cellAtRound3.tier ≤ cellAtRound4.tier))
-- expected: (true, true)

/-! ## 7. Axiom-hygiene tripwires.

`#assert_axioms` on each genuinely-closed keystone. These FAIL the build if any depends on a
`sorryAx`. ALL of the keystones below ride only `sorry`-free lemmas (`Finality.no_downgrade`,
`World.quorum_monotone`, `World.committedByQuorum_mono`, `Finality.commit_at_join_of_tiers`
are all themselves proved without `sorry`), so they are kernel-clean. We pin NONE of the
`…_OPEN` theorems (we never touch them; they live in `World.lean`). -/

#assert_axioms quorum_reaches_bft_tier
#assert_axioms committedByQuorum_reaches_bft_tier
#assert_axioms below_quorum_not_bft
#assert_axioms net_no_downgrade
#assert_axioms net_no_downgrade_via_world
#assert_axioms finality_monotone_on_net
#assert_axioms quorum_grows_preserves_finality
#assert_axioms committed_holds_along_rounds
#assert_axioms cross_tier_join_on_net
#assert_axioms NetCell.tier_eq_bft_iff

end Dregg2.Exec.Consensus
