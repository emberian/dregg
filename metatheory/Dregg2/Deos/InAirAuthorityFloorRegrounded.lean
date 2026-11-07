/-
# `Dregg2.Deos.InAirAuthorityFloorRegrounded` — the `FloorDigestBinds` consumers RE-GROUNDED off the
FALSE-AS-NAMED injective felt-digest floor onto a REAL collision game carrying an explicit `Eff`.

## The bug this closes (VACUITY-SWEEP FINDING 2, the `FloorDigestBinds` site)

`InAirAuthorityDigestGadget.FloorDigestBinds hash := ∀ l l' : List ℤ, hash l = hash l' → l = l'` is
stated as **injectivity** of the Option-B felt-domain floor digest — literally the same predicate
shape as `StateCommit.compressNInjective`, which `HashFloorHonesty` ALREADY proves FALSE. `List ℤ` is
INFINITE; the deployed `hash_many` lands in ONE BabyBear felt (`p = 2013265921`), so its range is
FINITE. By pigeonhole the floor is **FALSE at deployed parameters** (§1,
`floorDigestBinds_false_of_finite_range` / `floorDigestBinds_false_babyBear`), and all four consumers
conditioned on it — `gentian_selector_forced_discharged`, `gentian_settle_forced_discharged`,
`gentian_partial_unsat_discharged`, `gentian_phantom_unsat_discharged` — are **VACUOUSLY TRUE** at
real parameters. `#assert_axioms` is blind: the gadget's proofs are clean; the HYPOTHESIS is the flaw.

⚑ **The file states the bound that refutes its own floor.** Every one of those four consumers already
carries `hcanon : ∀ c, 0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < 2013265921`. The deployed felt range
is right there in the same signature — the premise of `floorDigestBinds_false_babyBear` is a
hypothesis the carrier already assumes about the very felts it digests.

## The re-grounding (the `PreRotationKeySetRegrounded` pattern)

  * **§1 — FALSE AS NAMED.** The counting core (`HashFloorHonesty.not_injective_of_finite_range`)
    fires on `FloorDigestBinds` directly; `floorDigestBinds_false_babyBear` is the deployed form, fed
    by `HashFloorHonesty.finite_range_of_field_bound` — already stated for exactly `List ℤ → ℤ`,
    which is exactly this carrier's type.
  * **§2 — the KEYED family.** `FloorDigestDeployment` bundles the deployed `hash_many` floor digest
    with its domain-separation tag space (the effective key — the standard keyed-from-unkeyed model)
    and the floor the `B_AUTHORITY_DIGEST` limb pre-commits to at each sampled instance.
    `floorDigestFamily` lifts it to a `HashFloorHonesty.KeyedHashFamily`;
    `deployed_hash_is_family_instance` pins FAITHFULNESS — the game is about the function the chip
    computes.
  * **§3 — the ALTERNATE-FLOOR ATTACK GAME.** `gentian_selector_forced_discharged`'s docstring says
    the forger "can dodge NEITHER by an alternate witnessed floor ... NOR by `sel = 0`". The
    alternate-floor dodge is put IN the win relation: handed a sampled tag, the adversary outputs a
    floor and WINS iff it is NOT the committed one yet its digest HITS THE LIMB THE DEPLOYED TRACE
    PUBLISHES at the real `gentianAuthDigestCol` column, read through the real `envAt`. The win
    relation therefore names the deployed gadget, not a restatement of the collision relation —
    and `limb_eq_witnessed_digest_of_sat` PROVES that limb is the very value the gadget's poseidon2
    chip lookup + `gentianRecomputeBindGate` force on a satisfying trace.
  * **§4 — THE REDUCTION.** `alternateFloorToCollisionFinder` pairs the presented floor against the
    committed one; `alternate_wins_imp` proves win-preservation by TRANSPORTING the limb-hit through
    the limb binding `hcommitLimb` into a genuine digest collision; `alternate_adv_le` is the
    advantage inequality by `winProb_le_of_imp`.
  * **§5 — the RE-GROUNDED CONSUMERS.** The Boolean "the alternate-floor dodge is IMPOSSIBLE" becomes
    "impossible EXCEPT with negligible probability" — which is what a real felt hash can actually
    deliver, and what the FALSE injective floor was standing in for.

## ⚑ SCOPE — exactly which leg this re-grounds, and which it does NOT

`gentian_selector_forced_discharged` rests on THREE named hypotheses. This module re-grounds **one**:

  * `hCR : FloorDigestBinds hash` — the **CR leg**, the alternate-floor dodge. RE-GROUNDED here,
    onto `Hard (floorCollisionGame D) Eff` via the reduction.
  * `hChip : ChipTableSound hash (t.tf .poseidon2)` — the **chip-table-faithfulness leg**. NOT
    touched. It is a separate floor (does the poseidon2 chip table actually compute `hash`?) with its
    own shape and its own repair path; nothing here says anything about it.
  * `hcommitLimb : (envAt t i).loc gentianAuthDigestCol = hash committedFloor` — the **wide-commit
    binding**. NOT touched. It is a binding assumption about the rotated limb, discharged (or not)
    upstream by the wide-commit absorption argument, not by any hash floor.

So: the gadget keystone is NOT wholly re-grounded by this file. Its CR leg is. Saying otherwise would
be the exact `Describe-At-CURRENT-Resolution` sin the sweep exists to catch.

## ⚑ RESIDUAL — what the attack game does and does NOT read off the deployed gadget

Stated at CURRENT resolution, not intended:

  * **It DOES** read the attacked value out of a real `VmTrace` — `digestLimb t` is literally
    `(envAt (D.trace t) (D.row t)).loc gentianAuthDigestCol`, the real column through the real `envAt`
    — and `limb_eq_witnessed_digest_of_sat` proves, from `Satisfied2` on the real
    `gentianGadgetDescriptor` plus `ChipTableSound`, that this limb equals the digest of the trace's
    witnessed floor columns, by composing the gadget's OWN deployed levers (`recompute_discharged`
    and the `gentianRecomputeBindGate` gate). So the game's target is the gadget's object.
  * **It does NOT** carry `Satisfied2` inside the win relation. It cannot: `Game.winsDec` demands a
    DECIDABLE win event and `Satisfied2` is not decidable. Satisfaction therefore enters as the
    hypothesis of `limb_eq_witnessed_digest_of_sat`, beside the game, rather than within it.
  * **`hcommitLimb` is a structure FIELD, not a discharged fact.** The deployment ASSERTS that the
    published limb is the committed floor's digest. That is the gadget keystone's own third
    hypothesis, held fixed, and the reduction transports through it — it is not proved here, and this
    file makes no claim to prove it.
  * **The trace is a deployment field, not a live prover output.** `D.trace` is quantified over, so
    the bound holds for every trace family the deployment names; no `VmTrace` produced by the Rust
    prover is exhibited anywhere in this file.

## ⚑ THE `Eff` PARAMETER IS THE WHOLE HONESTY, AND IT IS UNDISCHARGED

`FloorGames` §2 (`hard_top_iff_solvableFrac_negl`): at the UNRESTRICTED adversary class a game floor IS
the existence floor, so it is FALSE wherever collisions exist — and §1 proves they exist at the
deployed felt digest. §7 instantiates both poles at THIS carrier:
`floorDigest_floor_top_false_of_compressing` / `_babyBear` (`Eff := ⊤` is FALSE at deployed
parameters) and `floorDigest_floor_bot_vacuous` (`Eff := ⊥` is vacuous). So `Eff` is a PARAMETER, in
the open, at every use site: this tree has no cost model (`FloorGames` §8), and inventing a shallow
imitation would be another costume. `hEff` is UNDISCHARGED; naming it is the repair.

## Non-fake

The floor is REFUTABLE (`brokenFloorDigest_floor_top_false`: a constant felt digest has a finder
winning at every tag, advantage `1`) and the reduction is LOAD-BEARING (§6's canary: the keystone does
NOT follow from the floor applied at some OTHER finder). The OLD `FloorDigestBinds` consumers are KEPT
untouched in `InAirAuthorityDigestGadget`; siblings ADDED here. `#assert_all_clean`; no `sorry`, no
fresh `axiom`.

## Coordination

This is the felt-domain Option-B floor-digest lane. The key-set carrier is
`Apps.PreRotationKeySetRegrounded`; `RosterCR` is `Circuit.CouncilRosterRegrounded`; the
STARK/FRI/Merkle hash consumers are `Circuit.FloorRegroundedConsumers` / `Circuit.Poseidon2KeyedBridge`.
-/
import Dregg2.Deos.InAirAuthorityDigestGadget
import Dregg2.Circuit.HashFloorHonesty
import Dregg2.Crypto.FloorGames
import Dregg2.Crypto.RomCarrierSites

namespace Dregg2.Deos.InAirAuthorityFloorRegrounded

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff)
open Dregg2.Deos.InAirAuthorityDigestSelector
  (GENTIAN_WIT_DIGEST_COL gentianAuthDigestCol gentianGates gentianRecomputeBindGate)
open Dregg2.Deos.InAirAuthorityDigestGadget
  (FloorDigestBinds FLOOR0_COL FLOOR1_COL gentianGadgetDescriptor gentianGate_mem_gadget
   gadget_gate_holds recompute_discharged)
open Dregg2.Circuit.HashFloorHonesty
  (KeyedHashFamily CollisionFinder collisionAdv
   not_injective_of_finite_range finite_range_of_field_bound)
open Dregg2.Crypto.ProbCrypto (winProb winProb_top winProb_bot winProb_le_of_imp negl_of_le)
open Dregg2.Crypto.ConcreteSecurity (Negl Ensemble negl_zero not_negl_one)
open Dregg2.Crypto.FloorGames
  (Game Adversary gameAdv gameAdv_mem_unit Hard hard_bot_vacuous not_hard_top_of_always_solvable
   HashCRHardQuant hashCRHardQuant_top_of_injective)

set_option autoImplicit false

/-! ## §1 — FALSE AS NAMED: the injective `FloorDigestBinds` floor is refuted by the deployed digest.

`FloorDigestBinds hash` IS `Function.Injective hash` on the INFINITE `List ℤ` — the identical
predicate `HashFloorHonesty` already refutes for `Poseidon2SpongeCR` and `compressNInjective`. The
deployed Option-B floor digest is `hash_many` into ONE BabyBear felt, so its range is finite and the
counting core fires. No felt collision need be exhibited; cardinality suffices, and is the honest
statement. -/

/-- **TOOTH — `FloorDigestBinds` is FALSE for any range-bounded felt digest.** Literally the counting
core: the floor IS injectivity on `List ℤ`, which is infinite, while a real digest's range is finite.
Stated in the same shape as its flagged siblings
(`HashFloorHonesty.poseidon2SpongeCR_false_of_finite_range`,
`HashFloorHonesty.compressNInjective_false_of_finite_range`) — this carrier is the third instance of
the same predicate, and it is false for the same reason. -/
theorem floorDigestBinds_false_of_finite_range (hash : List ℤ → ℤ)
    (hfin : (Set.range hash).Finite) : ¬ FloorDigestBinds hash :=
  fun hCR => not_injective_of_finite_range hash hfin (fun l l' h => hCR l l' h)

/-- **TOOTH (deployed form) — `FloorDigestBinds` is FALSE at the deployed BabyBear felt digest.** A
digest whose output is a genuine BabyBear field element (`0 ≤ · < p`, `p = 2³¹ − 2²⁷ + 1`) — i.e. every
real `hash_many` Option-B floor commitment, the object the gadget's own docstring points at ("the
felt-domain digest of the cell's required-tag floor") — REFUTES the floor.

⚑ The refuting bound is ALREADY IN THE CONSUMERS' SIGNATURES: `gentian_selector_forced_discharged`
carries `hcanon : ∀ c, 0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < 2013265921`. The file states the
felt range that refutes its own floor. So the floor is not merely un-proven at the deployed hash; it is
provably FALSE there, and every `FloorDigestBinds` consumer is vacuous at real parameters. -/
theorem floorDigestBinds_false_babyBear (hash : List ℤ → ℤ)
    (hb : ∀ l, 0 ≤ hash l ∧ hash l < (2013265921 : ℤ)) : ¬ FloorDigestBinds hash :=
  floorDigestBinds_false_of_finite_range hash (finite_range_of_field_bound hash _ hb)

/-- **THE COLLISION THE FALSITY EXHIBITS.** A range-bounded felt digest has, at every parameter, a
genuine collision — two DISTINCT floors with equal digests. This is the counting core in the positive
form the game floors below consume: it is what makes the `⊤`-class floor false (§7), and therefore what
makes the `Eff` parameter load-bearing rather than decorative. -/
theorem exists_collision_of_finite_range (hash : List ℤ → ℤ) (hfin : (Set.range hash).Finite) :
    ∃ p : List ℤ × List ℤ, p.1 ≠ p.2 ∧ hash p.1 = hash p.2 := by
  by_contra hno
  push_neg at hno
  refine not_injective_of_finite_range hash hfin (fun a b hab => ?_)
  by_contra hne
  exact hno (a, b) hne hab

/-! ## §2 — the KEYED family: domain separation is the key.

The deployed `hash_many` is a FIXED unkeyed function; its effective key is the domain-separation tag
the chip absorbs ahead of the floor felts. Modelling that tag as the key is the standard
keyed-from-unkeyed treatment (`Poseidon2KeyedBridge` §1-§2) and is what stops the "hardcode a known
collision" degeneracy that collapses an unkeyed floor. -/

/-- **The deployed Option-B floor-digest scheme.** `hash` is the tag-keyed felt-domain floor digest
(the deployed `hash_many` at each domain-separation tag); `Tag` is the finite, inhabited tag space the
CR game samples; `committedFloor t` is the required-tag floor the `B_AUTHORITY_DIGEST` limb commits to
at the sampled instance `t` — the `committedFloor` argument of `gentian_selector_forced_discharged`;
`deployedTag` is the tag the cell computes.

⚑ The instance also carries the DEPLOYED TRACE (`trace t`) and the attacked row (`row t`), so that the
attack game below can be stated about the value the trace actually PUBLISHES at the real
`gentianAuthDigestCol` column — read out through the real `envAt` — rather than about a restatement of
the collision relation. `hcommitLimb` is the gadget keystone's own `hcommitLimb` hypothesis, carried as
a NAMED FIELD: it is the leg this file explicitly does NOT re-ground (see the header), and naming it
here keeps it visible rather than dissolving it. -/
structure FloorDigestDeployment where
  /-- The domain-separation tag space (the effective key the CR game samples). -/
  Tag : Type
  /-- The tag space is finite (the game samples a uniform tag). -/
  tagFintype : Fintype Tag
  /-- The tag space is inhabited. -/
  tagNonempty : Nonempty Tag
  /-- The tag-keyed felt-domain floor digest — the deployed `hash_many` at each tag. -/
  hash : Tag → List ℤ → ℤ
  /-- The floor the committed authority-digest limb commits to at the sampled instance. -/
  committedFloor : Tag → List ℤ
  /-- The specific domain-separation tag the gadget's chip lookup computes at. -/
  deployedTag : Tag
  /-- The DEPLOYED trace at the sampled instance — the witness the light client is handed. -/
  trace : Tag → VmTrace
  /-- The attacked main row of that trace. -/
  row : Tag → Nat
  /-- **`hcommitLimb`, as a named field.** The published `B_AUTHORITY_DIGEST` limb IS the committed
  floor's digest — the gadget keystone's third hypothesis verbatim. NOT discharged here; carried. -/
  hcommitLimb : ∀ t : Tag,
    (envAt (trace t) (row t)).loc gentianAuthDigestCol = hash t (committedFloor t)

/-- **The published authority-digest limb** at the sampled instance: the value the deployed trace
carries at the real `gentianAuthDigestCol` column, read through the real `envAt`. This — not a
restatement of `hash (committedFloor t)` — is what the attack game below makes the adversary hit. -/
def FloorDigestDeployment.digestLimb (D : FloorDigestDeployment) (t : D.Tag) : ℤ :=
  (envAt (D.trace t) (D.row t)).loc gentianAuthDigestCol

/-- **`floorDigestFamily D`** — the deployed felt-domain floor digest lifted to a `KeyedHashFamily`,
keyed by its domain-separation tag, with `Input := List ℤ` and `Out := ℤ` — exactly the carrier's own
types. This is the object the collision floor `FloorGames.HashCRHardQuant (floorDigestFamily D) Eff` is
stated at for the real digest. -/
def floorDigestFamily (D : FloorDigestDeployment) : KeyedHashFamily where
  Key := fun _ => D.Tag
  Input := List ℤ
  Out := ℤ
  H := fun _ t l => D.hash t l
  keyFintype := fun _ => D.tagFintype
  keyNonempty := fun _ => D.tagNonempty
  inputDecEq := inferInstance
  outDecEq := inferInstance

/-- **FAITHFULNESS.** The deployed FIXED digest IS the keyed family's instance at the deployed tag — a
definitional equality, no idealization. So the collision game below is a game about the very function
the gadget's poseidon2 chip lookup computes. -/
theorem deployed_hash_is_family_instance (D : FloorDigestDeployment) (n : ℕ) :
    D.hash D.deployedTag = (floorDigestFamily D).H n D.deployedTag := rfl

/-! ⚑ **DELETED 2026-07-28 — `floorDigestFamily_CR_of_floorDigestBinds`.** It bridged the injective
`FloorDigestBinds` floor to `HashFloorHonesty.CollisionResistant (floorDigestFamily D)`, and the
argument in its docstring was "the OLD floor was STRICTLY STRONGER than the honest computational
floor, so nothing is lost re-grounding". That argument is FALSE, and both ends of the bridge are
refuted.

`CollisionResistant F` was never a computational floor — it was a SPELLING of
`HashCRHardQuant F (fun _ => True)` that hid the `⊤`, and it is deleted in favour of writing the `⊤`
out. THIS FILE refutes that destination: §7's `floorDigest_floor_top_false_babyBear` proves the
`⊤`-class floor on the very same collision event is FALSE at a BabyBear-bounded digest — i.e. at the
deployed `hash_many` — using nothing but the felt bound the consumers' own `hcanon` already asserts.
And §1 proves the SOURCE empty at those same parameters. A bridge from an empty hypothesis to a
refuted conclusion carries nothing, so it is gone rather than restated.

The honest floor is the one §5's `_advantage_bound` siblings actually consume:
`Hard (floorCollisionGame D) Eff`, with `Eff` a parameter in the open and both its poles priced in §7.
Satisfiability of the `⊤` pole survives below as `floorDigestFamily_CR_of_injective`, recorded with
its price. -/

/-! ## §3 — the floor COLLISION GAME and the ALTERNATE-FLOOR ATTACK GAME, as first-class objects. -/

/-- **THE FLOOR-DIGEST COLLISION GAME.** Instances are sampled domain-separation tags; the adversary
outputs two floors and WINS iff they are a GENUINE collision of the deployed felt digest at that tag —
distinct floors, equal digests. This is the game the floor below quantifies over, with an explicit
adversary class. -/
def floorCollisionGame (D : FloorDigestDeployment) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => List ℤ × List ℤ
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t p => p.1 ≠ p.2 ∧ D.hash t p.1 = D.hash t p.2
  winsDec := fun _ _ _ => inferInstance

/-- **THE PROBLEM IS IN THE STATEMENT** — the win relation unfolds, by `Iff.rfl`, to a genuine
collision of the real deployed felt digest. Not a docstring: the `Prop` itself. -/
theorem floorCollisionGame_wins_iff (D : FloorDigestDeployment) (n : ℕ) (t : D.Tag)
    (p : List ℤ × List ℤ) :
    (floorCollisionGame D).wins n t p ↔ (p.1 ≠ p.2 ∧ D.hash t p.1 = D.hash t p.2) :=
  Iff.rfl

/-- **THE ALTERNATE-FLOOR ATTACK GAME.** `gentian_selector_forced_discharged`'s docstring says the
forger "can dodge NEITHER by an alternate witnessed floor (the recompute lookup + recompute-bind + CR
floor force it equal to the committed floor) NOR by `sel = 0`". This game IS the first dodge, as a win
relation: handed a sampled tag, the adversary outputs a floor and WINS iff it is NOT the committed
floor yet its digest HITS THE LIMB THE DEPLOYED TRACE PUBLISHES at `gentianAuthDigestCol`. Such a floor
rides the recompute chain: the chip lookup digests it, the recompute-bind gate ties that digest to the
published limb, and the decode then reads an escrow requirement out of the WRONG floor — so the
selector is no longer forced.

⚑ Note what the win relation mentions: `D.digestLimb t`, i.e. `(envAt (D.trace t) (D.row t)).loc
gentianAuthDigestCol` — the real column of the real gadget, read through the real `envAt`. It is NOT
`D.hash t (D.committedFloor t)` restated; that the two coincide is `hcommitLimb`, a hypothesis the
reduction must TRANSPORT THROUGH (`alternate_wins_imp`), and `limb_eq_witnessed_digest_of_sat` proves
this limb is the same object the deployed gadget's chip lookup forces. -/
def alternateFloorGame (D : FloorDigestDeployment) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => List ℤ
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t l => l ≠ D.committedFloor t ∧ D.hash t l = D.digestLimb t
  winsDec := fun _ _ _ => inferInstance

/-- **THE PROBLEM IS IN THE STATEMENT (2/2)** — an alternate-floor win is, by `Iff.rfl`, a floor
DIFFERENT from the committed one whose digest nevertheless equals the limb the deployed trace publishes
at `gentianAuthDigestCol`. -/
theorem alternateFloorGame_wins_iff (D : FloorDigestDeployment) (n : ℕ) (t : D.Tag) (l : List ℤ) :
    (alternateFloorGame D).wins n t l ↔
      (l ≠ D.committedFloor t ∧
        D.hash t l = (envAt (D.trace t) (D.row t)).loc gentianAuthDigestCol) :=
  Iff.rfl

/-! ### The limb the game attacks IS the one the deployed gadget forces. -/

/-- Field-faithful lift: two CANONICAL (`0 ≤ · < p`) integers congruent mod `p` are EQUAL. (The
gadget's own `canonEq` is `private`; this is the same three-line fact, not a weakening.) -/
private theorem canonEq {a b : ℤ} (h : a ≡ b [ZMOD 2013265921])
    (ha0 : 0 ≤ a) (hap : a < 2013265921) (hb0 : 0 ≤ b) (hbp : b < 2013265921) : a = b := by
  unfold Int.ModEq at h
  rwa [Int.emod_eq_of_lt ha0 hap, Int.emod_eq_of_lt hb0 hbp] at h

/-- **⚑ FAITHFULNESS — the attacked limb is the object the DEPLOYED GADGET forces.** On a satisfying
gadget trace, against the sound chip table, the published `gentianAuthDigestCol` limb IS the felt
digest of the trace's WITNESSED floor columns — proven by composing the gadget's own deployed levers:
`recompute_discharged` (the poseidon2 chip lookup forces `witDigestCol = hash [F0, F1]`) with the
`gentianRecomputeBindGate` gate (which ties `witDigestCol` to `gentianAuthDigestCol`, field-faithfully
under `hcanon`).

This is what stops `digestLimb` from being an abstracted stand-in: the value the attack game makes the
adversary hit is exactly the value the deployed recompute chain publishes. Hitting it with a floor
`≠ committedFloor` is precisely the step at which `gentian_selector_forced_discharged` invokes `hCR`. -/
theorem limb_eq_witnessed_digest_of_sat (hash : List ℤ → ℤ) (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (gentianGadgetDescriptor legA legB) minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hcanon : ∀ c, 0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < 2013265921) :
    (envAt t i).loc gentianAuthDigestCol
      = hash [(envAt t i).loc FLOOR0_COL, (envAt t i).loc FLOOR1_COL] := by
  -- the chip lookup forces the witnessed-digest column to the felt-floor digest.
  have hwit := recompute_discharged hash legA legB hsat hChip i hi
  -- the recompute-bind gate ties the witnessed digest to the published limb.
  have hbind : (envAt t i).loc GENTIAN_WIT_DIGEST_COL = (envAt t i).loc gentianAuthDigestCol := by
    have h := gadget_gate_holds hash legA legB hsat i hi hnl
      (gentianRecomputeBindGate GENTIAN_WIT_DIGEST_COL gentianAuthDigestCol)
      (gentianGate_mem_gadget legA legB _ (by simp [gentianGates]))
      _ rfl
    simp only [EmittedExpr.eval] at h
    exact canonEq ((gate_modEq_iff (by ring)).mp h) (hcanon _).1 (hcanon _).2 (hcanon _).1 (hcanon _).2
  rw [← hbind, hwit]

/-! ## §4 — THE REDUCTION: an alternate-floor forger IS a floor-digest collision finder. -/

/-- **THE REDUCTION, AS A MAP OF ADVERSARIES.** An alternate-floor forger becomes a floor-digest
collision finder by pairing the floor it PRESENTED against the floor the limb COMMITTED to. This is not
a rename and not a re-indexing: it is the gadget's `hdig` step (`hash witnessedFloor = hash
committedFloor`, forced by the recompute lookup + recompute-bind gate) read as an extractor — the
precise step at which `hCR` is applied in `gentian_selector_forced_discharged`. -/
def alternateFloorToCollisionFinder (D : FloorDigestDeployment)
    (A : Adversary (alternateFloorGame D)) : Adversary (floorCollisionGame D) where
  run := fun n t => (A.run n t, D.committedFloor t)

/-- **⚑ WIN-PRESERVATION — and this IS the CR leg of `gentian_selector_forced_discharged`, at the game
level.** Wherever the alternate-floor forger wins, the extracted pair is a GENUINE collision of the
deployed felt digest. The win hands over `hash presented = digestLimb t` — an equation about the value
the TRACE PUBLISHES, not about `hash committed`; the reduction must TRANSPORT it through the limb
binding `hcommitLimb` (the gadget keystone's own named hypothesis) to land `hash presented = hash
committed`, which with `presented ≠ committed` is the collision. That transport is the deployed step
`gentian_selector_forced_discharged` performs before invoking `hCR`. The crypto content lives in a
proof term, not in a sentence about one. -/
theorem alternate_wins_imp (D : FloorDigestDeployment) (A : Adversary (alternateFloorGame D))
    (n : ℕ) (t : D.Tag) (hwin : (alternateFloorGame D).wins n t (A.run n t)) :
    (floorCollisionGame D).wins n t ((alternateFloorToCollisionFinder D A).run n t) := by
  obtain ⟨hne, hlimb⟩ := hwin
  refine ⟨hne, ?_⟩
  -- TRANSPORT: the forger hit the PUBLISHED limb (`hlimb`); `hcommitLimb` says that limb IS the
  -- committed floor's digest. Composing the two turns a limb-hit into a genuine digest collision.
  exact hlimb.trans (D.hcommitLimb t)

/-- **THE ADVANTAGE INEQUALITY.** The alternate-floor forger's advantage is at most the extracted
collision finder's, at every parameter — both play over the SAME sampled tag space, and every tag the
forger wins the extracted finder wins. A genuine reduction inequality over real game advantages. -/
theorem alternate_adv_le (D : FloorDigestDeployment) (A : Adversary (alternateFloorGame D)) (n : ℕ) :
    gameAdv (alternateFloorGame D) A n
      ≤ gameAdv (floorCollisionGame D) (alternateFloorToCollisionFinder D A) n := by
  refine @winProb_le_of_imp _ (D.tagFintype) _ _ (fun t ht => ?_)
  replace ht := (Adversary.hit_eq_true _ _ _).mp ht
  refine (Adversary.hit_eq_true _ _ _).mpr ?_
  exact alternate_wins_imp D A n t ht

/-! ## §5 — the RE-GROUNDED CONSUMERS.

The Boolean keystones become advantage bounds, derived FROM the collision floor VIA the reduction. The
old statements are kept in `InAirAuthorityDigestGadget`; these are their honest siblings. -/

/-- **⚑ RE-GROUNDED `InAirAuthorityDigestGadget.gentian_selector_forced_discharged` (CR LEG).**

Under the floor-digest collision floor at the game the reduction actually attacks, an alternate-floor
forger whose extracted finder is in the floor's adversary class has NEGLIGIBLE advantage: the Boolean
"the alternate-witnessed-floor dodge is IMPOSSIBLE" becomes "impossible EXCEPT with negligible
probability" — which is what a real felt hash can actually deliver, and what the FALSE injective
`FloorDigestBinds` was standing in for.

⚑ **SCOPE.** This re-grounds the CR leg — the `hCR` step of the keystone, where an alternate witnessed
floor is ruled out. The keystone's OTHER two hypotheses are untouched and remain exactly as they were:
`hChip : ChipTableSound hash (t.tf .poseidon2)` (chip-table faithfulness — a separate floor with its
own repair path) and `hcommitLimb` (the wide-commit binding of `gentianAuthDigestCol`). The gadget
keystone as a whole is NOT re-grounded by this file; one of its three legs is.

Unlike its predecessor this statement is FALSE if you delete the reduction: the conclusion is about the
alternate-floor game, the hypothesis about the collision game, and `alternate_adv_le` is the only
bridge (§6's canary compiles that fact).

⚑ **`hEff` IS UNDISCHARGED AND THAT IS THE HONEST STATE** — the standard "the reduction is efficient"
side condition, a PARAMETER because this tree has no cost model (`FloorGames` §8). The floor's honesty
is exactly its `Eff`'s, and §7 prices both poles: `⊤` makes it FALSE at the deployed felt digest, `⊥`
vacuous. The DISCHARGED successor — on the PROVED keyed-ROM floor, forger an oracle program with
query-counted cost — is §8's `gentian_alternate_floor_binds_rom`. -/
theorem gentian_alternate_floor_advantage_bound (D : FloorDigestDeployment)
    (Eff : Adversary (floorCollisionGame D) → Prop)
    (A : Adversary (alternateFloorGame D))
    (hEff : Eff (alternateFloorToCollisionFinder D A))
    (hcol : Hard (floorCollisionGame D) Eff) :
    Negl (gameAdv (alternateFloorGame D) A) :=
  negl_of_le (fun n => (gameAdv_mem_unit (alternateFloorGame D) A n).1)
    (alternate_adv_le D A) (hcol _ hEff)

/-- **⚑ RE-GROUNDED `gentian_settle_forced_discharged` / `gentian_partial_unsat_discharged` /
`gentian_phantom_unsat_discharged` (CR LEG).** All three downstream consumers take `hCR` and use it
ONLY through `gentian_selector_forced_discharged` — they add no further crypto step (the settle-forcing
is gate arithmetic off the forced selector; the two unsat teeth are `decide` contradictions off the
settle-forcing). So the CR leg of all three is re-grounded by the SAME bound: the alternate-floor dodge
that would break the selector forcing has negligible advantage.

The `Eff` obligation is the same undischarged side condition as above — named, not hidden. Their
`hChip` and `hcommitLimb` legs are likewise untouched. -/
theorem gentian_settle_alternate_floor_advantage_bound (D : FloorDigestDeployment)
    (Eff : Adversary (floorCollisionGame D) → Prop)
    (A : Adversary (alternateFloorGame D))
    (hEff : Eff (alternateFloorToCollisionFinder D A))
    (hcol : Hard (floorCollisionGame D) Eff) :
    Negl (gameAdv (alternateFloorGame D) A) :=
  gentian_alternate_floor_advantage_bound D Eff A hEff hcol

/-! ## §6 — the CANARY: break the reduction and the keystone goes RED. -/

/-- **(CANARY — the keystone does NOT follow from the floor applied at some OTHER finder.)** Strip the
reduction — try to conclude the alternate-floor forger's negligibility from the collision floor applied
at some OTHER finder `B`, NOT the one extracted from the forger — and the proof does not go through:
the floor bounds `B`, and only `alternate_adv_le` connects the EXTRACTED finder to the alternate-floor
game. Under the OLD free hypothesis (`hCR : FloorDigestBinds hash`, hypothesis and conclusion sharing
the same free `hash`) this tooth was unwritable. It compiles now, and reds if a future edit reconnects
the games. -/
example (D : FloorDigestDeployment)
    (Eff : Adversary (floorCollisionGame D) → Prop)
    (A : Adversary (alternateFloorGame D))
    (B : Adversary (floorCollisionGame D)) (hB : Eff B)
    (hcol : Hard (floorCollisionGame D) Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (alternateFloorGame D) A) := hcol B hB)
  trivial

/-- **THE POSITIVE POLE — the RIGHT floor DOES discharge it.** A gate that refuses everything is a
broken keystone, not a fixed one. With the collision floor at the EXTRACTED finder the keystone fires.
Refusal is discrimination only if acceptance still happens. -/
theorem the_repaired_bound_fires_on_the_right_floor (D : FloorDigestDeployment)
    (Eff : Adversary (floorCollisionGame D) → Prop)
    (A : Adversary (alternateFloorGame D))
    (hEff : Eff (alternateFloorToCollisionFinder D A))
    (hcol : Hard (floorCollisionGame D) Eff) :
    Negl (gameAdv (alternateFloorGame D) A) :=
  gentian_alternate_floor_advantage_bound D Eff A hEff hcol

/-! ## §7 — the `Eff` parameter, PRICED: both poles proved at THIS carrier.

`FloorGames` §2 says a game floor at the unrestricted class IS the existence floor. Here is that
theorem instantiated at the deployed felt-domain floor digest, so a reader can price any `Eff` exactly
rather than take the residual on faith. -/

/-- **⚑ (TOOTH — the floor is FALSE at `Eff := ⊤` for the DEPLOYED digest.)** The real content, and the
reason `Eff` is not decoration: a range-bounded felt digest HAS a collision at every tag (§1's counting
core), so the collision game is always solvable, so the floor at the unrestricted adversary class is
FALSE — and every consumer would be vacuous there. `Classical.choice` is the adversary and no
restatement of the win relation can see it coming. This is the price of `hEff`, stated as a theorem
instead of a promise. -/
theorem floorDigest_floor_top_false_of_compressing (D : FloorDigestDeployment)
    (hfin : ∀ t : D.Tag, (Set.range (D.hash t)).Finite) :
    ¬ Hard (floorCollisionGame D) (fun _ => True) :=
  not_hard_top_of_always_solvable (floorCollisionGame D)
    (fun _ => ⟨([], [])⟩)
    (fun _ t => exists_collision_of_finite_range (D.hash t) (hfin t))

/-- **(TOOTH — the deployed BabyBear form of the same.)** A genuine BabyBear felt digest (`0 ≤ · < p`)
refutes the unrestricted-class floor — the deployment the gadget's docstring names is exactly where
`Eff := ⊤` fails.

⚑ Note what supplies the hypothesis: the consumers' OWN `hcanon : ∀ c, 0 ≤ (envAt t i).loc c ∧
(envAt t i).loc c < 2013265921` asserts precisely this felt bound about the columns the digest ranges
over. The signature that carries the floor also carries its refutation. -/
theorem floorDigest_floor_top_false_babyBear (D : FloorDigestDeployment)
    (hb : ∀ (t : D.Tag) (l : List ℤ), 0 ≤ D.hash t l ∧ D.hash t l < (2013265921 : ℤ)) :
    ¬ Hard (floorCollisionGame D) (fun _ => True) :=
  floorDigest_floor_top_false_of_compressing D
    (fun t => finite_range_of_field_bound (D.hash t) _ (fun l => hb t l))

/-- **(TOOTH — the OTHER pole: `Eff := ⊥` is vacuous.)** At the empty adversary class the floor holds
for ANY deployment, including a completely broken felt digest. Recorded HONESTLY: a satisfiability
witness is worth nothing without the refutation beside it, and these two poles together are what make
`Eff` a dial rather than a costume. -/
theorem floorDigest_floor_bot_vacuous (D : FloorDigestDeployment) :
    Hard (floorCollisionGame D) (fun _ => False) :=
  hard_bot_vacuous _

/-! ### The floor is REFUTABLE on a broken deployment (load-bearing, not `True`-shaped). -/

/-- A **broken** floor-digest deployment: the digest IGNORES the floor entirely, so every pair of
distinct floors collides at every tag, and every floor whatsoever hits the published limb. -/
def brokenFloorDigest : FloorDigestDeployment where
  Tag := Unit
  tagFintype := inferInstance
  tagNonempty := inferInstance
  hash := fun _ _ => 0
  committedFloor := fun _ => []
  deployedTag := ()
  trace := fun _ => { rows := [], pub := zeroAsg, tf := fun _ => [] }
  row := fun _ => 0
  hcommitLimb := fun _ => rfl

/-- **(TOOTH — the floor is REFUTABLE.)** The broken deployment's collision game is solvable at every
tag (`[0] ≠ [1]`, both digest to `0`), so it has no unrestricted-class floor. So the floor is a GENUINE
constraint — a broken digest refutes it — not vacuously true. -/
theorem brokenFloorDigest_floor_top_false :
    ¬ Hard (floorCollisionGame brokenFloorDigest) (fun _ => True) :=
  not_hard_top_of_always_solvable (floorCollisionGame brokenFloorDigest)
    (fun _ => ⟨([], [])⟩)
    (fun _ _ => ⟨([0], [1]), by decide, rfl⟩)

/-- **(TOOTH — the ATTACK game is refutable too.)** On the broken deployment the alternate-floor dodge
SUCCEEDS at every tag (`[0] ≠ []` yet both digest to `0`), so the attack game has no unrestricted-class
floor either. The dodge the keystone's CR leg rules out is a real event that a real (broken) digest
admits — the win relation is not `True`-shaped in the other direction. -/
theorem brokenFloorDigest_alternate_top_false :
    ¬ Hard (alternateFloorGame brokenFloorDigest) (fun _ => True) :=
  not_hard_top_of_always_solvable (alternateFloorGame brokenFloorDigest)
    (fun _ => ⟨[]⟩)
    (fun _ _ => ⟨[0], List.cons_ne_nil _ _, rfl⟩)

/-! ### The floor is SATISFIABLE (the connection to the keyed-family treatment). -/

/-- **(TOOTH — the keyed family is SATISFIABLE on an injective deployment.)** A deployment whose per-tag
digest is injective discharges `HashCRHardQuant (floorDigestFamily D) (fun _ => True)` — the floor is
REALIZABLE, unlike the injective `FloorDigestBinds` at deployed parameters. ⚑ The `⊤` is now WRITTEN
OUT in the statement instead of hidden behind the deleted `CollisionResistant`, which makes the price
legible without a lemma: this is the UNRESTRICTED adversary class, which §7's first tooth proves FALSE
at a range-bounded (i.e. real) felt digest. So this witness says only that the family is NOT
COMPRESSING — an injective `List ℤ → ℤ` is not a felt digest. Honest as a non-emptiness check, never
as evidence the deployed `hash_many` satisfies anything. -/
theorem floorDigestFamily_CR_of_injective (D : FloorDigestDeployment)
    (hinj : ∀ t : D.Tag, Function.Injective (D.hash t)) :
    HashCRHardQuant (floorDigestFamily D) (fun _ => True) :=
  hashCRHardQuant_top_of_injective (floorDigestFamily D) (fun _ t => hinj t)

/-! ## §8 — ⚑ THE KEYED-ROM SUCCESSOR: the alternate-floor bound DISCHARGED on the PROVED floor.

§5's `_advantage_bound` siblings are the honest fixed-hash statements, and their `hcol : Hard … Eff`
hypothesis is a PARAMETER with no known non-vacuous instantiation (§7: `⊤` FALSE at the deployed felt
digest, `⊥` vacuous, no cost model). The DISCHARGED successor moves the floor where it is a THEOREM:
the keyed random-oracle model (`Crypto.KeyedRomFloor.keyedRom_hard`, the birthday bound), the forger
an ORACLE PROGRAM with QUERY-COUNTED cost, oracle sampled AFTER the program is fixed
(`Crypto.RomCarrierSites`, the `Exec.SystemRootsBindingReduction` §7 pattern).

⚑ **THE MODELLING STEP, STATED (not smuggled)** — `RomCarrierSites`' header caveat, inherited: the
sampled `H : Tag × Msg → Fin (2 ^ l)` replaces the fixed public `hash_many` (a deliberate labelled
idealisation, NOT a derivation); the digest space is `λ`-growing where the deployed limb is a FIXED
~31-bit BabyBear felt (birthday ≈ `2^15.5` at the deployed width — the felt-width wound). The message
domain is the TRUNCATED deployed shape: floors of at most `m` BabyBear-RANGE felt limbs — the
consumers' own `hcanon` bound — and on those the truncation is LOSSLESS (`floorVec_inj` /
`floorVec_val`). The published limb the forger must hit becomes the PUBLISHED value of the opening
game (`romOpenGame`), exactly the `alternateFloorGame` shape at the sampled oracle; the `hcommitLimb`
transport and the `hChip`/`Satisfied2` legs stay deployed-side, untouched, per the SCOPE header. -/

open Dregg2.Crypto.KeyedRomFloor (KeyedRomFamily)
open Dregg2.Crypto.RomBindingReduction (RomCarrier)
open Dregg2.Crypto.RomCarrierSites
  (flatFamily flatFamily_card_R taggedCarrier BVec bvecOfList bvecOfList_inj romOpenGame RomOpenEff
   romOpenAdv rom_open_binds flat_open_binds constOpenComp constOpen_in_eff constOpen_gameAdv_pos
   constOpen_binds romOpen_forger_excluded babyBearP babyBearP_pos one_lt_babyBearP)
open Dregg2.Crypto.ConcreteSecurity (PolyBounded)

/-- Truncate an IN-RANGE deployed floor (felt limb list) to its `Fin babyBearP` limbs — total on
exactly the floors the deployed gadget can digest (`hcanon`'s bound, verbatim). -/
def floorVec (xs : List ℤ) (hb : ∀ x ∈ xs, 0 ≤ x ∧ x < (babyBearP : ℤ)) :
    List (Fin babyBearP) :=
  xs.pmap (fun x hx => ⟨x.toNat, (Int.toNat_lt hx.1).mpr hx.2⟩) hb

/-- **LIMB-FOR-LIMB FAITHFULNESS** — reading the truncated limbs back as integers IS the deployed
floor; what changed is only WHO evaluates them (the sampled oracle vs the fixed `hash_many`). -/
theorem floorVec_val : ∀ (xs : List ℤ) (hb : ∀ x ∈ xs, 0 ≤ x ∧ x < (babyBearP : ℤ)),
    (floorVec xs hb).map (fun f : Fin babyBearP => ((f.val : ℕ) : ℤ)) = xs
  | [], _ => rfl
  | x :: xs, hb => by
      simp only [floorVec, List.pmap, List.map_cons]
      exact congrArg₂ List.cons (Int.toNat_of_nonneg (hb x (List.mem_cons_self)).1)
        (floorVec_val xs (fun y hy => hb y (List.mem_cons_of_mem x hy)))

@[simp] theorem floorVec_length (xs : List ℤ) (hb : ∀ x ∈ xs, 0 ≤ x ∧ x < (babyBearP : ℤ)) :
    (floorVec xs hb).length = xs.length :=
  List.length_pmap ..

/-- **THE TRUNCATION LOSES NOTHING** — two in-range floors with one truncation are EQUAL. -/
theorem floorVec_inj {xs ys : List ℤ}
    (hbx : ∀ x ∈ xs, 0 ≤ x ∧ x < (babyBearP : ℤ))
    (hby : ∀ y ∈ ys, 0 ≤ y ∧ y < (babyBearP : ℤ))
    (h : floorVec xs hbx = floorVec ys hby) : xs = ys := by
  have hmap := congrArg (List.map (fun f : Fin babyBearP => ((f.val : ℕ) : ℤ))) h
  rwa [floorVec_val, floorVec_val] at hmap

/-- **THE FLOOR-DIGEST KEYED ROM FAMILY** — keyed by the DEPLOYED tag space `D.Tag` (the anchor to
the deployed object), over truncated floors (at most `m` BabyBear-range limbs), with the ideal
`λ`-bit digest. The `hw` obligation is closed by construction. -/
def floorRomFamily (D : FloorDigestDeployment) (tagDec : DecidableEq D.Tag) (m : ℕ) :
    KeyedRomFamily :=
  flatFamily D.Tag D.tagFintype tagDec D.tagNonempty (fun _ => BVec (Fin babyBearP) m)
    (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ => ⟨(⟨0, Nat.succ_pos m⟩, fun _ => none)⟩)

/-- **THE FLOOR-DIGEST CARRIER** — commitment `H (t, floor)`: the authority-digest limb binds the
WHOLE witnessed floor in one query; the embedding is the identity, injective on the nose. -/
def floorRomCarrier (D : FloorDigestDeployment) (tagDec : DecidableEq D.Tag) (m : ℕ) :
    RomCarrier (floorRomFamily D tagDec m) :=
  taggedCarrier _ (fun _ => Unit) (fun _ => BVec (Fin babyBearP) m) (fun _ => inferInstance)
    (fun _ _ v => v) (fun _ _ _ _ h => h)

/-- The alternate-floor game at the sampled oracle: the adversary PUBLISHES a digest limb and
exhibits two DISTINCT truncated floors that BOTH digest to it — `romOpenGame`, the published value IN
the win relation, exactly `alternateFloorGame`'s dodge (presented vs committed floor, one published
`gentianAuthDigestCol` limb) at the sampled oracle. -/
abbrev alternateFloorRomGame (D : FloorDigestDeployment) (tagDec : DecidableEq D.Tag) (m : ℕ) :
    Game :=
  romOpenGame (floorRomFamily D tagDec m) (floorRomCarrier D tagDec m)

/-- **⚑ THE DEPLOYED DODGE IS A WIN OF THE ROM GAME.** A presented floor DIFFERENT from the committed
one, both in-range and truncation-bounded, whose digests BOTH hit one published limb at the sampled
oracle, IS a win — `alternateFloorGame`'s event after the `hcommitLimb` transport, restated at the
sampled oracle with the truncation proved lossless. -/
theorem alternateFloorRom_dodge_is_break (D : FloorDigestDeployment) (tagDec : DecidableEq D.Tag)
    (m : ℕ) (l : ℕ) (H : (alternateFloorRomGame D tagDec m).Inst l) (t : D.Tag)
    {presented committed : List ℤ}
    (hb : ∀ x ∈ presented, 0 ≤ x ∧ x < (babyBearP : ℤ))
    (hb' : ∀ x ∈ committed, 0 ≤ x ∧ x < (babyBearP : ℤ))
    (hl : (floorVec presented hb).length ≤ m) (hl' : (floorVec committed hb').length ≤ m)
    (hne : presented ≠ committed) (limb : Fin (2 ^ l))
    (h1 : H (t, bvecOfList m (floorVec presented hb) hl) = limb)
    (h2 : H (t, bvecOfList m (floorVec committed hb') hl') = limb) :
    (alternateFloorRomGame D tagDec m).wins l H
      (limb, (t, ()), bvecOfList m (floorVec presented hb) hl,
        bvecOfList m (floorVec committed hb') hl') :=
  ⟨fun hc => hne (floorVec_inj hb hb' (bvecOfList_inj hl hl' hc)), h1, h2⟩

/-- **⚑⚑ RE-GROUNDED `gentian_selector_forced_discharged` (CR LEG), DISCHARGED ON THE PROVED FLOOR** —
the keyed-ROM successor of §5's `gentian_alternate_floor_advantage_bound`: every query-bounded
alternate-floor forger has NEGLIGIBLE advantage, in the keyed ROM model of §8's header. Hypotheses: a
polynomial query budget and class membership — nothing refutable. SCOPE unchanged: this is the CR leg
only; `hChip` and `hcommitLimb` stay deployed-side named hypotheses exactly as before. -/
theorem gentian_alternate_floor_binds_rom (D : FloorDigestDeployment) (tagDec : DecidableEq D.Tag)
    (m : ℕ) (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (alternateFloorRomGame D tagDec m))
    (hA : RomOpenEff (floorRomFamily D tagDec m) (floorRomCarrier D tagDec m) Q A) :
    Negl (gameAdv (alternateFloorRomGame D tagDec m) A) :=
  flat_open_binds _ _ _ _ _ _ _ _ _ Q hQ A hA

/-- **⚑ RE-GROUNDED `gentian_settle_forced_discharged` / `gentian_partial_unsat_discharged` /
`gentian_phantom_unsat_discharged` (CR LEG), DISCHARGED** — all three consume `hCR` only through the
selector forcing, so the same discharged bound covers their CR leg. -/
theorem gentian_settle_alternate_floor_binds_rom (D : FloorDigestDeployment)
    (tagDec : DecidableEq D.Tag) (m : ℕ) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (alternateFloorRomGame D tagDec m))
    (hA : RomOpenEff (floorRomFamily D tagDec m) (floorRomCarrier D tagDec m) Q A) :
    Negl (gameAdv (alternateFloorRomGame D tagDec m) A) :=
  gentian_alternate_floor_binds_rom D tagDec m Q hQ A hA

/-- **(TOOTH — the class is INHABITED with POSITIVE advantage.)** The `0`-query constant answerer on
two distinct truncated floors is in the class at every budget and wins with positive probability at
every parameter — the discharged bound bounds something genuinely nonzero. -/
theorem alternateFloorRom_class_inhabited_pos (D : FloorDigestDeployment)
    (tagDec : DecidableEq D.Tag) (m : ℕ) (hm : 0 < m) (Q : ℕ → ℕ) :
    ∃ A, RomOpenEff (floorRomFamily D tagDec m) (floorRomCarrier D tagDec m) Q A
      ∧ ∀ l, 0 < gameAdv (alternateFloorRomGame D tagDec m) A l := by
  obtain ⟨t₀⟩ := D.tagNonempty
  refine ⟨romOpenAdv (floorRomFamily D tagDec m) (floorRomCarrier D tagDec m)
      (constOpenComp (floorRomFamily D tagDec m) (floorRomCarrier D tagDec m)
        (fun l => ⟨0, by positivity⟩) (fun _ => (t₀, ()))
        (fun _ => (⟨0, Nat.succ_pos m⟩, fun _ => none)) (fun _ => (⟨1, by omega⟩, fun _ => none))),
    constOpen_in_eff (floorRomFamily D tagDec m) (floorRomCarrier D tagDec m) _ _ _ _ Q,
    fun l => constOpen_gameAdv_pos (floorRomFamily D tagDec m) (floorRomCarrier D tagDec m)
      _ _ _ _ l ?_⟩
  intro hc
  have : (0 : ℕ) = 1 := congrArg (fun v : BVec (Fin babyBearP) m => v.1.val) hc
  omega

/-- **(TOOTH — the `shortCollAdv` shape is ADMITTED and DEFANGED, at this site.)** The `0`-query
constant answerer is in the class and the discharged bound applies to it: negligible against the
sampled oracle, where against the fixed `hash_many` it wins with probability `1`. -/
theorem alternateFloorRom_constAnswer_defanged (D : FloorDigestDeployment)
    (tagDec : DecidableEq D.Tag) (m : ℕ) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (r : ∀ l, Fin (2 ^ l)) (c : ∀ _l, D.Tag × Unit) (v w : ∀ _l, BVec (Fin babyBearP) m) :
    Negl (gameAdv (alternateFloorRomGame D tagDec m)
      (romOpenAdv _ _ (constOpenComp (floorRomFamily D tagDec m) (floorRomCarrier D tagDec m)
        r c v w))) :=
  constOpen_binds (floorRomFamily D tagDec m) (floorRomCarrier D tagDec m) r c v w Q hQ
    (flatFamily_card_R _ _ _ _ _ _ _ _)

/-- **(TOOTH — a non-negligible forger is OUTSIDE the class.)** -/
theorem alternateFloorRom_nonNegl_forger_excluded (D : FloorDigestDeployment)
    (tagDec : DecidableEq D.Tag) (m : ℕ) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (alternateFloorRomGame D tagDec m))
    (hnn : ¬ Negl (gameAdv (alternateFloorRomGame D tagDec m) A)) :
    ¬ RomOpenEff (floorRomFamily D tagDec m) (floorRomCarrier D tagDec m) Q A :=
  romOpen_forger_excluded _ _ Q hQ (flatFamily_card_R _ _ _ _ _ _ _ _) A hnn

#assert_all_clean [
  floorDigestBinds_false_of_finite_range,
  floorDigestBinds_false_babyBear,
  exists_collision_of_finite_range,
  deployed_hash_is_family_instance,
  floorCollisionGame_wins_iff,
  alternateFloorGame_wins_iff,
  limb_eq_witnessed_digest_of_sat,
  alternate_wins_imp,
  alternate_adv_le,
  gentian_alternate_floor_advantage_bound,
  gentian_settle_alternate_floor_advantage_bound,
  the_repaired_bound_fires_on_the_right_floor,
  floorDigest_floor_top_false_of_compressing,
  floorDigest_floor_top_false_babyBear,
  floorDigest_floor_bot_vacuous,
  brokenFloorDigest_floor_top_false,
  brokenFloorDigest_alternate_top_false,
  floorDigestFamily_CR_of_injective,
  floorVec_val,
  floorVec_inj,
  alternateFloorRom_dodge_is_break,
  gentian_alternate_floor_binds_rom,
  gentian_settle_alternate_floor_binds_rom,
  alternateFloorRom_class_inhabited_pos,
  alternateFloorRom_constAnswer_defanged,
  alternateFloorRom_nonNegl_forger_excluded
]

end Dregg2.Deos.InAirAuthorityFloorRegrounded
