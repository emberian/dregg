/-
# `Dregg2.Exec.SystemRootsBindingReduction` — the `system_roots` consensus binding, REBUILT as a
SECURITY REDUCTION on the grounded floor.

## What was here before, and why it was still a shirk

`Dregg2.Exec.SystemRoots` §3/§4 exports five bindings for the eight kernel-owned side-table roots
(escrow · queue · refcount · sturdyref · delegation · nullifier · commitments · sealed-boxes):

    systemRootsDigest_binds_or_collides           rootList sr = rootList sr' ∨ RootsColl …
    systemRootsDigest_binds_fn_or_collides        sr = sr'                   ∨ RootsColl …
    systemRootsDigest_binds_pointwise_or_collides (∀ i, sr i = sr' i)        ∨ RootsColl …
    cellCommitS_binds_systemRoots_or_collides     equal digest               ∨ CellCommitSColl …
    cellCommitS_binds_roots_pointwise_or_collides (∀ i, sr i = sr' i) ∨ CellCommitSColl ∨ RootsColl

Each was a genuine repair of a VACUOUS predecessor (they used to carry `compressNInjective`, which the
deployed BabyBear sponge REFUTES).  But they are still BARE DISJUNCTIONS, and at deployed parameters a
sponge collision EXISTS by pigeonhole — so `binds ∨ collides` is satisfiable through the `collides`
branch with `binds` never holding.  They quantify over SOLUTIONS.  Cryptographic hardness quantifies
over EFFICIENT ADVERSARIES.

⚑ **THESE ARE NOT THE HEADLINE ANY MORE.**  This module supplies the headline, and `SystemRoots`'s
docstrings now say so.  The exported security claim about the eight consensus roots is now
`sysRoots_binds_rom` / `cellCommitS_binds_rom` / `cellRoots_binds_rom` (§7): the same reductions on
the KEYED, QUERY-COUNTED random-oracle floor, which is PROVED (`KeyedRomFloor.keyedRom_hard`), with
no refutable hypothesis carried.  The `_from_polyTime` forms that used to sit here are DELETED — §6
proves their floor FALSE at the deployed sponge, and `Crypto.RomBindingReduction`'s header proves the
fixed-function game cannot be repaired by any `Eff`.

⚑ **AND THE DEMOTION IS NOT A DEPENDENCE — SAID PLAINLY, BECAUSE THE OPPOSITE IS THE EASY CLAIM.**
This reduction does NOT consume the five disjunctions.  Its win relation is
`EncodedBindingReduction.encBreakGame` at the deployed encoder, and the two bridges
(`sysRoots_forgery_is_break`, `cellCommitS_forgery_is_break`) are proved from `rootsEnc_faithful` +
`rootsEnc_inj` and from `List.append_cancel_left` respectively — the disjunctions appear over there
only in prose.  They survive for two reasons that are OPEN WORK, not architecture:

  1. `SystemRoots` §3′'s `_of_injective` strength bridges are derived from them, and
  2. they are STILL the exported headline one layer up — `Circuit.Emit.EffectVmFullStateRunnable`'s
     `wide_binds_systemRoots_or_collides` and its per-tag re-exports across 29 `Circuit/Emit`
     modules, of which exactly ONE (`EffectVmEmitMintRunnable`, via
     `EffectVmRowCommitReduction.wideRow_binds_from_polyTime`) has been re-pointed at a reduction.

Until (2) is finished, the deployed per-tag statements still offer the escape branch that this module
prices at the record layer.  That residual is named here rather than left for a reader to discover.

## The shape, and what it costs

The primitive is the deployed domain-separated Poseidon2 sponge
(`Poseidon2KeyedBridge.spongeFamily D`) — the real `List ℤ → ℤ` the prover computes, keyed by
the tag it absorbs.  The whole reduction is inherited from
`Dregg2.Crypto.EncodedBindingReduction`; this file supplies only

  * the two ENCODERS — `rootList` (the eight ordered root cells) at the digest layer, and
    `rest ++ [systemRootsDigest]` at the commitment layer — plus the definitional facts that the
    deployed digest/commitment ARE the family applied to them,
  * the STRUCTURAL injectivity `List.ofFn_inj` (a fact about the LIMB LAYOUT, not about the hash),
  * the fixed widths (`8` limbs at the digest layer, `rest.length + 1` at the commitment layer) that
    discharge the `poly_time` output-growth slot.

The three-way disjunction of `cellCommitS_binds_roots_pointwise_or_collides` becomes the standard
UNION BOUND (`EncodedBindingReduction.chained_binding_advantage_bound`): two extracted finders, two
advantages, one floor, one negligible sum.

⚑ **THE RESIDUAL, NAMED — AND THE INSTANTIATION IS PART OF IT.** The fixed-hash floor is
`HashCRHardQuant (spongeFamily D) Eff`, and at `Eff := ⊤` it is FALSE at deployed BabyBear parameters
(§5 — the honest price), at `Eff := ⊥` vacuous.  `Eff := IsPolyTime` is a strictly intermediate CLASS
(the class is proved inhabited, and `CostAdversary.bruteForce_not_polyTime` excludes the brute-force
PROGRAM) — but §6 PROVES that the floor AT that class is FALSE too at the deployed sponge:
`IsPolyTime` prices only ANSWER SIZE and declared syntactic work, so the `Classical.choice` adversary
that answers each tag with a TWO-LIMB collision is in it and wins with probability `1`
(`sysRoots_floor_polyTime_false_babyBear`).

So, stated without softening: at the FIXED hash, the `_advantage_bound` theorems (arbitrary `Eff`,
`hEff` in the open) are the honest content, and no `_from_polyTime` discharge survives — the three
that used to be exported here are DELETED, because their floor hypothesis is refuted by §6 and the
fixed-function game cannot be repaired by any class (`Crypto.RomBindingReduction`'s header: against a
fixed public sponge even a query-bounded adversary brute-forces).  The DISCHARGED headlines live in
§7, on the keyed-ROM floor, under the ROM idealisation named there — a floor that is PROVED
(`KeyedRomFloor.keyedRom_hard`, the birthday bound), at the price of a labelled modelling step
instead of a false hypothesis.

No `sorry`, no `axiom`, no `native_decide`.
-/
import Dregg2.Exec.SystemRoots
import Dregg2.Crypto.SpongeCarrierReduction
import Dregg2.Crypto.EncodedBindingReduction
import Dregg2.Crypto.RomCarrierSites

namespace Dregg2.Exec.SystemRootsBindingReduction

open Dregg2.Exec.SystemRoots
open Dregg2.Crypto.SpongeCarrierReduction (SpongeKeyed spongeFamily)
open Dregg2.Crypto.ConcreteSecurity (Negl PolyBounded)
open Dregg2.Crypto.FloorGames (Game Adversary gameAdv hashGame HashCRHardQuant)
open Dregg2.Crypto.CostAdversary (AnsSize IsPolyTime)
open Dregg2.Crypto.EncodedBindingReduction
open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)
open Dregg2.Crypto.KeyedRomFloor (KeyedRomFamily)
open Dregg2.Crypto.RomBindingReduction
open Dregg2.Crypto.RomCarrierSites

set_option autoImplicit false

/-! ## §1 — the two deployed ENCODERS, and the faithfulness facts. -/

/-- **THE DIGEST-LAYER ENCODER** — the eight ordered side-table roots, exactly the list the deployed
`systemRootsDigest` sponge absorbs.  Key-independent: the domain separation lives in the family's own
`H` (`sponge (tagCode t ++ ·)`), which is where the deployment puts it. -/
def rootsEnc (D : SpongeKeyed) :
    ∀ l, (spongeFamily D).Key l → SysRoots → (spongeFamily D).Input :=
  fun _ _ sr => rootList sr

/-- **THE COMMITMENT-LAYER ENCODER** — the canonical cell's absorbed list with the `system_roots`
digest folded in as its last limb.  Key-DEPENDENT, because the inner digest is itself computed at the
sampled tag: this is the deployed nesting, not an idealization. -/
def commitEnc (D : SpongeKeyed) (rest : List FieldElem) :
    ∀ l, (spongeFamily D).Key l → SysRoots → (spongeFamily D).Input :=
  fun _ t sr => rest ++ [systemRootsDigest (D.hashAt t) sr]

/-- **FAITHFULNESS (digest layer).** The deployed `systemRootsDigest` at the sampled tag IS the keyed
family applied to the encoder — a definitional equality, so the game below is a game about the very
function the prover computes. -/
theorem rootsEnc_faithful (D : SpongeKeyed) (l : ℕ)
    (t : (spongeFamily D).Key l) (sr : SysRoots) :
    systemRootsDigest (D.hashAt t) sr = (spongeFamily D).H l t (rootsEnc D l t sr) := by
  simp [systemRootsDigest, Dregg2.Circuit.ListCommit.listDigest, rootsEnc, spongeFamily,
    SpongeKeyed.hashAt]

/-- **FAITHFULNESS (commitment layer).** The deployed `cellCommitS` at the sampled tag IS the keyed
family applied to the commitment encoder. -/
theorem commitEnc_faithful (D : SpongeKeyed) (rest : List FieldElem) (l : ℕ)
    (t : (spongeFamily D).Key l) (sr : SysRoots) :
    cellCommitS (D.hashAt t) rest sr = (spongeFamily D).H l t (commitEnc D rest l t sr) :=
  rfl

/-- **THE STRUCTURAL INJECTIVITY — about the LIMB LAYOUT, never about the hash.** `rootList` is
`List.ofFn`, so equal root lists force the whole sub-block function equal.  This is the fact that makes
a sub-block equivocation an ENCODING equivocation, i.e. a genuine sponge break. -/
theorem rootsEnc_inj (D : SpongeKeyed) (l : ℕ) (t : (spongeFamily D).Key l)
    (sr sr' : SysRoots) (h : rootsEnc D l t sr = rootsEnc D l t sr') : sr = sr' :=
  List.ofFn_inj.mp h

/-! ## §2 — the two forgery GAMES, and the deployed-object bridges.

⚑ These REPLACE `systemRootsDigest_binds_or_collides` / `_binds_fn_or_collides` /
`_binds_pointwise_or_collides` / `cellCommitS_binds_systemRoots_or_collides` as the exported claim.
All three digest-layer disjunctions are ONE game — they differed only in how the SAME binding was
projected (list / function / pointwise), which is precisely why three bare disjunctions were three
copies of one unpriced escape. -/

/-- **THE `system_roots` DIGEST FORGERY.** The adversary is handed a sampled domain-separation tag and
WINS iff it publishes ONE `systemRootsDigest` for TWO different side-table configurations — a dropped
escrow, an omitted nullifier, a reordered queue, all at once. -/
def sysRootsBreakGame (D : SpongeKeyed) : Game :=
  encBreakGame (spongeFamily D) SysRoots (rootsEnc D)

/-- **THE CELL-COMMITMENT FORGERY.** The adversary WINS iff two cells over the same `rest` publish one
`cellCommitS` while their absorbed `system_roots` digests differ. -/
def cellCommitSBreakGame (D : SpongeKeyed) (rest : List FieldElem) : Game :=
  encBreakGame (spongeFamily D) SysRoots (commitEnc D rest)

/-- **⚑ THE FORGERY IS THE DEPLOYED ANTI-GHOST VIOLATION (digest layer).** Two side-table sub-blocks
that DIFFER AT ANY KERNEL INDEX yet share the deployed `systemRootsDigest` ARE a win.  This is the
statement `systemRootsDigest_binds_pointwise_or_collides` was reaching for, with the escape priced
instead of offered. -/
theorem sysRoots_forgery_is_break (D : SpongeKeyed) (l : ℕ)
    (t : (spongeFamily D).Key l) {sr sr' : SysRoots}
    (hne : ¬ (∀ i : Fin N_SYSTEM_ROOTS, sr i = sr' i))
    (heq : systemRootsDigest (D.hashAt t) sr = systemRootsDigest (D.hashAt t) sr') :
    (sysRootsBreakGame D).wins l t (sr, sr') := by
  refine encForgery_is_break_of_inj (spongeFamily D) SysRoots (rootsEnc D)
    (rootsEnc_inj D) (fun h => hne (fun i => congrFun h i)) ?_
  rw [← rootsEnc_faithful, ← rootsEnc_faithful]
  exact heq

/-- **⚑ THE FORGERY IS THE DEPLOYED ANTI-GHOST VIOLATION (commitment layer).** Two cells with EQUAL
canonical commitments over the same `rest` but DIFFERENT `system_roots` digests ARE a win — the
statement `cellCommitS_binds_systemRoots_or_collides` was reaching for. -/
theorem cellCommitS_forgery_is_break (D : SpongeKeyed) (rest : List FieldElem) (l : ℕ)
    (t : (spongeFamily D).Key l) {sr sr' : SysRoots}
    (hne : systemRootsDigest (D.hashAt t) sr ≠ systemRootsDigest (D.hashAt t) sr')
    (heq : cellCommitS (D.hashAt t) rest sr = cellCommitS (D.hashAt t) rest sr') :
    (cellCommitSBreakGame D rest).wins l t (sr, sr') := by
  refine encForgery_is_break (spongeFamily D) SysRoots (commitEnc D rest) ?_ heq
  intro h
  have happ : rest ++ [systemRootsDigest (D.hashAt t) sr]
      = rest ++ [systemRootsDigest (D.hashAt t) sr'] := h
  exact hne (by simpa using List.append_cancel_left happ)

/-! ## §3 — THE HEADLINE BINDINGS, as reductions, with efficiency DISCHARGED. -/

/-- The digest game's answer encoding — two eight-cell sub-blocks. -/
def sysRootsAnsSize (D : SpongeKeyed) : AnsSize (sysRootsBreakGame D) :=
  domainAnsSize (spongeFamily D) SysRoots (rootsEnc D) (fun _ _ => N_SYSTEM_ROOTS)

/-- The commitment game's answer encoding — the same two sub-blocks. -/
def cellCommitSAnsSize (D : SpongeKeyed) (rest : List FieldElem) :
    AnsSize (cellCommitSBreakGame D rest) :=
  domainAnsSize (spongeFamily D) SysRoots (commitEnc D rest) (fun _ _ => N_SYSTEM_ROOTS)

/-- The sponge collision game's answer encoding — the two claimed absorbed lists. -/
def spongeAnsSize (D : SpongeKeyed) : AnsSize (hashGame (spongeFamily D)) :=
  pairAnsSize (spongeFamily D) (fun _ xs => xs.length)

/-- The deployed sub-block is EXACTLY eight limbs wide — the layout fact that discharges the
`poly_time` output-growth slot at the digest layer. -/
theorem rootsEnc_width (D : SpongeKeyed) (l : ℕ)
    (t : (spongeFamily D).Key l) (sr : SysRoots) :
    (rootsEnc D l t sr).length ≤ N_SYSTEM_ROOTS := by
  show (List.ofFn sr).length ≤ N_SYSTEM_ROOTS
  exact Nat.le_of_eq List.length_ofFn

/-- The deployed cell absorbs `rest` plus ONE digest limb — the commitment-layer width fact. -/
theorem commitEnc_width (D : SpongeKeyed) (rest : List FieldElem) (l : ℕ)
    (t : (spongeFamily D).Key l) (sr : SysRoots) :
    (commitEnc D rest l t sr).length ≤ rest.length + 1 := by
  simp [commitEnc]

/-- **⚑ THE `system_roots` BINDING — the headline, at an arbitrary adversary class.** Under the
deployed sponge's collision floor, a side-table-root forger whose extracted finder is in the class has
NEGLIGIBLE advantage: the committed digest binds all EIGHT consensus roots except with negligible
probability.  `hEff` is the honest open obligation; the next theorem discharges it. -/
theorem sysRoots_binds_advantage_bound (D : SpongeKeyed)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (sysRootsBreakGame D))
    (hEff : Eff (encBreakToFinder (spongeFamily D) SysRoots (rootsEnc D) A))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (sysRootsBreakGame D) A) :=
  encBinding_advantage_bound (spongeFamily D) SysRoots (rootsEnc D) Eff A hEff hCR

/-!  ⚑ **WHERE THE DISCHARGED HEADLINES WENT.** This section used to export
`sysRoots_binds_from_polyTime` / `cellCommitS_binds_from_polyTime`: the same reductions with `hEff`
discharged at `Eff := IsPolyTime`.  §6 PROVES that floor FALSE at the deployed sponge
(`sysRoots_floor_polyTime_false_babyBear`), so those exports were VACUOUS at deployed parameters, and
— `Crypto.RomBindingReduction`'s header argument — the fixed-function game they rest on cannot be
repaired by ANY `Eff`: against a fixed public sponge even a query-bounded adversary brute-forces.
They are DELETED.  The discharged headlines are now §7's `sysRoots_binds_rom` /
`cellCommitS_binds_rom` / `cellRoots_binds_rom`, on the keyed, query-counted random-oracle floor,
which is a THEOREM (`KeyedRomFloor.keyedRom_hard`).  The `_advantage_bound` forms above remain the
honest fixed-hash statements, with `hEff` in the open. -/

/-! ## §4 — the FULL CHAIN (commitment ⟸ digest ⟸ sub-block), as a UNION BOUND.

`cellCommitS_binds_roots_pointwise_or_collides` exported a THREE-way bare disjunction — TWO escape
branches.  Here it is one game with two extractors and one floor: the standard union bound. -/

/-- **THE FULL-CHAIN FORGERY.** The adversary WINS iff two cells with the SAME canonical commitment
(over the same `rest`) disagree on ANY of the eight side-table roots.  This is the deployed soundness
statement for the whole `system_roots` sub-block: "the canonical commitment binds the whole side-table
state". -/
def cellRootsForgery (D : SpongeKeyed) (rest : List FieldElem) :
    KeyedForgery (spongeFamily D) where
  Ans := fun _ => SysRoots × SysRoots
  wins := fun _ t c =>
    (¬ (∀ i : Fin N_SYSTEM_ROOTS, c.1 i = c.2 i))
      ∧ cellCommitS (D.hashAt t) rest c.1 = cellCommitS (D.hashAt t) rest c.2
  winsDec := fun _ t c => by
    letI : DecidableEq SysRoots := Classical.decEq _
    exact inferInstance

/-- **THE PROBLEM IS IN THE STATEMENT.** -/
theorem cellRootsForgery_wins_iff (D : SpongeKeyed) (rest : List FieldElem) (l : ℕ)
    (t : (spongeFamily D).Key l) (c : SysRoots × SysRoots) :
    (cellRootsForgery D rest).wins l t c ↔
      ((¬ (∀ i : Fin N_SYSTEM_ROOTS, c.1 i = c.2 i))
        ∧ cellCommitS (D.hashAt t) rest c.1 = cellCommitS (D.hashAt t) rest c.2) :=
  Iff.rfl

/-- The commitment-layer extractor: hand the chain forger's answer straight to the commitment game. -/
def chainToCommit (D : SpongeKeyed) (rest : List FieldElem)
    (A : Adversary (cellRootsForgery D rest).game) : Adversary (cellCommitSBreakGame D rest) where
  run := A.run

/-- The digest-layer extractor: the SAME answer, read at the inner layer. -/
def chainToRoots (D : SpongeKeyed) (rest : List FieldElem)
    (A : Adversary (cellRootsForgery D rest).game) : Adversary (sysRootsBreakGame D) where
  run := A.run

/-- **⚑ THE CHAIN PEEL, AS A WIN IMPLICATION.** Every tag the chain forger wins, at least ONE layer
forger wins: either the two absorbed cell lists DIFFER (a commitment-layer break) or they AGREE — in
which case the two `system_roots` digests are equal while the sub-blocks differ, a digest-layer break.
This is `cellCommitS_binds_roots_pointwise_or_collides`'s case analysis, turned from an exported
disjunction into the internal step of a union bound. -/
theorem chain_wins_imp (D : SpongeKeyed) (rest : List FieldElem)
    (A : Adversary (cellRootsForgery D rest).game) (l : ℕ)
    (t : (spongeFamily D).Key l)
    (hwin : (cellRootsForgery D rest).wins l t (A.run l t)) :
    (cellCommitSBreakGame D rest).wins l t ((chainToCommit D rest A).run l t)
      ∨ (sysRootsBreakGame D).wins l t ((chainToRoots D rest A).run l t) := by
  obtain ⟨hne, heq⟩ := hwin
  by_cases hdig : systemRootsDigest (D.hashAt t) (A.run l t).1
      = systemRootsDigest (D.hashAt t) (A.run l t).2
  · exact Or.inr (sysRoots_forgery_is_break D l t hne hdig)
  · exact Or.inl (cellCommitS_forgery_is_break D rest l t hdig heq)

/-- **⚑ THE FULL-CHAIN BINDING — the headline that replaces the three-way disjunction.** Under ONE
collision floor for the deployed sponge, a forger that equivocates ANY of the eight side-table roots
under a fixed canonical cell commitment has NEGLIGIBLE advantage.  Two extracted finders, two
advantages, one floor, one negligible sum — the union bound, not an escape hatch.

⚑ This is what replaces `cellCommitS_binds_roots_pointwise_or_collides` as the exported claim: the
soundness statement STAGE 3 buys for ALL 8 side-tables, at deployed parameters, against EFFICIENT
adversaries. -/
theorem cellRoots_binds_advantage_bound (D : SpongeKeyed) (rest : List FieldElem)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (cellRootsForgery D rest).game)
    (hEff₁ : Eff (encBreakToFinder (spongeFamily D) SysRoots (commitEnc D rest)
      (chainToCommit D rest A)))
    (hEff₂ : Eff (encBreakToFinder (spongeFamily D) SysRoots (rootsEnc D)
      (chainToRoots D rest A)))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (cellRootsForgery D rest).game A) :=
  chained_binding_advantage_bound (cellRootsForgery D rest) SysRoots SysRoots
    (commitEnc D rest) (rootsEnc D) Eff A (chainToCommit D rest A) (chainToRoots D rest A)
    (chain_wins_imp D rest A) hEff₁ hEff₂ hCR

/-!  ⚑ **WHERE THE DISCHARGED CHAIN WENT.** `cellRoots_binds_from_polyTime` — this union bound with
both `hEff`s discharged at `Eff := IsPolyTime` — is DELETED for the same §6 reason, and its successor
is §7's `cellRoots_binds_rom`: the same two-layer union bound, over ONE sampled oracle, with the
digest-layer extractor a `mapOut` post-map and the commitment-layer extractor a `bindComp` two-query
extension, both budgets preserved, and the floor PROVED. -/

/-! ## §5 — BOTH POLES of the floor, PROVED, plus the non-vacuity teeth. -/

/-- **⚑ THE ⊤ POLE — the floor is FALSE at the REAL BabyBear parameters** (the honest price of `hEff`).
A sponge whose output is a genuine field element has finite range on the infinite `List ℤ`, so a
collision exists at every tag and the floor at `Eff := ⊤` is FALSE.  What the reduction buys is not a
floor the deployed sponge satisfies at ⊤ — no such floor exists — it is one named parameter with both
poles proved, in place of an unconditionally-available disjunct. -/
theorem sysRoots_floor_top_false_babyBear (D : SpongeKeyed)
    (hb : ∀ xs : List ℤ, 0 ≤ D.sponge xs ∧ D.sponge xs < (2013265921 : ℤ)) :
    ¬ HashCRHardQuant (spongeFamily D) (fun _ => True) := by
  refine floor_top_false_of_compressing _ ⟨([] : List ℤ)⟩ (fun l t => ?_)
  refine exists_collision_of_not_injective
    (h := fun xs => (spongeFamily D).H l t xs) (fun hinj => ?_)
  refine Dregg2.Circuit.HashFloorHonesty.poseidon2SpongeCR_false_babyBear
    (fun xs => D.sponge (D.tagCode t ++ xs)) (fun xs => hb _) ?_
  intro xs ys hxy
  exact hinj xs ys hxy

/-- **THE ⊥ POLE — vacuous.** Recorded so the floor's satisfiability cannot be mistaken for evidence. -/
theorem sysRoots_floor_bot_vacuous (D : SpongeKeyed) :
    HashCRHardQuant (spongeFamily D) (fun _ => False) :=
  floor_bot_vacuous _

/-- **(TOOTH — the instantiated class is NOT EMPTY.)** The constant finder is in `IsPolyTime` at the
sponge game's own answer encoding, so `Eff := IsPolyTime` is not `⊥` in disguise.  With
`CostAdversary.bruteForce_not_polyTime` (the ⊤-collapse witness EXCLUDED) this pins the instantiated
floor strictly between the two poles. -/
theorem sysRoots_polyTime_class_inhabited (D : SpongeKeyed) :
    IsPolyTime (spongeAnsSize D)
      (Dregg2.Crypto.CostAdversary.idAdv (G := hashGame (spongeFamily D)) (O := Unit)
        (Q := fun _ => Unit) (R := fun _ => Unit)
        (fun _ _ => (([] : List ℤ), ([] : List ℤ)))).toAdversary :=
  isPolyTime_class_inhabited (spongeFamily D) (fun _ xs => xs.length) _
    ⟨0, 0, fun _ _ => by simp [pairAnsSize]⟩

/-- **(CANARY — the keystone does NOT follow from the floor applied at ANOTHER finder.)** Strip the
reduction and the binding does not go through: only `enc_adv_le` connects the extracted finder to the
forgery game.  Reds if a future edit collapses the two games. -/
example (D : SpongeKeyed)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (sysRootsBreakGame D))
    (B : Adversary (hashGame (spongeFamily D))) (hB : Eff B)
    (hCR : HashCRHardQuant (spongeFamily D) Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (sysRootsBreakGame D) A) := hCR B hB)
  trivial

/-- **THE POSITIVE POLE — the RIGHT floor DOES discharge it.** A gate that refuses everything is a
broken keystone, not a fixed one. -/
theorem the_reduced_sysRoots_bound_fires (D : SpongeKeyed)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (sysRootsBreakGame D))
    (hEff : Eff (encBreakToFinder (spongeFamily D) SysRoots (rootsEnc D) A))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (sysRootsBreakGame D) A) :=
  sysRoots_binds_advantage_bound D Eff A hEff hCR

/-- **(TOOTH — a REFLEXIVE answer is never a win.)** The game does not hand the adversary a free win,
so the negligibility is not the negligibility of an unwinnable game's advantage in disguise. -/
theorem sysRoots_no_reflexive_break (D : SpongeKeyed) (l : ℕ)
    (t : (spongeFamily D).Key l) (sr : SysRoots) :
    ¬ (sysRootsBreakGame D).wins l t (sr, sr) :=
  no_reflexive_break (spongeFamily D) SysRoots (rootsEnc D) l t sr

/-! ## §6 — ⚑ THE INSTANTIATED FLOOR IS FALSE TOO, AT THE DEPLOYED SPONGE.

§5 prices the ⊤ pole and records that `Eff := IsPolyTime` sits STRICTLY BETWEEN the two poles AS A
CLASS.  That is true and it is not enough, and this section says why in Lean rather than in prose.

`CostAdversary.IsPolyTime sz A` is `∃ B : CostAdversary …, B.toAdversary = A ∧ PolyTime sz B`, and
`CostAdversary.idAdv a₀` accepts an ARBITRARY Lean function `a₀` — including a `Classical.choice` one —
as `.pure (a₀ l i)`, whose whole cost is `sz l (a₀ l i)`.  So the class contains EVERY adversary whose
ANSWERS are poly-size, no matter how hard those answers are to find:
`isPolyTime_of_polySize_answers` below is that observation, proved.

Consequently the floor at `Eff := IsPolyTime` is not the class restriction it reads as.  A compressing
sponge has SHORT collisions — the one-limb messages `[n]`, `n : ℤ`, are an infinite family landing in
one bounded field — so the choice adversary that answers with a short collision at every tag is in the
class, wins with probability `1`, and REFUTES the floor.  `sysRoots_floor_polyTime_false_babyBear` is
that refutation at the deployed BabyBear bound.

⚑ **WHAT THIS MEANT FOR THE OLD HEADLINES — AND WHAT WAS DONE ABOUT IT.**
`sysRoots_binds_from_polyTime`, `cellCommitS_binds_from_polyTime` and `cellRoots_binds_from_polyTime`
carried `HashCRHardQuant (spongeFamily D) (IsPolyTime (spongeAnsSize D))` as a hypothesis, and at the
deployed sponge that hypothesis is FALSE — the same defect, one level up, as the `compressNInjective`
bindings this whole repair deleted.  They are now DELETED in turn, and their successors are §7's
`_binds_rom` forms.  The `_advantage_bound` forms are NOT vacuous and remain: they quantify over an
arbitrary class with `hEff` in the open, and they are the honest fixed-hash content of this module.

⚑ **THE DEFECT WAS THE COST MODEL AND THE GAME, NOT THIS SITE.** `IsPolyTime` measures OUTPUT SIZE
plus DECLARED syntactic work, and lets any Lean function be embedded at that price, so it cannot
separate "writes a short string" from "finds a collision" — and no repair of the class fixes the
GAME, because the fixed public sponge can be brute-forced by any adversary allowed to evaluate it
(`Crypto.RomBindingReduction`'s header).  The fix that landed is the one that works: the floor moved
to a SAMPLED oracle (`Crypto.KeyedRomFloor`), where query-counting has teeth and the birthday bound
is a THEOREM.  This section survives as the refutation that FORCED that move, provable at a deployed
instance. -/

/-- **⚑ `IsPolyTime` IS EXACTLY "POLY-SIZE ANSWERS" (the ⊇ half, which is the damaging one).** Any
adversary at all — `Classical.choice`-defined, non-computable, whatever — is in the class as soon as
the answers it writes are poly-size, because `idAdv` embeds its `run` verbatim and charges only the
answer.  Nothing about finding the answer is priced. -/
theorem isPolyTime_of_polySize_answers {G : Dregg2.Crypto.FloorGames.Game}
    (sz : AnsSize G) (A : Adversary G)
    (hsz : ∃ C k : ℕ, ∀ l (i : G.Inst l), sz l (A.run l i) ≤ C * l ^ k + C) :
    IsPolyTime sz A :=
  Dregg2.Crypto.CostAdversary.isPolyTime_inhabited sz A.run hsz

/-- **A SHORT COLLISION AT EVERY TAG.** The one-limb messages `[n]` for `n : ℤ` are an infinite family
whose sponge images all land in `[0, p)` — so two of them collide, and the witness is TWO LIMBS TOTAL.
Pure pigeonhole (`HashFloorHonesty.not_injective_of_finite_range`), no Poseidon2 structure used. -/
theorem exists_short_collision (D : SpongeKeyed)
    (hb : ∀ xs : List ℤ, 0 ≤ D.sponge xs ∧ D.sponge xs < (2013265921 : ℤ))
    (l : ℕ) (t : (spongeFamily D).Key l) :
    ∃ p : List ℤ × List ℤ, (hashGame (spongeFamily D)).wins l t p
      ∧ p.1.length + p.2.length ≤ 2 := by
  have hfin : (Set.range (fun n : ℤ => D.sponge (D.tagCode t ++ [n]))).Finite := by
    refine (Set.finite_Ico (0 : ℤ) 2013265921).subset ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨(hb _).1, (hb _).2⟩
  have hni := Dregg2.Circuit.HashFloorHonesty.not_injective_of_finite_range
    (fun n : ℤ => D.sponge (D.tagCode t ++ [n])) hfin
  rw [Function.not_injective_iff] at hni
  obtain ⟨n, m, himg, hne⟩ := hni
  refine ⟨([n], [m]), ⟨fun h => hne ?_, himg⟩, by simp⟩
  injection h with h1 _

/-- **THE SHORT-COLLISION ADVERSARY** — answers every sampled tag with a two-limb collision. It is a
perfectly good `Adversary`: nothing in that type demands computability, and nothing in `IsPolyTime`
demands it either. -/
noncomputable def shortCollAdv (D : SpongeKeyed)
    (hb : ∀ xs : List ℤ, 0 ≤ D.sponge xs ∧ D.sponge xs < (2013265921 : ℤ)) :
    Adversary (hashGame (spongeFamily D)) where
  run := fun l t => (exists_short_collision D hb l t).choose

/-- It wins at EVERY tag. -/
theorem shortCollAdv_wins (D : SpongeKeyed)
    (hb : ∀ xs : List ℤ, 0 ≤ D.sponge xs ∧ D.sponge xs < (2013265921 : ℤ))
    (l : ℕ) (t : (spongeFamily D).Key l) :
    (hashGame (spongeFamily D)).wins l t ((shortCollAdv D hb).run l t) :=
  (exists_short_collision D hb l t).choose_spec.1

/-- And it is IN the class the headline theorems instantiate the floor at — two limbs is poly-size. -/
theorem shortCollAdv_isPolyTime (D : SpongeKeyed)
    (hb : ∀ xs : List ℤ, 0 ≤ D.sponge xs ∧ D.sponge xs < (2013265921 : ℤ)) :
    IsPolyTime (spongeAnsSize D) (shortCollAdv D hb) :=
  isPolyTime_of_polySize_answers _ _
    ⟨2, 0, fun l t => by
      have h := (exists_short_collision D hb l t).choose_spec.2
      simpa [spongeAnsSize, pairAnsSize, shortCollAdv] using h.trans (by omega)⟩

/-- **⚑ THE INSTANTIATED FLOOR IS FALSE AT THE DEPLOYED SPONGE.** The refutation that killed (and
deleted) the `_from_polyTime` exports of this module: any discharge at `Eff := IsPolyTime` over the
fixed-hash game carries a hypothesis this theorem refutes.  The fixed-hash live content is the
`_advantage_bound` forms with `hEff` in the open; the DISCHARGED headlines are §7's `_binds_rom`
forms on the keyed-ROM floor, which this refutation forced the floor to move to. -/
theorem sysRoots_floor_polyTime_false_babyBear (D : SpongeKeyed)
    (hb : ∀ xs : List ℤ, 0 ≤ D.sponge xs ∧ D.sponge xs < (2013265921 : ℤ)) :
    ¬ HashCRHardQuant (spongeFamily D) (IsPolyTime (spongeAnsSize D)) := by
  intro hHard
  have hneg := hHard (shortCollAdv D hb) (shortCollAdv_isPolyTime D hb)
  have hone : gameAdv (hashGame (spongeFamily D)) (shortCollAdv D hb) = fun _ => (1 : ℝ) := by
    funext l
    show @Dregg2.Crypto.ProbCrypto.winProb _ ((hashGame (spongeFamily D)).instFin l) _ = 1
    have hall : (shortCollAdv D hb).hit l = fun _ => true := by
      funext t
      exact ((shortCollAdv D hb).hit_eq_true l t).mpr (shortCollAdv_wins D hb l t)
    rw [hall]
    exact @Dregg2.Crypto.ProbCrypto.winProb_top _ ((hashGame (spongeFamily D)).instFin l)
      ((hashGame (spongeFamily D)).instNe l)
  rw [hone] at hneg
  exact Dregg2.Crypto.ConcreteSecurity.not_negl_one hneg

/-! ## §7 — ⚑⚑ THE KEYED-ROM RE-GROUNDING: the discharged headlines, on a floor that is PROVED.

§6 killed the `IsPolyTime` discharge, and `Crypto.RomBindingReduction`'s header proves the deeper
point: NO efficiency class repairs the fixed-function game, because the sponge there is a fixed
public function and only the tag is sampled.  The floor must move to a SAMPLED oracle.  This section
is that move for the eight consensus roots, on `Crypto.RomCarrierSites`' kit.

⚑ **THE MODELLING STEP, STATED (not smuggled).**  Landing here idealises the deployed
domain-separated Poseidon2 sponge as a keyed RANDOM ORACLE at an ASYMPTOTIC digest width:

  * the sampled `H : Tag × Msg → Fin (2 ^ l)` replaces the fixed public
    `sponge (tagCode t ++ ·)` — the standard ROM idealisation, a deliberate modelling step and NOT a
    derivation (`DomainSeparatedCREffRegrounded` §5's rule);
  * the digest space `Fin (2 ^ l)` is `λ`-growing where the deployed felt is a FIXED ~31-bit
    BabyBear element — there is no `l` at which they coincide, and at the deployed width the honest
    reading stays "binds exactly as well as ~31 bits allow" (birthday ≈ `2^15.5`), the felt-width
    wound (`docs/WOUND-felt-width-boundaries-2026-07-19.md`);
  * the message domain is the TRUNCATED deployed shape: sub-blocks of BabyBear-RANGE roots
    (`RootsBlock`), and `rest` limbs of fixed width `m`.  On everything the deployed prover actually
    absorbs (in-range felts, fixed layout) the truncation is LOSSLESS — `truncRoots_inj` and
    `truncRoots_rootList` pin that limb-for-limb;
  * the chained commitment absorbs the inner digest as a `Fin (2 ^ l)` limb (`Sum.inr (rest, dig)`),
    modelling the deployed `rest ++ [systemRootsDigest]` absorb; at the ideal width that limb is not
    a felt — the SAME felt-width residual, carried visibly in the type.

What the move buys: the floor under every theorem below is `KeyedRomFloor.keyedRom_hard` — the
birthday bound, a THEOREM with no assumption under it — where the deleted `_from_polyTime` forms
carried a hypothesis §6 REFUTES.  What it does not buy: any statement about the fixed deployed sponge
itself.

The two message shapes are domain-separated by the `Sum` constructor inside ONE family, so both
layers share one sampled oracle and the chain is a genuine union bound over it. -/

/-- **THE TRUNCATED SUB-BLOCK** — the eight consensus roots, each a genuine BabyBear-range felt.
Every sub-block the deployed prover commits is of this shape (`truncRoots` embeds it losslessly). -/
abbrev RootsBlock : Type := Fin N_SYSTEM_ROOTS → Fin babyBearP

/-- **THE ORACLE MESSAGE DOMAIN** — the two absorbed shapes, domain-separated by constructor:
`inl` a sub-block (the digest layer), `inr` a fixed-width `rest` with the inner digest as its last
limb (the commitment layer, the deployed `rest ++ [systemRootsDigest]` nesting). -/
abbrev SysRomMsg (m : ℕ) (l : ℕ) : Type :=
  RootsBlock ⊕ ((Fin m → Fin babyBearP) × Fin (2 ^ l))

/-- **THE `system_roots` KEYED ROM FAMILY** — keyed by the DEPLOYED tag space `D.Tag` (the anchor to
the deployed object: the same tags the prover absorbs), over the two-shape message domain, with the
ideal `λ`-bit digest. -/
def sysRomFamily (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) (m : ℕ) : KeyedRomFamily :=
  flatFamily D.Tag D.tagFintype tagDec D.tagNonempty (SysRomMsg m)
    (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ => ⟨Sum.inl (fun _ => ⟨0, babyBearP_pos⟩)⟩)

/-- The family's `hw` obligation, closed by construction — the trap `card BabyBear = 2 ^ l` (which no
`l` satisfies) never appears. -/
theorem sysRomFamily_card_R (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) (m : ℕ) (l : ℕ) :
    letI := (sysRomFamily D tagDec m).rFin l
    Fintype.card ((sysRomFamily D tagDec m).R l) = 2 ^ l := by
  show Fintype.card (Fin (2 ^ l)) = 2 ^ l
  simp

/-- **THE DIGEST-LAYER CARRIER** — commitment `H (t, inl block)`: the digest binds the WHOLE
sub-block.  The embedding is `Sum.inl`, injective on the nose — the ROM restatement of
`rootsEnc` + `rootsEnc_inj` (`List.ofFn` injectivity became constructor injectivity because the
truncated block IS the ordered limb tuple). -/
def rootsRomCarrier (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) (m : ℕ) :
    RomCarrier (sysRomFamily D tagDec m) :=
  taggedCarrier _ (fun _ => Unit) (fun _ => RootsBlock) (fun _ => inferInstance)
    (fun _ _ v => Sum.inl v) (fun _ _ _ _ h => Sum.inl.inj h)

/-- **THE COMMITMENT-LAYER CARRIER** — commitment `H (t, inr (rest, dig))`: the canonical cell
commitment binds its absorbed DIGEST limb under a fixed `(tag, rest)` context.  The ROM restatement
of `commitEnc`'s `List.append_cancel_left` content. -/
def commitRomCarrier (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) (m : ℕ) :
    RomCarrier (sysRomFamily D tagDec m) :=
  taggedCarrier _ (fun _ => Fin m → Fin babyBearP) (fun l => Fin (2 ^ l))
    (fun _ => inferInstance)
    (fun _ rest dig => Sum.inr (rest, dig))
    (fun _ _ _ _ h => congrArg Prod.snd (Sum.inr.inj h))

/-- The digest-layer forgery game: equivocate the sub-block digest at the sampled oracle. -/
abbrev sysRootsRomGame (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) (m : ℕ) : Game :=
  romCarrierGame (sysRomFamily D tagDec m) (rootsRomCarrier D tagDec m)

/-- The commitment-layer forgery game: equivocate the absorbed digest limb under one `(tag, rest)`. -/
abbrev cellCommitSRomGame (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) (m : ℕ) : Game :=
  romCarrierGame (sysRomFamily D tagDec m) (commitRomCarrier D tagDec m)

/-! ### The truncation is lossless on the deployed payloads (the modelling step's honesty teeth). -/

/-- Truncate an IN-RANGE deployed sub-block to its `RootsBlock` — total on exactly the sub-blocks the
deployed prover can commit (every root a genuine BabyBear felt). -/
def truncRoots (sr : SysRoots) (hb : ∀ i, 0 ≤ sr i ∧ sr i < (babyBearP : ℤ)) : RootsBlock :=
  fun i => ⟨(sr i).toNat, (Int.toNat_lt (hb i).1).mpr (hb i).2⟩

/-- **THE TRUNCATION LOSES NOTHING** — two in-range sub-blocks with one truncation are EQUAL, so a
distinct pair of deployed sub-blocks stays a distinct pair of ROM payloads. -/
theorem truncRoots_inj {sr sr' : SysRoots}
    (hb : ∀ i, 0 ≤ sr i ∧ sr i < (babyBearP : ℤ))
    (hb' : ∀ i, 0 ≤ sr' i ∧ sr' i < (babyBearP : ℤ))
    (h : truncRoots sr hb = truncRoots sr' hb') : sr = sr' := by
  funext i
  have hv : (sr i).toNat = (sr' i).toNat := congrArg Fin.val (congrFun h i)
  have hcast : (((sr i).toNat : ℕ) : ℤ) = (((sr' i).toNat : ℕ) : ℤ) := by exact_mod_cast hv
  rwa [Int.toNat_of_nonneg (hb i).1, Int.toNat_of_nonneg (hb' i).1] at hcast

/-- **LIMB-FOR-LIMB FAITHFULNESS** — reading the truncated block back as integers IS the deployed
absorbed list `rootList sr`.  The ROM message `inl (truncRoots sr _)` and the deployed absorb
`tagCode t ++ rootList sr` carry the same limbs; what changed is only WHO evaluates them (the sampled
oracle vs the fixed sponge) — which is the modelling step, named in §7's header. -/
theorem truncRoots_rootList {sr : SysRoots}
    (hb : ∀ i, 0 ≤ sr i ∧ sr i < (babyBearP : ℤ)) :
    List.ofFn (fun i => ((truncRoots sr hb i : ℕ) : ℤ)) = rootList sr := by
  unfold rootList
  congr 1
  funext i
  exact Int.toNat_of_nonneg (hb i).1

/-! ### The deployed anti-ghost violations ARE wins of the ROM games. -/

/-- **⚑ THE DIGEST-LAYER FORGERY IS THE DEPLOYED ANTI-GHOST VIOLATION.** Two DISTINCT in-range
sub-blocks whose (truncated) messages the sampled oracle maps to ONE digest ARE a win of the
digest-layer game — the §2 bridge `sysRoots_forgery_is_break`, restated at the sampled oracle. -/
theorem sysRootsRom_forgery_is_break (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) (m : ℕ)
    (l : ℕ) (H : (sysRootsRomGame D tagDec m).Inst l) (t : D.Tag) {sr sr' : SysRoots}
    (hb : ∀ i, 0 ≤ sr i ∧ sr i < (babyBearP : ℤ))
    (hb' : ∀ i, 0 ≤ sr' i ∧ sr' i < (babyBearP : ℤ))
    (hne : sr ≠ sr')
    (heq : H (t, Sum.inl (truncRoots sr hb)) = H (t, Sum.inl (truncRoots sr' hb'))) :
    (sysRootsRomGame D tagDec m).wins l H ((t, ()), truncRoots sr hb, truncRoots sr' hb') :=
  ⟨fun hc => hne (truncRoots_inj hb hb' hc), heq⟩

/-- **THE COMMITMENT-LAYER FORGERY IS THE DEPLOYED VIOLATION** — one `(tag, rest)` cell commitment
carrying two DISTINCT inner digests is a win (the `List.append_cancel_left` step of
`cellCommitS_forgery_is_break`, now in the type). -/
theorem cellCommitSRom_forgery_is_break (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) (m : ℕ)
    (l : ℕ) (H : (cellCommitSRomGame D tagDec m).Inst l) (t : D.Tag)
    (rest : Fin m → Fin babyBearP) {d d' : Fin (2 ^ l)}
    (hne : d ≠ d')
    (heq : H (t, Sum.inr (rest, d)) = H (t, Sum.inr (rest, d'))) :
    (cellCommitSRomGame D tagDec m).wins l H ((t, rest), d, d') :=
  ⟨hne, heq⟩

/-! ### THE HEADLINES — no floor hypothesis, no width obligation, nothing refutable carried. -/

/-- **⚑⚑ THE `system_roots` BINDING, DISCHARGED ON THE PROVED FLOOR.** Every query-bounded forger of
the sub-block digest has NEGLIGIBLE advantage: the committed digest binds all EIGHT consensus roots
except with negligible probability, in the keyed ROM model of §7's header.  The hypotheses are a
polynomial query budget and the forger's membership in the query class — nothing refutable.  This is
what `sysRoots_binds_from_polyTime` (DELETED, floor refuted by §6) claimed and could not have. -/
theorem sysRoots_binds_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) (m : ℕ) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (sysRootsRomGame D tagDec m))
    (hA : RomCarrierEff (sysRomFamily D tagDec m) (rootsRomCarrier D tagDec m) Q A) :
    Negl (gameAdv (sysRootsRomGame D tagDec m) A) :=
  romCarrier_binds _ _ Q hQ (sysRomFamily_card_R D tagDec m) A hA

/-- **⚑ THE CELL-COMMITMENT BINDING, DISCHARGED** — the successor of the deleted
`cellCommitS_binds_from_polyTime`: a query-bounded forger that equivocates the absorbed digest limb
under one canonical `(tag, rest)` commitment has negligible advantage. -/
theorem cellCommitS_binds_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) (m : ℕ) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (cellCommitSRomGame D tagDec m))
    (hA : RomCarrierEff (sysRomFamily D tagDec m) (commitRomCarrier D tagDec m) Q A) :
    Negl (gameAdv (cellCommitSRomGame D tagDec m) A) :=
  romCarrier_binds _ _ Q hQ (sysRomFamily_card_R D tagDec m) A hA

/-! ### The FULL CHAIN — commitment ⟸ digest ⟸ sub-block, over ONE sampled oracle. -/

/-- **THE FULL-CHAIN FORGERY** — the composed break: two DISTINCT sub-blocks whose NESTED deployed
commitments agree, `H (t, inr (rest, H (t, inl v))) = H (t, inr (rest, H (t, inl v')))`.  The inner
digest is genuinely re-absorbed by the outer commitment — the oracle appears INSIDE the win relation,
which is what neither single carrier could say.  The ROM restatement of `cellRootsForgery`. -/
def cellRootsRomForgery (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) (m : ℕ) :
    RomForgery (sysRomFamily D tagDec m) where
  Ans := fun _ => D.Tag × (Fin m → Fin babyBearP) × RootsBlock × RootsBlock
  wins := fun _ H a =>
    a.2.2.1 ≠ a.2.2.2 ∧
      H (a.1, Sum.inr (a.2.1, H (a.1, Sum.inl a.2.2.1)))
        = H (a.1, Sum.inr (a.2.1, H (a.1, Sum.inl a.2.2.2)))
  winsDec := fun l _ _ => by
    letI := ((sysRomFamily D tagDec m).toRomFamily).rDec l
    exact inferInstance

/-- **THE DIGEST-LAYER EXTRACTION** — a pure post-map of the chain forger's program: read its answer
at the inner layer.  `mapOut`, so the query budget is PRESERVED. -/
def chainRomComp₁ (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) (m : ℕ)
    (M : ∀ l, OracleComp ((sysRomFamily D tagDec m).toRomFamily.D l)
      ((sysRomFamily D tagDec m).toRomFamily.R l) ((cellRootsRomForgery D tagDec m).Ans l)) :
    RomCarrierComp (sysRomFamily D tagDec m) (rootsRomCarrier D tagDec m) :=
  fun l => OracleComp.mapOut (fun a => ((a.1, ()), a.2.2.1, a.2.2.2)) (M l)

/-- **THE COMMITMENT-LAYER EXTRACTION** — run the chain forger, then RE-QUERY the two inner digests
and answer with them: `bindComp` with a two-query continuation, so the budget grows by exactly `2`. -/
def chainRomComp₂ (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) (m : ℕ)
    (M : ∀ l, OracleComp ((sysRomFamily D tagDec m).toRomFamily.D l)
      ((sysRomFamily D tagDec m).toRomFamily.R l) ((cellRootsRomForgery D tagDec m).Ans l)) :
    RomCarrierComp (sysRomFamily D tagDec m) (commitRomCarrier D tagDec m) :=
  fun l => OracleComp.bindComp (M l) (fun a =>
    OracleComp.query (a.1, Sum.inl a.2.2.1) (fun d =>
      OracleComp.query (a.1, Sum.inl a.2.2.2) (fun d' =>
        OracleComp.pure ((a.1, a.2.1), d, d'))))

/-- **⚑⚑ THE FULL-CHAIN BINDING, DISCHARGED ON THE PROVED FLOOR** — the successor of the deleted
`cellRoots_binds_from_polyTime`, and the deployed soundness statement for the whole `system_roots`
sub-block in the ROM model: a query-bounded forger that equivocates ANY of the eight side-table roots
under a fixed canonical cell commitment has NEGLIGIBLE advantage.  The chain peel is the §4 case
split (digests equal → digest-layer win; digests distinct → commitment-layer win); the two extracted
programs are `mapOut` (budget `Q`) and `bindComp` (budget `Q + 2`); the union bound runs over the ONE
sampled oracle both carriers share; each layer dies by the birthday floor.  No floor hypothesis. -/
theorem cellRoots_binds_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) (m : ℕ)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (cellRootsRomForgery D tagDec m).game)
    (hA : RomForgeryEff (sysRomFamily D tagDec m) (cellRootsRomForgery D tagDec m) Q A) :
    Negl (gameAdv (cellRootsRomForgery D tagDec m).game A) := by
  obtain ⟨M, hM, hrun⟩ := hA
  refine chained_rom_binds (cellRootsRomForgery D tagDec m)
    (rootsRomCarrier D tagDec m) (commitRomCarrier D tagDec m)
    Q (fun l => Q l + 2) hQ (polyBounded_sq_add_two Q hQ)
    (sysRomFamily_card_R D tagDec m) A
    (romCarrierAdv _ _ (chainRomComp₁ D tagDec m M))
    (romCarrierAdv _ _ (chainRomComp₂ D tagDec m M))
    ?_
    ⟨chainRomComp₁ D tagDec m M,
      fun l => OracleComp.mapOut_queryBounded _ (hM l), fun _ _ => rfl⟩
    ⟨chainRomComp₂ D tagDec m M,
      fun l => OracleComp.bindComp_queryBounded (hM l)
        (fun a => QueryBounded.query 1 _ _ (fun _ => QueryBounded.query 0 _ _
          (fun _ => QueryBounded.pure 0 _))), fun _ _ => rfl⟩
  intro l H hwin
  have hB₁run : (romCarrierAdv _ _ (chainRomComp₁ D tagDec m M)).run l H
      = (((A.run l H).1, ()), (A.run l H).2.2.1, (A.run l H).2.2.2) := by
    show (chainRomComp₁ D tagDec m M l).eval H = _
    unfold chainRomComp₁
    erw [OracleComp.mapOut_eval, ← hrun l H]
    rfl
  have hB₂run : (romCarrierAdv _ _ (chainRomComp₂ D tagDec m M)).run l H
      = (((A.run l H).1, (A.run l H).2.1),
          H ((A.run l H).1, Sum.inl (A.run l H).2.2.1),
          H ((A.run l H).1, Sum.inl (A.run l H).2.2.2)) := by
    show (chainRomComp₂ D tagDec m M l).eval H = _
    unfold chainRomComp₂
    erw [OracleComp.bindComp_eval, ← hrun l H]
    rfl
  obtain ⟨hne, heq⟩ := hwin
  by_cases hdig : H ((A.run l H).1, Sum.inl (A.run l H).2.2.1)
      = H ((A.run l H).1, Sum.inl (A.run l H).2.2.2)
  · refine Or.inl ?_
    rw [hB₁run]
    exact ⟨hne, hdig⟩
  · refine Or.inr ?_
    rw [hB₂run]
    exact ⟨hdig, heq⟩

/-! ### Non-vacuity teeth, at THIS site. -/

/-- **(TOOTH — the CHAIN class is INHABITED with POSITIVE advantage.)** The `0`-query constant
answerer on two distinct sub-blocks is in `RomForgeryEff` at every budget, and the chained game is
winnable at every parameter (the constant oracle collapses both nested commitments), so
`cellRoots_binds_rom` bounds something genuinely nonzero. -/
theorem cellRootsRom_class_inhabited_pos (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (m : ℕ) (Q : ℕ → ℕ) :
    ∃ A, RomForgeryEff (sysRomFamily D tagDec m) (cellRootsRomForgery D tagDec m) Q A
      ∧ ∀ l, 0 < gameAdv (cellRootsRomForgery D tagDec m).game A l := by
  obtain ⟨t₀⟩ := D.tagNonempty
  refine ⟨⟨fun _ _ => (t₀, (fun _ => ⟨0, babyBearP_pos⟩),
      (fun _ => ⟨0, babyBearP_pos⟩), (fun _ => ⟨1, one_lt_babyBearP⟩))⟩,
    ⟨fun _ => OracleComp.pure (t₀, (fun _ => ⟨0, babyBearP_pos⟩),
      (fun _ => ⟨0, babyBearP_pos⟩), (fun _ => ⟨1, one_lt_babyBearP⟩)),
      fun l => QueryBounded.pure (Q l) _, fun _ _ => rfl⟩, ?_⟩
  intro l
  refine @winProb_pos_of_witness _ ((cellRootsRomForgery D tagDec m).game.instFin l) _
    (fun _ => ⟨0, by positivity⟩) ?_
  refine (Dregg2.Crypto.FloorGames.Adversary.hit_eq_true _ l _).mpr ⟨?_, rfl⟩
  intro hcon
  have h0 : (⟨0, babyBearP_pos⟩ : Fin babyBearP) = ⟨1, one_lt_babyBearP⟩ :=
    congrFun hcon ⟨0, by norm_num [N_SYSTEM_ROOTS]⟩
  have : (0 : ℕ) = 1 := congrArg Fin.val h0
  omega

/-- **(TOOTH — the class is INHABITED with POSITIVE advantage.)** The `0`-query constant answerer on
two distinct sub-blocks is in the class at every budget and wins with positive probability at every
parameter — the binding above bounds something genuinely nonzero. -/
theorem sysRootsRom_class_inhabited_pos (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (m : ℕ) (Q : ℕ → ℕ) :
    ∃ A, RomCarrierEff (sysRomFamily D tagDec m) (rootsRomCarrier D tagDec m) Q A
      ∧ ∀ l, 0 < gameAdv (sysRootsRomGame D tagDec m) A l := by
  obtain ⟨t₀⟩ := D.tagNonempty
  refine ⟨romCarrierAdv _ _ (constTripleComp _ _ (fun _ => (t₀, ()))
      (fun _ _ => ⟨0, babyBearP_pos⟩) (fun _ _ => ⟨1, one_lt_babyBearP⟩)),
    constTriple_in_eff _ _ _ _ _ Q, fun l => constTriple_gameAdv_pos _ _ _ _ _ l ?_⟩
  intro hcon
  have h0 : (⟨0, babyBearP_pos⟩ : Fin babyBearP) = ⟨1, one_lt_babyBearP⟩ :=
    congrFun hcon ⟨0, by norm_num [N_SYSTEM_ROOTS]⟩
  have : (0 : ℕ) = 1 := congrArg Fin.val h0
  omega

/-- **(TOOTH — the `shortCollAdv` shape is ADMITTED and DEFANGED, at this site.)** The exact answerer
shape that refutes the `IsPolyTime` floor (§6) — a `0`-query constant answer — is in the query class,
and the binding applies to it: its advantage is NEGLIGIBLE against the sampled oracle, where against
the fixed sponge it won with probability `1`.  The counterexample dies here, per §7's floor. -/
theorem sysRootsRom_constAnswer_defanged (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (m : ℕ) (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (c : ∀ l, (rootsRomCarrier D tagDec m).Ctx l)
    (v w : ∀ l, (rootsRomCarrier D tagDec m).Val l) :
    Negl (gameAdv (sysRootsRomGame D tagDec m)
      (romCarrierAdv _ _ (constTripleComp _ _ c v w))) :=
  constTriple_binds _ _ c v w Q hQ (sysRomFamily_card_R D tagDec m)

/-- **(TOOTH — a non-negligible forger is OUTSIDE the class.)** The general exclusion at this site:
the refutation strategy that killed the `IsPolyTime` floor cannot produce a member of this one. -/
theorem sysRootsRom_nonNegl_forger_excluded (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (m : ℕ) (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (sysRootsRomGame D tagDec m))
    (hnn : ¬ Negl (gameAdv (sysRootsRomGame D tagDec m) A)) :
    ¬ RomCarrierEff (sysRomFamily D tagDec m) (rootsRomCarrier D tagDec m) Q A :=
  romCarrier_choiceForger_excluded _ _ Q hQ (sysRomFamily_card_R D tagDec m) A hnn

#assert_axioms rootsEnc_faithful
#assert_axioms commitEnc_faithful
#assert_axioms rootsEnc_inj
#assert_axioms sysRoots_forgery_is_break
#assert_axioms cellCommitS_forgery_is_break
#assert_axioms rootsEnc_width
#assert_axioms commitEnc_width
#assert_axioms sysRoots_binds_advantage_bound
#assert_axioms cellRootsForgery_wins_iff
#assert_axioms chain_wins_imp
#assert_axioms cellRoots_binds_advantage_bound
#assert_axioms sysRomFamily_card_R
#assert_axioms truncRoots_inj
#assert_axioms truncRoots_rootList
#assert_axioms sysRootsRom_forgery_is_break
#assert_axioms cellCommitSRom_forgery_is_break
#assert_axioms sysRoots_binds_rom
#assert_axioms cellCommitS_binds_rom
#assert_axioms cellRoots_binds_rom
#assert_axioms cellRootsRom_class_inhabited_pos
#assert_axioms sysRootsRom_class_inhabited_pos
#assert_axioms sysRootsRom_constAnswer_defanged
#assert_axioms sysRootsRom_nonNegl_forger_excluded
#assert_axioms sysRoots_floor_top_false_babyBear
#assert_axioms sysRoots_floor_bot_vacuous
#assert_axioms sysRoots_polyTime_class_inhabited
#assert_axioms the_reduced_sysRoots_bound_fires
#assert_axioms sysRoots_no_reflexive_break
#assert_axioms isPolyTime_of_polySize_answers
#assert_axioms exists_short_collision
#assert_axioms shortCollAdv_wins
#assert_axioms shortCollAdv_isPolyTime
#assert_axioms sysRoots_floor_polyTime_false_babyBear

end Dregg2.Exec.SystemRootsBindingReduction
