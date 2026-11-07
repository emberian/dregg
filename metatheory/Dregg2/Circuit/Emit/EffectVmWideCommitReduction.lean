/-
# `Dregg2.Circuit.Emit.EffectVmWideCommitReduction` — the WIDE `state_commit` anti-ghost, REBUILT as a
SECURITY REDUCTION on the grounded floor.

## What was here before, and why it was still a shirk

`Dregg2.Circuit.Emit.EffectVmFullStateRunnable` exports the whole commitment-binding core of the
RUNNABLE (`system_roots`-absorbing) EffectVM descriptor as FIVE bare disjunctions:

    wide_binds_or_collides                    (cols = cols ∧ carrier = carrier) ∨ WideColl …
    wide_binds_systemRoots_or_collides         (∀ i, sr₁ i = sr₂ i) ∨ WideColl … ∨ RootsColl …
    runnable_full_commit_binds_or_collides     (cols = cols ∧ ∀ i, sr₁ i = sr₂ i) ∨ WideColl ∨ RootsColl
    wide_rejects_state_tamper_or_collides      WideColl … ∨ RootsColl …
    wide_rejects_root_tamper_or_collides       WideColl … ∨ RootsColl …

Each was a genuine repair of a VACUOUS predecessor — they used to carry
`Poseidon2Binding.Poseidon2SpongeCR hash`, which the deployed BabyBear sponge REFUTES
(`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`), so the old forms said nothing at all about the
deployed circuit.  But a bare `binds ∨ collides` is still a SHIRK: at deployed parameters a sponge
collision EXISTS by pigeonhole, so the disjunction is satisfiable through the `collides` branch with
`binds` never holding.  It quantifies over SOLUTIONS.  Cryptographic hardness quantifies over
EFFICIENT ADVERSARIES.  And the two `_rejects_*_tamper` teeth are the worst of the five: their
CONCLUSION is nothing BUT the two collision disjuncts, so as exported statements they promise a
tamper "costs" something whose price was never named.

⚑ **THOSE FIVE ARE NOT THE HEADLINE ANY MORE.**  This module supplies the headline, and
`EffectVmFullStateRunnable`'s docstrings now say so: the five disjunctions are DEMOTED to the
exact-Prop skeleton the win relations rest on (and to the base of the `_of_injective` strength
bridges), exactly as `Dregg2.Exec.SystemRoots` was demoted by
`Dregg2.Exec.SystemRootsBindingReduction` and `Market.WideCommitBoundary` demoted
`stateDecode8_pre_faithful`.  They are RETAINED rather than deleted because ~40 per-effect wide
keystones (bridgeMint, createCell, cellSeal, setPermissions, refreshDelegation, revokeDelegation,
pipelinedSend, exercise, noop, …) instantiate them as their deterministic skeleton; the EXPORTED
security claim about the wide commitment is now `wideCommit_binds_advantage_bound` /
`wideFullState_binds_advantage_bound` (fixed hash, `hEff` in the open) and the DISCHARGED
`wideCommit_binds_rom` / `wideFullState_binds_rom` below (keyed-ROM floor, PROVED — the
`_from_polyTime` discharges that stood here carried a refuted floor and are DELETED).

## The shape, and what it costs

The primitive is the deployed domain-separated Poseidon2 sponge
(`Crypto.SpongeCarrierReduction.spongeFamily D`) — the real `List ℤ → ℤ` the prover computes, keyed
by the tag it absorbs.  The whole reduction is inherited from
`Dregg2.Crypto.SpongeCarrierReduction`; this file supplies only

  * the two deployed CARRIERS — `wideAbsorbCarrier` (the `H4`-of-`H4` over the 12 absorbed
    state-block columns plus the `sysRootsDigestCol` felt) and `wideFullCarrier` (the same, with the
    carrier slot resolved to the `systemRootsDigest` of an eight-root sub-block),
  * their COLLISION EXTRACTORS, which are the file's OWN existing extraction spine reused rather than
    re-authored: `Poseidon2Binding.group4Find` for the GROUP-4 peel and
    `Exec.SystemRoots.rootsCollFind` for the roots peel, composed into ONE total function
    (`wideFullFind`) so the three-way disjunction becomes ONE extracted finder rather than a union
    bound over two,
  * the STRUCTURAL injectivity of the 12-column layout (`WideCols.eq_of_blocks`) — a fact about the
    LIMB LAYOUT, never about the hash,
  * the fixed widths (four felts per GROUP-4 block, eight per root sub-block) that discharge the
    `poly_time` output-growth slot.

Every deployed statement the five disjunctions made is re-expressed as "this configuration IS a win of
the forgery game" (`wideAbsorb_forgery_is_break`, `wideFull_forgery_is_break`,
`runnable_full_forgery_is_break`, `wide_state_tamper_is_break`, `wide_root_tamper_is_break`), and the
game's advantage is NEGLIGIBLE under the named floor.

⚑ **THE RESIDUAL, NAMED.** The floor is `HashCRHardQuant (spongeFamily D) Eff`, and at `Eff := ⊤` it
is FALSE at deployed BabyBear parameters (§5 — the honest price), at `Eff := ⊥` vacuous.
`Eff := IsPolyTime` sits strictly between: the ⊤-collapse witness is PROVED excluded
(`CostAdversary.bruteForce_not_polyTime`) and the class is PROVED inhabited.  What the rebuild buys is
not a floor the deployed sponge satisfies at ⊤ — no such floor exists — it is that the residual is ONE
named parameter with both poles proved, instead of a disjunct that is unconditionally available.

What it does NOT buy: the exact-Prop AIR layer and the computational game layer are still bridged
per-instance (the game samples a tag; a deployed trace fixes `deployedTag`), and the per-cell `Value`
`restLimbs` residuals (`slotCaveats`/`factories`/`lifecycle`/`deathCert`/`delegate`) ride
`CommitmentCrossBind.LeafIsCellCommit`, a separately-priced layer.

No `sorry`, no `axiom`, no `native_decide`, no `decide` on an opaque `Prop`.  Cost stays SYNTACTIC.
-/
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable
import Dregg2.Circuit.Emit.EffectVmRowCommitReduction
import Dregg2.Crypto.SpongeCarrierReduction

namespace Dregg2.Circuit.Emit.EffectVmWideCommitReduction

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (wideHashSites baseAbsorbedCols wideCommitOf wide_commit_eq wideBlockA wideBlockB wideBlockC
   wideCollFind RunnableFullStateSpec)
open Dregg2.Circuit.Poseidon2Binding (SpongeColl group4Find group4Find_spec)
open Dregg2.Exec.SystemRoots
  (SysRoots systemRootsDigest systemRootsDigest_eq_hash_rootList rootList rootsCollFind RootsColl
   systemRootsDigest_binds_or_collides N_SYSTEM_ROOTS)
open Dregg2.Crypto.SpongeCarrierReduction
  (SpongeKeyed SpongeCarrier IsSpongeColl spongeFamily carrierBreakGame carrierBreakToFinder
   carrier_adv_le carrier_binds_advantage_bound carrierAnsSize
   spongeAnsSize carrierFloor_top_false_babyBear carrierFloor_bot_vacuous
   carrierFloor_isPolyTime_inhabited)
open Dregg2.Crypto.FloorGames (Game Adversary gameAdv hashGame HashCRHardQuant)
open Dregg2.Crypto.CostAdversary (AnsSize IsPolyTime)
open Dregg2.Crypto.ConcreteSecurity (Negl)

set_option autoImplicit false

/-! ## §1 — the 12 absorbed state-block columns, AS DATA, and their structural injectivity.

The deployed wide commitment absorbs exactly twelve state-block columns
(`bal_lo, bal_hi, nonce, fields[0..7], cap_root`) in three GROUP-4 blocks, plus the
`sysRootsDigestCol` carrier at the fourth outer slot.  `WideCols` is that twelve-felt payload as a
first-class value, so the forgery game has a DOMAIN to quantify over rather than a row environment.
Its `blkA`/`blkB`/`blkC` are the deployed blocks verbatim (`rowCols_blkA` etc. pin them by `rfl`). -/

/-- **The twelve absorbed state-block columns of a WIDE row, as data.** The domain the deployed wide
`state_commit` claims to bind (together with the side-table carrier, §2). -/
structure WideCols where
  /-- `state_after.balance_lo`. -/
  balLo : ℤ
  /-- `state_after.balance_hi`. -/
  balHi : ℤ
  /-- `state_after.nonce`. -/
  nonce : ℤ
  /-- `state_after.fields[0]`. -/
  f0 : ℤ
  /-- `state_after.fields[1]`. -/
  f1 : ℤ
  /-- `state_after.fields[2]`. -/
  f2 : ℤ
  /-- `state_after.fields[3]`. -/
  f3 : ℤ
  /-- `state_after.fields[4]`. -/
  f4 : ℤ
  /-- `state_after.fields[5]`. -/
  f5 : ℤ
  /-- `state_after.fields[6]`. -/
  f6 : ℤ
  /-- `state_after.fields[7]`. -/
  f7 : ℤ
  /-- `state_after.cap_root`. -/
  capRoot : ℤ
deriving DecidableEq

namespace WideCols

/-- The FIRST deployed GROUP-4 block: `bal_lo, bal_hi, nonce, fields[0]`. -/
def blkA (v : WideCols) : List ℤ := [v.balLo, v.balHi, v.nonce, v.f0]

/-- The SECOND deployed GROUP-4 block: `fields[1..4]`. -/
def blkB (v : WideCols) : List ℤ := [v.f1, v.f2, v.f3, v.f4]

/-- The THIRD deployed GROUP-4 block: `fields[5..7], cap_root`. -/
def blkC (v : WideCols) : List ℤ := [v.f5, v.f6, v.f7, v.capRoot]

/-- The twelve columns in deployed absorption order. -/
def toList (v : WideCols) : List ℤ := blkA v ++ blkB v ++ blkC v

/-- **THE STRUCTURAL INJECTIVITY — about the LIMB LAYOUT, never about the hash.** The three GROUP-4
blocks jointly recover the whole twelve-felt payload.  This is the fact that turns a block-level
agreement into a payload-level agreement inside the extractor's correctness proof; it carries no
hypothesis on the sponge whatsoever. -/
theorem eq_of_blocks {a b : WideCols} (hA : blkA a = blkA b) (hB : blkB a = blkB b)
    (hC : blkC a = blkC b) : a = b := by
  cases a
  cases b
  simp_all [blkA, blkB, blkC]

/-- The ordered twelve-column list determines the payload — the `toList` projection of
`eq_of_blocks`. -/
theorem toList_inj {a b : WideCols} (h : toList a = toList b) : a = b := by
  cases a
  cases b
  simp_all [toList, blkA, blkB, blkC]

/-- Each GROUP-4 block is exactly four felts wide — the deployed arity, and the fact that discharges
the extractor's output-growth obligation. -/
theorem blk_len (v : WideCols) :
    (blkA v).length = 4 ∧ (blkB v).length = 4 ∧ (blkC v).length = 4 := by
  simp [blkA, blkB, blkC]

end WideCols

/-- **THE DEPLOYED READ-OFF.** A wide row's twelve absorbed state-block columns, as a `WideCols`. -/
def rowCols (env : VmRowEnv) : WideCols where
  balLo   := env.loc (saCol state.BALANCE_LO)
  balHi   := env.loc (saCol state.BALANCE_HI)
  nonce   := env.loc (saCol state.NONCE)
  f0      := env.loc (saCol (state.FIELD_BASE + 0))
  f1      := env.loc (saCol (state.FIELD_BASE + 1))
  f2      := env.loc (saCol (state.FIELD_BASE + 2))
  f3      := env.loc (saCol (state.FIELD_BASE + 3))
  f4      := env.loc (saCol (state.FIELD_BASE + 4))
  f5      := env.loc (saCol (state.FIELD_BASE + 5))
  f6      := env.loc (saCol (state.FIELD_BASE + 6))
  f7      := env.loc (saCol (state.FIELD_BASE + 7))
  capRoot := env.loc (saCol state.CAP_ROOT)

/-- **FAITHFULNESS (columns).** The read-off's ordered list IS the deployed `baseAbsorbedCols` — by
`rfl`, so the forgery domain is the very payload the existing keystones talk about. -/
theorem rowCols_toList (env : VmRowEnv) : (rowCols env).toList = baseAbsorbedCols env := rfl

/-- **FAITHFULNESS (blocks).** The read-off's GROUP-4 blocks ARE the deployed `wideBlockA/B/C`. -/
theorem rowCols_blk (env : VmRowEnv) :
    (rowCols env).blkA = wideBlockA env ∧ (rowCols env).blkB = wideBlockB env
      ∧ (rowCols env).blkC = wideBlockC env :=
  ⟨rfl, rfl, rfl⟩

/-! ## §2 — CARRIER 1: the wide commitment binds its twelve columns AND the side-table carrier felt.

This is the reduction that replaces `wide_binds_or_collides` — the GENERIC ROOT every per-effect wide
keystone instantiates.  The bound domain is `WideCols × ℤ`: the twelve state-block columns and the
`sysRootsDigestCol` carrier read as an opaque felt (the carrier is NOT assumed to be a roots digest
here; that is §3's stronger carrier). -/

/-- The domain the wide `state_commit` binds: twelve absorbed columns + the side-table carrier felt. -/
abbrev WideAbsorbed : Type := WideCols × ℤ

/-- **THE DEPLOYED WIDE COMMITMENT**, as a function of the payload: the `H4`-of-`H4` whose fourth
outer slot is the `system_roots` carrier.  Definitionally `wideCommitOf` at the payload's fields, so
this is the function the prover computes, not a re-derivation of it. -/
def wideAbsorbEnc (h : List ℤ → ℤ) (v : WideAbsorbed) : ℤ :=
  h [h v.1.blkA, h v.1.blkB, h v.1.blkC, v.2]

/-- The deployed `wideCommitOf` IS `wideAbsorbEnc` at the payload read-off — by `rfl`. -/
theorem wideAbsorbEnc_eq_wideCommitOf (h : List ℤ → ℤ) (v : WideAbsorbed) :
    wideAbsorbEnc h v
      = wideCommitOf h v.1.balLo v.1.balHi v.1.nonce v.1.f0 v.1.f1 v.1.f2 v.1.f3 v.1.f4
          v.1.f5 v.1.f6 v.1.f7 v.1.capRoot v.2 := rfl

/-- **THE EXTRACTOR — the file's OWN GROUP-4 peel, reused.** `Poseidon2Binding.group4Find` is a TOTAL
function that, from two absorptions publishing one digest, either proves the four slots equal or hands
back the specific pair of lists at which the deployed sponge collides.  No parallel copy: this is
literally the spine `EffectVmFullStateRunnable.wideCollFind` already walks. -/
def wideAbsorbFind (h : List ℤ → ℤ) (a b : WideAbsorbed) : List ℤ × List ℤ :=
  group4Find h a.1.blkA a.1.blkB a.1.blkC a.2 b.1.blkA b.1.blkB b.1.blkC b.2

/-- **⚑ THE EXTRACTOR IS CORRECT, UNCONDITIONALLY.** Two DISTINCT payloads publishing the SAME wide
commitment yield a genuine collision of the deployed sponge.  No injectivity, no floor, no hypothesis
on `h` — which is exactly why (unlike the binding it replaces) it is a true theorem at deployed
BabyBear parameters. -/
theorem wideAbsorbFind_spec (h : List ℤ → ℤ) (a b : WideAbsorbed) (hne : a ≠ b)
    (heq : wideAbsorbEnc h a = wideAbsorbEnc h b) : IsSpongeColl h (wideAbsorbFind h a b) := by
  have heq' : h [h a.1.blkA, h a.1.blkB, h a.1.blkC, a.2]
      = h [h b.1.blkA, h b.1.blkB, h b.1.blkC, b.2] := heq
  rcases group4Find_spec h a.1.blkA a.1.blkB a.1.blkC a.2 b.1.blkA b.1.blkB b.1.blkC b.2 heq'
    with ⟨hA, hB, hC, hd⟩ | hcoll
  · refine absurd ?_ hne
    have hcols : a.1 = b.1 := WideCols.eq_of_blocks hA hB hC
    have hcar : a.2 = b.2 := hd
    cases a
    cases b
    simp_all
  · exact hcoll

/-- **THE EXTRACTOR DOES NOT BLOW UP ITS INPUT** — every branch of the GROUP-4 peel returns two
four-felt lists (an outer `H4` argument list, or one inner block pair), so the output is at most eight
felts whatever the adversary does.  PROVED, not assumed; this is the cost model's output-growth
obligation. -/
theorem wideAbsorbFind_len_le (h : List ℤ → ℤ) (a b : WideAbsorbed) :
    (wideAbsorbFind h a b).1.length + (wideAbsorbFind h a b).2.length ≤ 8 := by
  unfold wideAbsorbFind group4Find
  split_ifs <;> simp [WideCols.blkA, WideCols.blkB, WideCols.blkC]

/-- **⚑ CARRIER 1 — the deployed wide `state_commit`, with its collision extractor.** The whole
per-site content of the rebuilt `wide_binds_or_collides`: one commitment, one total extractor, one
unconditional correctness theorem, one proved output bound. -/
def wideAbsorbCarrier : SpongeCarrier where
  Ctx := Unit
  Val := WideAbsorbed
  valDecEq := inferInstance
  enc := fun h _ v => wideAbsorbEnc h v
  find := fun h _ a b => wideAbsorbFind h a b
  find_spec := fun h _ a b hne heq => wideAbsorbFind_spec h a b hne heq
  size := fun _ _ => 13
  outCo := 0
  outBo := 8
  find_len_le := fun h _ a b => by simpa using wideAbsorbFind_len_le h a b

/-- The wide row's forgery payload: its twelve absorbed columns and its side-table carrier. -/
def rowAbsorbed (env : VmRowEnv) : WideAbsorbed := (rowCols env, env.loc sysRootsDigestCol)

/-- **⚑ THE REDUCTION'S INTERNAL WITNESS IS THE FILE'S OWN EXTRACTOR.** The carrier's `find` at two
deployed rows IS `EffectVmFullStateRunnable.wideCollFind` — by `rfl`.  So the `_or_collides` keystones'
extractor has not been replaced, it has been DEMOTED to its correct role: the witness inside a
reduction, rather than an exported escape branch. -/
theorem wideAbsorbCarrier_find_eq_wideCollFind (h : List ℤ → ℤ) (e₁ e₂ : VmRowEnv) :
    wideAbsorbCarrier.find h () (rowAbsorbed e₁) (rowAbsorbed e₂) = wideCollFind h e₁ e₂ := rfl

/-- **FAITHFULNESS.** A wide row satisfying the deployed hash-sites publishes exactly the carrier's
commitment of its own payload — the repackaging of `wide_commit_eq`. -/
theorem rowAbsorbed_commit (h : List ℤ → ℤ) (env : VmRowEnv)
    (hs : siteHoldsAll h env wideHashSites) :
    env.loc (saCol state.STATE_COMMIT) = wideAbsorbEnc h (rowAbsorbed env) :=
  wide_commit_eq h env hs

/-- The forgery payloads of two rows agree exactly when the deployed absorbed columns and carriers
do — so the game's win relation is stated in the DEPLOYED vocabulary, not a re-encoding of it. -/
theorem rowAbsorbed_eq_iff (e₁ e₂ : VmRowEnv) :
    rowAbsorbed e₁ = rowAbsorbed e₂ ↔
      (baseAbsorbedCols e₁ = baseAbsorbedCols e₂
        ∧ e₁.loc sysRootsDigestCol = e₂.loc sysRootsDigestCol) := by
  constructor
  · intro h
    have hc : rowCols e₁ = rowCols e₂ := congrArg Prod.fst h
    refine ⟨?_, congrArg Prod.snd h⟩
    rw [← rowCols_toList, ← rowCols_toList, hc]
  · rintro ⟨hcols, hd⟩
    have hc : rowCols e₁ = rowCols e₂ := by
      refine WideCols.toList_inj ?_
      rw [rowCols_toList, rowCols_toList]
      exact hcols
    show (rowCols e₁, e₁.loc sysRootsDigestCol) = (rowCols e₂, e₂.loc sysRootsDigestCol)
    rw [hc, hd]

/-- **⚑ THE FORGERY IS THE DEPLOYED ANTI-GHOST VIOLATION.** Two wide rows publishing the SAME
`state_commit` that DISAGREE on any absorbed state-block column or on the side-table carrier ARE a win
of the forgery game.  This is the statement `wide_binds_or_collides` was reaching for, with the escape
PRICED instead of offered. -/
theorem wideAbsorb_forgery_is_break (D : SpongeKeyed) (l : ℕ) (t : D.Tag) (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll (D.hashAt t) e₁ wideHashSites)
    (hs₂ : siteHoldsAll (D.hashAt t) e₂ wideHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT))
    (htamper : ¬ (baseAbsorbedCols e₁ = baseAbsorbedCols e₂
        ∧ e₁.loc sysRootsDigestCol = e₂.loc sysRootsDigestCol)) :
    (carrierBreakGame D wideAbsorbCarrier).wins l t ((), rowAbsorbed e₁, rowAbsorbed e₂) := by
  refine ⟨fun heq => htamper ((rowAbsorbed_eq_iff e₁ e₂).mp heq), ?_⟩
  show wideAbsorbEnc (D.hashAt t) (rowAbsorbed e₁) = wideAbsorbEnc (D.hashAt t) (rowAbsorbed e₂)
  rw [← rowAbsorbed_commit _ _ hs₁, ← rowAbsorbed_commit _ _ hs₂]
  exact hcommit

/-- **⚑ THE WIDE COMMITMENT BINDING — the headline, at an arbitrary adversary class.** Under the
deployed sponge's collision floor, a forger of the wide `state_commit` whose extracted finder is in the
class has NEGLIGIBLE advantage: the published commitment binds all twelve absorbed state-block columns
AND the side-table carrier except with negligible probability.  `hEff` is the honest open obligation;
the next theorem discharges it. -/
theorem wideCommit_binds_advantage_bound (D : SpongeKeyed)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (carrierBreakGame D wideAbsorbCarrier))
    (hEff : Eff (carrierBreakToFinder D wideAbsorbCarrier A))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (carrierBreakGame D wideAbsorbCarrier) A) :=
  carrier_binds_advantage_bound D wideAbsorbCarrier Eff A hEff hCR

/-- **⚑⚑ THE WIDE COMMITMENT BINDING, DISCHARGED ON THE PROVED FLOOR** — the successor of the
deleted `wideCommit_binds_from_polyTime`, whose `IsPolyTime` floor
`Exec.SystemRootsBindingReduction.sysRoots_floor_polyTime_false_babyBear` refutes. The bound domain
`WideCols × ℤ` — twelve absorbed columns in three GROUP-4 blocks plus one opaque carrier felt,
absorbed as `h [h A, h B, h C, felt]` — is EXACTLY the nested shape
`EffectVmRowCommitReduction.effectVmNarrowRomForgery` transposes to the sampled oracle (three
truncated blocks, one payload felt in the outer absorb), so the successor is that chained binding,
reused rather than re-minted: every query-bounded forger of the nested commitment has NEGLIGIBLE
advantage, in the keyed ROM model of that file's §5 header. NO floor hypothesis. -/
theorem wideCommit_binds_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ)
    (hQ : Dregg2.Crypto.ConcreteSecurity.PolyBounded
      (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (Dregg2.Circuit.Emit.EffectVmRowCommitReduction.effectVmNarrowRomForgery
      D tagDec).game)
    (hA : Dregg2.Crypto.RomCarrierSites.RomForgeryEff
      (Dregg2.Circuit.Emit.EffectVmRowCommitReduction.narrowRomFamily D tagDec)
      (Dregg2.Circuit.Emit.EffectVmRowCommitReduction.effectVmNarrowRomForgery D tagDec) Q A) :
    Negl (gameAdv (Dregg2.Circuit.Emit.EffectVmRowCommitReduction.effectVmNarrowRomForgery
      D tagDec).game A) :=
  Dregg2.Circuit.Emit.EffectVmRowCommitReduction.narrowRow_binds_rom D tagDec Q hQ A hA

/-! ## §3 — CARRIER 2: the wide commitment binds the WHOLE 17-field post-state.

The carrier slot resolved to the `systemRootsDigest` of an eight-root sub-block.  This is the
reduction that replaces `wide_binds_systemRoots_or_collides`,
`runnable_full_commit_binds_or_collides`, `wide_rejects_state_tamper_or_collides` and
`wide_rejects_root_tamper_or_collides` — all four were the SAME binding, projected four ways, which is
precisely why four bare disjunctions were four copies of one unpriced escape.

⚑ **THE THREE-WAY DISJUNCTION BECOMES ONE FINDER, NOT A UNION BOUND.** `wideFullFind` composes the
GROUP-4 peel and the roots peel into ONE total function: run the GROUP-4 extractor, and if the pair it
returns is not a genuine collision then the four outer slots agreed, so the two sub-blocks share a
digest and the roots peel is the collision.  So the reduction loses no tightness — the forger's
advantage is bounded by ONE collision finder's, not a sum of two. -/

/-- The domain the wide commitment binds when its carrier is a `system_roots` digest: the twelve
absorbed state-block columns AND the eight-root side-table sub-block. -/
abbrev WideFull : Type := WideCols × SysRoots

/-- **THE DEPLOYED WIDE COMMITMENT OF A FULL POST-STATE** — the `H4`-of-`H4` whose fourth outer slot
is the `systemRootsDigest` of the sub-block, exactly as the runnable descriptor's `sysRootsAbsorbSite`
computes it. -/
def wideFullEnc (h : List ℤ → ℤ) (v : WideFull) : ℤ :=
  h [h v.1.blkA, h v.1.blkB, h v.1.blkC, systemRootsDigest h v.2]

/-- **THE COMPOSED EXTRACTOR — both deployed peels, as ONE total function.** Try the GROUP-4 peel; if
the pair it returns is a genuine collision, that is the answer.  Otherwise the four outer slots agreed,
so the two sub-blocks published one digest and the roots peel (`rootsCollFind`, `Exec.SystemRoots`'s
own) is the collision.  Both peels are reused, not re-authored, and the branch is `Decidable`
(`Poseidon2Binding.decidableSpongeColl`) so the walk is total with no `Classical.choice`. -/
def wideFullFind (h : List ℤ → ℤ) (a b : WideFull) : List ℤ × List ℤ :=
  if SpongeColl h (group4Find h a.1.blkA a.1.blkB a.1.blkC (systemRootsDigest h a.2)
                              b.1.blkA b.1.blkB b.1.blkC (systemRootsDigest h b.2)) then
    group4Find h a.1.blkA a.1.blkB a.1.blkC (systemRootsDigest h a.2)
                 b.1.blkA b.1.blkB b.1.blkC (systemRootsDigest h b.2)
  else rootsCollFind a.2 b.2

/-- **⚑ THE COMPOSED EXTRACTOR IS CORRECT, UNCONDITIONALLY.** Two DISTINCT full post-states publishing
the SAME wide commitment yield a genuine collision of the deployed sponge — at the GROUP-4 layer if the
absorbed blocks or the digests differ, at the roots layer otherwise.  No injectivity, no floor. -/
theorem wideFullFind_spec (h : List ℤ → ℤ) (a b : WideFull) (hne : a ≠ b)
    (heq : wideFullEnc h a = wideFullEnc h b) : IsSpongeColl h (wideFullFind h a b) := by
  by_cases hcoll : SpongeColl h (group4Find h a.1.blkA a.1.blkB a.1.blkC (systemRootsDigest h a.2)
      b.1.blkA b.1.blkB b.1.blkC (systemRootsDigest h b.2))
  · show IsSpongeColl h (wideFullFind h a b)
    unfold wideFullFind
    rw [if_pos hcoll]
    exact hcoll
  · show IsSpongeColl h (wideFullFind h a b)
    unfold wideFullFind
    rw [if_neg hcoll]
    have heq' : h [h a.1.blkA, h a.1.blkB, h a.1.blkC, systemRootsDigest h a.2]
        = h [h b.1.blkA, h b.1.blkB, h b.1.blkC, systemRootsDigest h b.2] := heq
    rcases group4Find_spec h a.1.blkA a.1.blkB a.1.blkC (systemRootsDigest h a.2)
      b.1.blkA b.1.blkB b.1.blkC (systemRootsDigest h b.2) heq' with ⟨hA, hB, hC, hd⟩ | hc
    · have hcols : a.1 = b.1 := WideCols.eq_of_blocks hA hB hC
      rcases systemRootsDigest_binds_or_collides h a.2 b.2 hd with hlist | hrc
      · refine absurd ?_ hne
        have hroots : a.2 = b.2 := List.ofFn_inj.mp hlist
        cases a
        cases b
        simp_all
      · exact hrc
    · exact absurd hc hcoll

/-- **THE COMPOSED EXTRACTOR DOES NOT BLOW UP ITS INPUT** — at most eight felts from the GROUP-4
branch (two four-felt lists) and sixteen from the roots branch (two eight-root lists), a CONSTANT
either way.  PROVED, not assumed. -/
theorem wideFullFind_len_le (h : List ℤ → ℤ) (a b : WideFull) :
    (wideFullFind h a b).1.length + (wideFullFind h a b).2.length ≤ 16 := by
  unfold wideFullFind
  split_ifs
  · unfold group4Find
    split_ifs <;> simp [WideCols.blkA, WideCols.blkB, WideCols.blkC]
  · simp only [rootsCollFind,
      Dregg2.Circuit.Emit.EffectVmRowCommitReduction.rootList_length_eight] <;> decide

/-- **⚑ CARRIER 2 — the deployed wide `state_commit` over a FULL post-state, with its extractor.** -/
def wideFullCarrier : SpongeCarrier where
  Ctx := Unit
  Val := WideFull
  valDecEq := inferInstance
  enc := fun h _ v => wideFullEnc h v
  find := fun h _ a b => wideFullFind h a b
  find_spec := fun h _ a b hne heq => wideFullFind_spec h a b hne heq
  size := fun _ _ => 20
  outCo := 0
  outBo := 16
  find_len_le := fun h _ a b => by simpa using wideFullFind_len_le h a b

/-- The full-state forgery payload of a wide row against a side-table sub-block. -/
def rowFull (env : VmRowEnv) (sr : SysRoots) : WideFull := (rowCols env, sr)

/-- **FAITHFULNESS.** A wide row satisfying the deployed hash-sites, whose carrier IS the
`systemRootsDigest` of `sr`, publishes exactly the carrier's commitment of its full post-state. -/
theorem rowFull_commit (h : List ℤ → ℤ) (env : VmRowEnv) (sr : SysRoots)
    (hs : siteHoldsAll h env wideHashSites)
    (hd : env.loc sysRootsDigestCol = systemRootsDigest h sr) :
    env.loc (saCol state.STATE_COMMIT) = wideFullEnc h (rowFull env sr) := by
  rw [wide_commit_eq h env hs, hd]
  rfl

/-- **⚑ THE FULL-STATE FORGERY IS THE DEPLOYED ANTI-GHOST VIOLATION.** Two wide rows publishing the
SAME `state_commit`, with `systemRootsDigest` carriers, that DISAGREE on any absorbed state-block
column OR on any side-table root ARE a win.  This is what
`runnable_full_commit_binds_or_collides` / `wide_binds_systemRoots_or_collides` were reaching for. -/
theorem wideFull_forgery_is_break (D : SpongeKeyed) (l : ℕ) (t : D.Tag)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hs₁ : siteHoldsAll (D.hashAt t) e₁ wideHashSites)
    (hs₂ : siteHoldsAll (D.hashAt t) e₂ wideHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT))
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₂)
    (htamper : ¬ (baseAbsorbedCols e₁ = baseAbsorbedCols e₂
        ∧ ∀ i : Fin N_SYSTEM_ROOTS, sr₁ i = sr₂ i)) :
    (carrierBreakGame D wideFullCarrier).wins l t ((), rowFull e₁ sr₁, rowFull e₂ sr₂) := by
  refine ⟨?_, ?_⟩
  · intro heq
    have hc : rowCols e₁ = rowCols e₂ := congrArg Prod.fst heq
    have hr : sr₁ = sr₂ := congrArg Prod.snd heq
    refine htamper ⟨?_, ?_⟩
    · rw [← rowCols_toList, ← rowCols_toList, hc]
    · intro i
      exact congrFun hr i
  · show wideFullEnc (D.hashAt t) (rowFull e₁ sr₁) = wideFullEnc (D.hashAt t) (rowFull e₂ sr₂)
    rw [← rowFull_commit _ _ _ hs₁ hd₁, ← rowFull_commit _ _ _ hs₂ hd₂]
    exact hcommit

/-- **⚑ THE PER-CELL-BLOCK TAMPER IS A WIN** — what replaces
`wide_rejects_state_tamper_or_collides`.  A forged balance, a tampered field, a forged cap-root that
still claims the published commitment is not merely "a named collision": it is a WIN of a game whose
advantage §4 bounds. -/
theorem wide_state_tamper_is_break (D : SpongeKeyed) (l : ℕ) (t : D.Tag)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hs₁ : siteHoldsAll (D.hashAt t) e₁ wideHashSites)
    (hs₂ : siteHoldsAll (D.hashAt t) e₂ wideHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT))
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₂)
    (htamper : baseAbsorbedCols e₁ ≠ baseAbsorbedCols e₂) :
    (carrierBreakGame D wideFullCarrier).wins l t ((), rowFull e₁ sr₁, rowFull e₂ sr₂) :=
  wideFull_forgery_is_break D l t e₁ e₂ sr₁ sr₂ hs₁ hs₂ hcommit hd₁ hd₂ (fun h => htamper h.1)

/-- **⚑ THE SIDE-TABLE TAMPER IS A WIN** — what replaces `wide_rejects_root_tamper_or_collides`, the
gap's headline tooth.  A dropped escrow, an omitted nullifier, a reordered queue under a fixed
`NEW_COMMIT` is a win of a game whose advantage §4 bounds. -/
theorem wide_root_tamper_is_break (D : SpongeKeyed) (l : ℕ) (t : D.Tag)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hs₁ : siteHoldsAll (D.hashAt t) e₁ wideHashSites)
    (hs₂ : siteHoldsAll (D.hashAt t) e₂ wideHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT))
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) :
    (carrierBreakGame D wideFullCarrier).wins l t ((), rowFull e₁ sr₁, rowFull e₂ sr₂) :=
  wideFull_forgery_is_break D l t e₁ e₂ sr₁ sr₂ hs₁ hs₂ hcommit hd₁ hd₂ (fun h => htamper (h.2 i))

/-- **⚑ THE GENERIC RUNNABLE-DESCRIPTOR FORGERY** — what replaces
`runnable_full_commit_binds_or_collides`, the single highest-fanout disjunction in the tree.  Two rows
SATISFYING the effect's wide runnable descriptor (`satisfiedVm`) that publish the SAME `NEW_COMMIT`,
with `systemRootsDigest` carriers, and disagree on any of the seventeen fields' bound content, ARE a
win.  Generic in `St` and in the effect's `RunnableFullStateSpec`, so every per-effect instantiation
inherits the reduction rather than a disjunction. -/
theorem runnable_full_forgery_is_break {St : Type} (E : RunnableFullStateSpec St)
    (D : SpongeKeyed) (l : ℕ) (t : D.Tag)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm (D.hashAt t) E.descriptor e₁ true true)
    (hsat₂ : satisfiedVm (D.hashAt t) E.descriptor e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₂)
    (htamper : ¬ (baseAbsorbedCols e₁ = baseAbsorbedCols e₂
        ∧ ∀ i : Fin N_SYSTEM_ROOTS, sr₁ i = sr₂ i)) :
    (carrierBreakGame D wideFullCarrier).wins l t ((), rowFull e₁ sr₁, rowFull e₂ sr₂) := by
  have hs₁ : siteHoldsAll (D.hashAt t) e₁ wideHashSites := E.usesWideSites ▸ hsat₁.2.1
  have hs₂ : siteHoldsAll (D.hashAt t) e₂ wideHashSites := E.usesWideSites ▸ hsat₂.2.1
  refine wideFull_forgery_is_break D l t e₁ e₂ sr₁ sr₂ hs₁ hs₂ ?_ hd₁ hd₂ htamper
  rw [hpin₁, hpin₂, hpub]

/-! ## §4 — THE HEADLINE BINDINGS, with efficiency DISCHARGED. -/

/-- **⚑ THE FULL-STATE BINDING — the headline, at an arbitrary adversary class.** Under the deployed
sponge's collision floor, a forger of the wide full-state commitment whose extracted finder is in the
class has NEGLIGIBLE advantage: the runnable descriptor's published `state_commit` binds the whole
seventeen-field post-state — the twelve absorbed columns AND all eight side-table roots — except with
negligible probability.  `hEff` is the honest open obligation. -/
theorem wideFullState_binds_advantage_bound (D : SpongeKeyed)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (carrierBreakGame D wideFullCarrier))
    (hEff : Eff (carrierBreakToFinder D wideFullCarrier A))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (carrierBreakGame D wideFullCarrier) A) :=
  carrier_binds_advantage_bound D wideFullCarrier Eff A hEff hCR

/-- **⚑⚑ THE FULL-STATE BINDING, DISCHARGED ON THE PROVED FLOOR — the exported anti-ghost claim of
the RUNNABLE descriptor.** The successor of the deleted `wideFullState_binds_from_polyTime` (floor
refuted, see `wideCommit_binds_rom`'s docstring). The bound domain `WideCols × SysRoots` — the whole
17-field post-state — is EXACTLY the shape `EffectVmRowCommitReduction.effectVmWideRomForgery`
transposes to the sampled oracle (three truncated state blocks plus the eight-root sub-block, the
inner digests re-absorbed by the outer query), so the successor is that chained binding: every
query-bounded forger of the whole nested post-state commitment has NEGLIGIBLE advantage. What
replaced the four `_or_collides` projections stays ONE binding — now with the floor PROVED
(`keyedRom_hard`, the birthday bound) instead of refutable. -/
theorem wideFullState_binds_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ)
    (hQ : Dregg2.Crypto.ConcreteSecurity.PolyBounded
      (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (Dregg2.Circuit.Emit.EffectVmRowCommitReduction.wideRomBreakGame D tagDec))
    (hA : Dregg2.Crypto.RomCarrierSites.RomForgeryEff
      (Dregg2.Circuit.Emit.EffectVmRowCommitReduction.wideRomFamily D tagDec)
      (Dregg2.Circuit.Emit.EffectVmRowCommitReduction.effectVmWideRomForgery D tagDec) Q A) :
    Negl (gameAdv (Dregg2.Circuit.Emit.EffectVmRowCommitReduction.wideRomBreakGame D tagDec) A) :=
  Dregg2.Circuit.Emit.EffectVmRowCommitReduction.wideRow_binds_rom D tagDec Q hQ A hA

/-- **THE ADVANTAGE INEQUALITY, UNCONDITIONAL — the adversary class does NOT appear.** Re-exported at
this site so the reduction's load-bearing step is visible here and not only in the spine: the wide
forger's advantage is at most the extracted collision finder's, at every parameter, over the same
sampled tag space.  `Eff` enters ONLY when the floor is applied. -/
theorem wideFullState_adv_le (D : SpongeKeyed)
    (A : Adversary (carrierBreakGame D wideFullCarrier)) (l : ℕ) :
    gameAdv (carrierBreakGame D wideFullCarrier) A l
      ≤ gameAdv (hashGame (spongeFamily D)) (carrierBreakToFinder D wideFullCarrier A) l :=
  carrier_adv_le D wideFullCarrier A l

/-! ## §5 — the floor PRICED at both poles, the inhabitation tooth, and the canaries. -/

/-- **⚑ THE ⊤ POLE — the floor is FALSE at the REAL BabyBear parameters** (the honest price of `hEff`).
A sponge whose output is a genuine BabyBear felt has finite range while `List ℤ` is infinite, so a
collision exists at every tag and the floor at the UNRESTRICTED class is FALSE.  What the rebuild buys
is not a floor the deployed sponge satisfies at ⊤ — no such floor exists — it is ONE named parameter
with both poles proved, in place of a disjunct that is unconditionally available. -/
theorem wideCommit_floor_top_false_babyBear (D : SpongeKeyed)
    (hb : ∀ xs, 0 ≤ D.sponge xs ∧ D.sponge xs < (2013265921 : ℤ)) :
    ¬ HashCRHardQuant (spongeFamily D) (fun _ => True) :=
  carrierFloor_top_false_babyBear D hb

/-- **THE ⊥ POLE — vacuous.** Recorded so the floor's satisfiability can never be mistaken for
evidence. -/
theorem wideCommit_floor_bot_vacuous (D : SpongeKeyed) :
    HashCRHardQuant (spongeFamily D) (fun _ => False) :=
  carrierFloor_bot_vacuous D

/-- **(TOOTH — the class §4 instantiates at is NOT EMPTY.)** The constant finder is in
`IsPolyTime (spongeAnsSize D)`, so `Eff := IsPolyTime` is not `⊥` in disguise.  With
`CostAdversary.bruteForce_not_polyTime` (the ⊤-collapse witness PROVED excluded) this pins the
instantiated floor strictly between the two poles. -/
theorem wideCommit_polyTime_class_inhabited (D : SpongeKeyed) :
    IsPolyTime (spongeAnsSize D)
      (Dregg2.Crypto.CostAdversary.idAdv (O := Unit) (Q := fun _ => Unit) (R := fun _ => Unit)
        (fun _ _ => (([] : List ℤ), ([] : List ℤ)))).toAdversary :=
  carrierFloor_isPolyTime_inhabited D

/-- **(CANARY — the binding does NOT follow from the floor applied at ANOTHER finder.)** Strip the
reduction: try to conclude the wide forger's negligibility from the collision floor at some OTHER
adversary `B`, rather than the one EXTRACTED from it.  It does not go through — only
`wideFullState_adv_le` connects the two games.  This tooth REDS if a future edit collapses them. -/
example (D : SpongeKeyed)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (carrierBreakGame D wideFullCarrier))
    (B : Adversary (hashGame (spongeFamily D))) (hB : Eff B)
    (hCR : HashCRHardQuant (spongeFamily D) Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (carrierBreakGame D wideFullCarrier) A) := hCR B hB)
  trivial

/-- **THE POSITIVE POLE — the RIGHT floor DOES discharge it.** A gate that refuses everything is a
broken keystone, not a fixed one: with the floor at the EXTRACTED finder the binding fires. -/
theorem the_reduced_wide_bound_fires (D : SpongeKeyed)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (carrierBreakGame D wideFullCarrier))
    (hEff : Eff (carrierBreakToFinder D wideFullCarrier A))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (carrierBreakGame D wideFullCarrier) A) :=
  wideFullState_binds_advantage_bound D Eff A hEff hCR

/-- **(TOOTH — a REFLEXIVE answer is never a win, at ANY sponge.)** The game does not hand the
adversary a free win, so the negligibility above is not the negligibility of an unwinnable game's
advantage in disguise.  The computational twin of `EffectVmFullStateRunnable.wideColl_irrefl`. -/
theorem no_reflexive_wide_break (D : SpongeKeyed) (l : ℕ) (t : D.Tag) (v : WideAbsorbed) :
    ¬ (carrierBreakGame D wideAbsorbCarrier).wins l t ((), v, v) := by
  rintro ⟨hne, -⟩
  exact hne rfl

/-- **(TOOTH — a REFLEXIVE full-state answer is never a win either.)** -/
theorem no_reflexive_wideFull_break (D : SpongeKeyed) (l : ℕ) (t : D.Tag) (v : WideFull) :
    ¬ (carrierBreakGame D wideFullCarrier).wins l t ((), v, v) := by
  rintro ⟨hne, -⟩
  exact hne rfl

/-- **(TOOTH — the win relation is NOT vacuously unsatisfiable.)** At a totally broken sponge (the
constant `0`), two payloads differing only in `cap_root` publish one commitment, so the forgery game IS
winnable.  Together with the reflexive tooth this pins the game as two-valued: it is neither a free
pass nor an empty promise. -/
theorem wide_break_reachable_at_broken_sponge (D : SpongeKeyed) (l : ℕ) (t : D.Tag)
    (hbroken : ∀ xs : List ℤ, D.hashAt t xs = 0) :
    (carrierBreakGame D wideAbsorbCarrier).wins l t
      ((), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)) := by
  refine ⟨?_, ?_⟩
  · intro h
    have := congrArg (fun p => p.1.capRoot) h
    simp at this
  · show wideAbsorbEnc (D.hashAt t) _ = wideAbsorbEnc (D.hashAt t) _
    unfold wideAbsorbEnc
    rw [hbroken, hbroken]

/-! ## §6 — axiom-hygiene pins. -/

#assert_axioms WideCols.eq_of_blocks
#assert_axioms WideCols.toList_inj
#assert_axioms WideCols.blk_len
#assert_axioms rowCols_toList
#assert_axioms rowCols_blk
#assert_axioms wideAbsorbEnc_eq_wideCommitOf
#assert_axioms wideAbsorbFind_spec
#assert_axioms wideAbsorbFind_len_le
#assert_axioms wideAbsorbCarrier_find_eq_wideCollFind
#assert_axioms rowAbsorbed_commit
#assert_axioms rowAbsorbed_eq_iff
#assert_axioms wideAbsorb_forgery_is_break
#assert_axioms wideCommit_binds_advantage_bound
#assert_axioms wideCommit_binds_rom
#assert_axioms wideFullFind_spec
#assert_axioms wideFullFind_len_le
#assert_axioms rowFull_commit
#assert_axioms wideFull_forgery_is_break
#assert_axioms wide_state_tamper_is_break
#assert_axioms wide_root_tamper_is_break
#assert_axioms runnable_full_forgery_is_break
#assert_axioms wideFullState_binds_advantage_bound
#assert_axioms wideFullState_binds_rom
#assert_axioms wideFullState_adv_le
#assert_axioms wideCommit_floor_top_false_babyBear
#assert_axioms wideCommit_floor_bot_vacuous
#assert_axioms wideCommit_polyTime_class_inhabited
#assert_axioms the_reduced_wide_bound_fires
#assert_axioms no_reflexive_wide_break
#assert_axioms no_reflexive_wideFull_break
#assert_axioms wide_break_reachable_at_broken_sponge

end Dregg2.Circuit.Emit.EffectVmWideCommitReduction
