/-
# `Dregg2.Circuit.CommitDifferentialRom` — the deployed `CellState::compute_commitment` bindings
(`record_digest`, `cap_root`) as REDUCTIONS on the PROVED keyed-ROM floor.

## What this replaces, and why a disjunction could not be the export

`CommitDifferential` models the deployed per-cell commitment (the `hash_4_to_1` two-level nest over
the ordered 13-limb list, `record_digest` at index 12, `cap_root` at index 11) and exported its
binding as `…_or_collides` DISJUNCTIONS — "the limb is bound OR here are the colliding quads". At
deployed BabyBear parameters a collision of the compressing `ℤ⁴ → ℤ` compress EXISTS by pigeonhole
(`InjectiveFloorRegrounded.compress4_not_injective_babyBear`), so a bare disjunction holds through
its right branch with NO binding: it is an extractor witness, not a security statement.

The security statement lives here. The deployed 13-column nested commitment at the SAMPLED oracle
is `EffectVmRowCommitReduction.narrowRomCommit` — `H (t, inr ((H(t,A), H(t,B), H(t,C)), d))` over
the three GROUP-4 state blocks and the record-digest felt — and its full equivocation is already
priced by `narrowRow_binds_rom` (the two-carrier union bound on `keyedRom_hard`, the birthday
bound, PROVED). This module supplies the two LOCALIZED tamper forgeries the `CommitDifferential`
headlines state — the disagreement pinned to the `record_digest` felt, and pinned to the `cap_root`
slot inside block C — and closes each as a reduction INTO the full narrow forgery: a localized
disagreement is payload distinctness, so the tamper forger IS a narrow forger.

  * `effectVmCommit_binds_record_digest_rom` — the audit-P0-2 anti-ghost tooth, DISCHARGED: a
    query-bounded adversary cannot keep the published commitment while tampering the authority
    residue, except with negligible probability. Successor of
    `effectVmCommit_binds_record_digest_or_collides` (which is RETAINED in `CommitDifferential`
    as the extractor witness its `RotatedCommitDifferential` consumer still `rcases` on).
  * `effectVmCommit_binds_cap_root_rom` — the cap-root twin, DISCHARGED. Its disjunction
    predecessor `effectVmCommit_binds_cap_root_or_collides` had NO consumers and is DELETED from
    `CommitDifferential` in the same commit this lands.

## The named correspondence, pinned

`narrowValOfLimbs` is the 13-limb field correspondence at the truncated widths — the SAME block
partition the Rust nesting absorbs: `A = [bal_lo, bal_hi, nonce, fields[0]]`,
`B = fields[1..5]`, `C = [fields[5], fields[6], fields[7], cap_root]`, outer felt =
`record_digest`. The projection pins tie the two tamper coordinates to their
`CommitDifferential.effectVmLimbs` positions (`record_digest_at_index_12`; `cap_root` = C slot 3 =
index 11), and `narrowValOfLimbs_inj` is the losslessness tooth: distinct deployed limb tuples stay
distinct ROM payloads.

## ⚑ The modelling step (inherited, said out loud)

The `RomCarrierSites` header discipline: the sampled `H` replaces the fixed public `hash_4_to_1`;
inner digests are ideal `Fin (2 ^ l)` values (no `l` is the deployed ~31-bit felt); the fixed
hash's own collision resistance stays a conjecture. What the move buys over the disjunction: the
floor under the export is a THEOREM instead of a branch that is free at deployed parameters.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no fresh `axiom`, no
`native_decide`.
-/
import Dregg2.Circuit.CommitDifferential
import Dregg2.Circuit.Emit.EffectVmRowCommitReduction

namespace Dregg2.Circuit.CommitDifferentialRom

open Dregg2.Circuit.Emit.EffectVmRowCommitReduction
  (narrowRomFamily NarrowRomVal StateBlock4 narrowRomCommit effectVmNarrowRomForgery
   narrowRow_binds_rom)
open Dregg2.Crypto.SpongeCarrierReduction (SpongeKeyed)
open Dregg2.Crypto.RomCarrierSites (RomForgery RomForgeryEff babyBearP)
open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)
open Dregg2.Crypto.FloorGames (Game Adversary gameAdv gameAdv_mem_unit)
open Dregg2.Crypto.ProbCrypto (winProb_le_of_imp negl_of_le)
open Dregg2.Crypto.ConcreteSecurity (Negl PolyBounded)

set_option autoImplicit false

/-! ## §1 — the named 13-limb correspondence at the truncated widths. -/

/-- The 13 deployed limbs, partitioned into the Rust absorb's three GROUP-4 blocks and the
record-digest felt — `effectVmLimbs`' order, `narrowRomCommit`'s shape. -/
def narrowValOfLimbs (balLo balHi nonce : Fin babyBearP) (fields : Fin 8 → Fin babyBearP)
    (capRoot recordDigest : Fin babyBearP) : NarrowRomVal :=
  ((![balLo, balHi, nonce, fields 0],
    ![fields 1, fields 2, fields 3, fields 4],
    ![fields 5, fields 6, fields 7, capRoot]), recordDigest)

/-- **THE `record_digest` POSITION PIN** — the outer fourth slot, the same authority-residue
position `CommitDifferential.record_digest_at_index_12` pins on the deployed limb list. -/
theorem narrowValOfLimbs_recordDigest (balLo balHi nonce : Fin babyBearP)
    (fields : Fin 8 → Fin babyBearP) (capRoot recordDigest : Fin babyBearP) :
    (narrowValOfLimbs balLo balHi nonce fields capRoot recordDigest).2 = recordDigest := rfl

/-- **THE `cap_root` POSITION PIN** — block C's fourth slot (deployed limb index 11). -/
theorem narrowValOfLimbs_capRoot (balLo balHi nonce : Fin babyBearP)
    (fields : Fin 8 → Fin babyBearP) (capRoot recordDigest : Fin babyBearP) :
    (narrowValOfLimbs balLo balHi nonce fields capRoot recordDigest).1.2.2 3 = capRoot := rfl

/-- **THE CORRESPONDENCE LOSES NOTHING** — two 13-limb tuples with one ROM payload are equal
limb-for-limb, so the ROM forgeries quantify over everything the deployed prover can absorb. -/
theorem narrowValOfLimbs_inj {balLo balHi nonce : Fin babyBearP} {fields : Fin 8 → Fin babyBearP}
    {capRoot recordDigest : Fin babyBearP}
    {balLo' balHi' nonce' : Fin babyBearP} {fields' : Fin 8 → Fin babyBearP}
    {capRoot' recordDigest' : Fin babyBearP}
    (h : narrowValOfLimbs balLo balHi nonce fields capRoot recordDigest
       = narrowValOfLimbs balLo' balHi' nonce' fields' capRoot' recordDigest') :
    balLo = balLo' ∧ balHi = balHi' ∧ nonce = nonce' ∧ fields = fields'
      ∧ capRoot = capRoot' ∧ recordDigest = recordDigest' := by
  have hA : (![balLo, balHi, nonce, fields 0] : StateBlock4)
      = ![balLo', balHi', nonce', fields' 0] := congrArg (fun v : NarrowRomVal => v.1.1) h
  have hB : (![fields 1, fields 2, fields 3, fields 4] : StateBlock4)
      = ![fields' 1, fields' 2, fields' 3, fields' 4] :=
    congrArg (fun v : NarrowRomVal => v.1.2.1) h
  have hC : (![fields 5, fields 6, fields 7, capRoot] : StateBlock4)
      = ![fields' 5, fields' 6, fields' 7, capRoot'] :=
    congrArg (fun v : NarrowRomVal => v.1.2.2) h
  have hrd : recordDigest = recordDigest' := congrArg (fun v : NarrowRomVal => v.2) h
  have ha0 : balLo = balLo' := congrFun hA 0
  have ha1 : balHi = balHi' := congrFun hA 1
  have ha2 : nonce = nonce' := congrFun hA 2
  have ha3 : fields 0 = fields' 0 := congrFun hA 3
  have hb0 : fields 1 = fields' 1 := congrFun hB 0
  have hb1 : fields 2 = fields' 2 := congrFun hB 1
  have hb2 : fields 3 = fields' 3 := congrFun hB 2
  have hb3 : fields 4 = fields' 4 := congrFun hB 3
  have hc0 : fields 5 = fields' 5 := congrFun hC 0
  have hc1 : fields 6 = fields' 6 := congrFun hC 1
  have hc2 : fields 7 = fields' 7 := congrFun hC 2
  have hc3 : capRoot = capRoot' := congrFun hC 3
  refine ⟨ha0, ha1, ha2, funext fun i => ?_, hc3, hrd⟩
  fin_cases i <;> assumption

/-! ## §2 — the RECORD-DIGEST tamper, DISCHARGED (the audit-P0-2 anti-ghost tooth). -/

/-- **THE RECORD-DIGEST ROM TAMPER** — the disagreement localized to the authority-residue felt:
two truncated 13-limb payloads whose `record_digest` felts DIFFER yet whose deployed nested
commitments AGREE at the sampled oracle. -/
def recordDigestRomTamper (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) :
    RomForgery (narrowRomFamily D tagDec) where
  Ans := fun _ => D.Tag × NarrowRomVal × NarrowRomVal
  wins := fun l H a =>
    a.2.1.2 ≠ a.2.2.2
      ∧ narrowRomCommit D tagDec l H a.1 a.2.1 = narrowRomCommit D tagDec l H a.1 a.2.2
  winsDec := fun l _ _ => by
    letI := ((narrowRomFamily D tagDec).toRomFamily).rDec l
    exact instDecidableAnd

/-- **⚑⚑ `effectVmCommit_binds_record_digest_rom` — THE audit-P0-2 TOOTH, AS A REDUCTION ON THE
PROVED FLOOR.** A query-bounded adversary that keeps the published per-cell commitment while
tampering ONLY the authority residue (a permission flip, a VK swap, a dropped side-table root) has
NEGLIGIBLE advantage: a record-digest disagreement is payload distinctness, so the tamper forger
IS a narrow full-state forger, and `narrowRow_binds_rom` (the union bound on `keyedRom_hard` — the
birthday bound, a THEOREM) kills it. NO bare disjunction, NO refuted floor. The ROM successor of
`CommitDifferential.effectVmCommit_binds_record_digest_or_collides`. -/
theorem effectVmCommit_binds_record_digest_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (recordDigestRomTamper D tagDec).game)
    (hA : RomForgeryEff (narrowRomFamily D tagDec) (recordDigestRomTamper D tagDec) Q A) :
    Negl (gameAdv (recordDigestRomTamper D tagDec).game A) := by
  obtain ⟨M, hM, hrun⟩ := hA
  have hgen : Negl (gameAdv (effectVmNarrowRomForgery D tagDec).game
      (⟨A.run⟩ : Adversary (effectVmNarrowRomForgery D tagDec).game)) :=
    narrowRow_binds_rom D tagDec Q hQ
      (⟨A.run⟩ : Adversary (effectVmNarrowRomForgery D tagDec).game) ⟨M, hM, hrun⟩
  refine negl_of_le
    (fun l => (gameAdv_mem_unit (recordDigestRomTamper D tagDec).game A l).1)
    (fun l => ?_) hgen
  refine @winProb_le_of_imp _ ((recordDigestRomTamper D tagDec).game.instFin l) _ _
    (fun H hH => ?_)
  replace hH := (Dregg2.Crypto.FloorGames.Adversary.hit_eq_true _ _ _).mp hH
  refine (Dregg2.Crypto.FloorGames.Adversary.hit_eq_true _ _ _).mpr ?_
  obtain ⟨hne, heq⟩ := hH
  exact ⟨fun hc => hne (congrArg Prod.snd hc), heq⟩

/-! ## §3 — the CAP-ROOT tamper, DISCHARGED. -/

/-- **THE CAP-ROOT ROM TAMPER** — the disagreement localized to block C's fourth slot (deployed
limb index 11): a forged openable c-list root under a kept commitment. -/
def capRootRomTamper (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) :
    RomForgery (narrowRomFamily D tagDec) where
  Ans := fun _ => D.Tag × NarrowRomVal × NarrowRomVal
  wins := fun l H a =>
    a.2.1.1.2.2 3 ≠ a.2.2.1.2.2 3
      ∧ narrowRomCommit D tagDec l H a.1 a.2.1 = narrowRomCommit D tagDec l H a.1 a.2.2
  winsDec := fun l _ _ => by
    letI := ((narrowRomFamily D tagDec).toRomFamily).rDec l
    exact instDecidableAnd

/-- **⚑⚑ `effectVmCommit_binds_cap_root_rom` — THE CAP-ROOT BINDING, AS A REDUCTION ON THE PROVED
FLOOR.** A query-bounded adversary that keeps the published per-cell commitment while moving the
`cap_root` limb has NEGLIGIBLE advantage — a slot disagreement inside block C is payload
distinctness, so `narrowRow_binds_rom` applies. The ROM successor of (and the same-commit
replacement for) the DELETED `effectVmCommit_binds_cap_root_or_collides`, whose two-branch case
split (inner quad vs root quad) is exactly the union bound `narrowRow_binds_rom` performs at the
sampled oracle. -/
theorem effectVmCommit_binds_cap_root_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (capRootRomTamper D tagDec).game)
    (hA : RomForgeryEff (narrowRomFamily D tagDec) (capRootRomTamper D tagDec) Q A) :
    Negl (gameAdv (capRootRomTamper D tagDec).game A) := by
  obtain ⟨M, hM, hrun⟩ := hA
  have hgen : Negl (gameAdv (effectVmNarrowRomForgery D tagDec).game
      (⟨A.run⟩ : Adversary (effectVmNarrowRomForgery D tagDec).game)) :=
    narrowRow_binds_rom D tagDec Q hQ
      (⟨A.run⟩ : Adversary (effectVmNarrowRomForgery D tagDec).game) ⟨M, hM, hrun⟩
  refine negl_of_le
    (fun l => (gameAdv_mem_unit (capRootRomTamper D tagDec).game A l).1)
    (fun l => ?_) hgen
  refine @winProb_le_of_imp _ ((capRootRomTamper D tagDec).game.instFin l) _ _
    (fun H hH => ?_)
  replace hH := (Dregg2.Crypto.FloorGames.Adversary.hit_eq_true _ _ _).mp hH
  refine (Dregg2.Crypto.FloorGames.Adversary.hit_eq_true _ _ _).mpr ?_
  obtain ⟨hne, heq⟩ := hH
  exact ⟨fun hc => hne (congrArg (fun v : NarrowRomVal => v.1.2.2 3) hc), heq⟩

/-! ## §4 — non-fake teeth: the tamper games are winnable, the admitted refuter-shape is defanged,
and a non-negligible tamperer is outside the class. -/

/-- **(TOOTH — the record-digest tamper class is INHABITED, WINS somewhere, and is DEFANGED.)**
The `0`-query constant answerer on two payloads differing only in the residue felt is in the class
at every budget; at the constant oracle both nested commitments collapse, so it WINS there
(positive advantage); and the binding applies to it — NEGLIGIBLE advantage. Against the FIXED
compress the same shape wins with probability `1`. -/
theorem recordDigestTamper_constAnswer_defanged (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (t₀ : D.Tag) (v w : NarrowRomVal) (hvw : v.2 ≠ w.2) :
    ∃ A, RomForgeryEff (narrowRomFamily D tagDec) (recordDigestRomTamper D tagDec) Q A
      ∧ Negl (gameAdv (recordDigestRomTamper D tagDec).game A)
      ∧ ∀ l, 0 < gameAdv (recordDigestRomTamper D tagDec).game A l := by
  refine ⟨⟨fun _ _ => (t₀, v, w)⟩,
    ⟨fun _ => OracleComp.pure (t₀, v, w), fun l => QueryBounded.pure (Q l) _, fun _ _ => rfl⟩,
    effectVmCommit_binds_record_digest_rom D tagDec Q hQ _
      ⟨fun _ => OracleComp.pure (t₀, v, w), fun l => QueryBounded.pure (Q l) _, fun _ _ => rfl⟩,
    fun l => ?_⟩
  obtain ⟨r₀⟩ : Nonempty ((narrowRomFamily D tagDec).toRomFamily.R l) :=
    ((narrowRomFamily D tagDec).toRomFamily).rNe l
  refine @Dregg2.Crypto.RomCarrierSites.winProb_pos_of_witness _
    ((recordDigestRomTamper D tagDec).game.instFin l) _ (fun _ => r₀) ?_
  exact (Dregg2.Crypto.FloorGames.Adversary.hit_eq_true _ l _).mpr ⟨hvw, rfl⟩

/-- **(TOOTH — a non-negligible record-digest tamperer is OUTSIDE the class.)** -/
theorem recordDigestTamper_nonNegl_excluded (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (recordDigestRomTamper D tagDec).game)
    (hnn : ¬ Negl (gameAdv (recordDigestRomTamper D tagDec).game A)) :
    ¬ RomForgeryEff (narrowRomFamily D tagDec) (recordDigestRomTamper D tagDec) Q A :=
  fun hA => hnn (effectVmCommit_binds_record_digest_rom D tagDec Q hQ A hA)

/-- **(TOOTH — a non-negligible cap-root tamperer is OUTSIDE the class.)** -/
theorem capRootTamper_nonNegl_excluded (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (capRootRomTamper D tagDec).game)
    (hnn : ¬ Negl (gameAdv (capRootRomTamper D tagDec).game A)) :
    ¬ RomForgeryEff (narrowRomFamily D tagDec) (capRootRomTamper D tagDec) Q A :=
  fun hA => hnn (effectVmCommit_binds_cap_root_rom D tagDec Q hQ A hA)

/-! ## §5 — axiom hygiene. -/

#assert_axioms narrowValOfLimbs_recordDigest
#assert_axioms narrowValOfLimbs_capRoot
#assert_axioms narrowValOfLimbs_inj
#assert_axioms effectVmCommit_binds_record_digest_rom
#assert_axioms effectVmCommit_binds_cap_root_rom
#assert_axioms recordDigestTamper_constAnswer_defanged
#assert_axioms recordDigestTamper_nonNegl_excluded
#assert_axioms capRootTamper_nonNegl_excluded

end Dregg2.Circuit.CommitDifferentialRom
