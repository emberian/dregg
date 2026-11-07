/-
# Market.WideCommitBoundary — the faithful eight-lane light-client boundary.

The generic circuit apex historically collapsed a deployed state commitment to one `ℤ`.
This module keeps the deployed shape: the commitment is the eight-felt result of the
`wireCommitR8` chain over a `rotatedNumPreLimbs`-limb kernel payload, with the receipt-log root absorbed
last.  The payload's first limb is the already-proved `CommitSurface.commit`; the
remaining 183 lanes are domain-separated headroom for the deployed layout.  Thus the
wide chain adds no new trust: the wide commitment recovers the entire payload and receipt
root, then `CommitSurface.commit_binds` recovers the kernel.

## ⚑ THE HEADLINE BINDING IS A SECURITY REDUCTION, not a disjunction (§R).

The anchor `turn/src/state_commit.rs` consumes is the wide `STATE_COMMIT` carrier
(`wireCommitR8` / `wire_commit_8_chip`).  Its binding used to be exported as the bare
disjunction `stateDecode8_pre_faithful : pre = pre' ∨ WireColl …` — the extraction-as-data
keystone that replaced the FALSE `Poseidon2WideCR` injectivity.  That was true at deployed
BabyBear parameters (unlike injectivity), but it is still a SHIRK: a collision EXISTS at
those parameters by pigeonhole (`VacuitySweepTeeth.widePerm_not_injective_babyBear`), so
`binds ∨ collides` is satisfiable through the `collides` branch WITHOUT `binds` ever
holding.  It NAMES the floor; it does not STAND on it.  It quantifies over SOLUTIONS
(a collision exists), where cryptographic hardness quantifies over EFFICIENT ADVERSARIES.

§R rebuilds it with the correct structure — a SECURITY REDUCTION to a NAMED hardness
assumption over EFFICIENT ADVERSARIES:

  * the honest floor is `FloorGames.HashCRHardQuant (wideFamily D) Eff` — a real collision
    game of the deployed wide permutation at an explicit adversary class `Eff`, negligible
    advantage.  It is NOT injectivity (false), NOT `∃ collision` (a solution).  Both poles
    are proved in `InjectiveFloorRegrounded` §3.6: `Eff := ⊤` is FALSE at deployed BabyBear
    params (the honest price of `hEff`), `Eff := ⊥` is vacuous.
  * a state-endpoint forgery is a first-class `Game` (`stateCommitBreakGame`): the adversary
    wins iff it outputs two chained states whose wide-chain inputs DIFFER yet publish the
    SAME eight-felt commit.  `stateDecode8_forgery_is_break` ties it to the deployed
    `StateDecode8` decode object.
  * the reduction (`stateCommit_binds_advantage_bound`) is the EXTRACTOR as a map of
    adversaries: a state forgery → (`stateBreakToWireBreak`) a wire-commit equivocation →
    (`wireBreakToFinder`, via `wireCommit8Find`) a genuine `permW` collision.  Under the
    named floor with the `hEff` obligation on the composed finder, a state forgery has
    NEGLIGIBLE advantage.  The `_binds_or_collides` extractor is the reduction's INTERNAL
    witness, NOT the headline.

The exact-Prop `stateDecode8_pre_faithful`/`_post_faithful` are RETAINED below as the
deterministic backbone (they are what the win relation rests on), explicitly demoted from
"the deployed binding" to "the exact-Prop skeleton".

## ⚑ THE CROSS-LAYER BRIDGE, and what remains (named, not faked).

The reduction closes the WIDE component of the anchor binding.  A state forgery whose wide
inputs AGREE while the states differ is NOT caught by the wide floor — it is a collision of
the receipt-root sponge — ⚑ as of 2026-08-01 that leg is no longer the refuted floor
`Poseidon2SpongeCR hash` but the per-instance `SpongeColl hash (receiptRootFind hash L L')`, a
FOURTH named disjunct at the exact-Prop backbone, worth ≈2^15.5 queries at the 1-felt root — or of
the kernel commit (`CommitSurface.commit_binds`, its own field).
Those are the SEPARATELY-priced residuals, named at `stateDecode8_pre_faithful`.  What is
NOT yet closed: the exact-Prop AIR layer and the computational game layer are still bridged
per-instance (the game samples a tag; the deployed trace fixes `deployedTag`).

`Eff` at the discharge site: an earlier §P instantiated it at
`Dregg2.Crypto.CostAdversary.IsPolyTime` and derived the composed finder's efficiency — but
that floor is REFUTED HERE (§P, `stateCommit_floor_polyTime_false_babyBear`): `IsPolyTime`
prices answer SIZE, so the `Classical.choice` adversary answering every sampled tag with a
short collision that EXISTS by pigeonhole is in the class and wins with probability `1`.
The discharged theorem was therefore VACUOUS at deployed BabyBear parameters, and it is
DELETED.  The honest discharge is §Q/§S: the chain is modeled as an ORACLE COMPUTATION —
each absorption step a `query` node (`wireCommitComp`, eval-equal to the deployed
`wireCommitR8`) — and the binding is re-grounded on the KEYED, QUERY-COUNTED sampled-oracle
floor (`KeyedRomFloor.keyedRom_hard`, the birthday bound, a THEOREM), where the
choice-answerer is PROVABLY excluded.  ⚑ That re-grounding is a MODELLING step (the standard
random-oracle idealization of the deployed sponge at an asymptotic digest width — `hw`
demands `|R l| = 2^l`, unsatisfiable by the fixed 31-bit BabyBear felt), taken deliberately
and LABELLED in §S, not smuggled.  §R's general `stateCommit_binds_advantage_bound` keeps
the `Eff`/`hEff` parameters, since it is the statement at an arbitrary adversary class.

No axiom, `sorry`, `admit`, or native decision procedure.
-/
import Dregg2.Circuit.CircuitSoundness
import Dregg2.Circuit.Emit.EffectVmEmitRotationR
import Dregg2.Circuit.Emit.RotatedLayout
import Dregg2.Circuit.InjectiveFloorRegrounded
import Dregg2.Crypto.CostAdversary
import Dregg2.Crypto.RomChainedReduction
import Dregg2.Tactics

namespace Market.WideCommitBoundary

open Dregg2.Exec
open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.Emit.EffectVmEmitRotationR
  (Poseidon2Width8 chainFrom8 chainFrom8_len chainFrom8_snoc wireCommitR8 WireColl
   wireCommitR8_binds_or_collides chunk31 chunk31_length chunkCount chainCollFind
   wireCommit8Find IsCollW)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR SpongeColl)
open Dregg2.Crypto.FloorGames
  (Game Adversary Hard gameAdv gameAdv_mem_unit hashGame HashCRHardQuant)
open Dregg2.Crypto.ConcreteSecurity (Negl PolyBounded not_negl_one)
open Dregg2.Crypto.CostAdversary (AnsSize IsPolyTime)
open Dregg2.Crypto.ProbCrypto (winProb_le_of_imp negl_of_le winProb_top)
open Dregg2.Circuit.InjectiveFloorRegrounded
  (WideKeyed wideFamily wireCommitBreakGame wireBreakToFinder wire_adv_le
   wireCommitR8_binds_advantage_bound wide_floor_top_false_babyBear wide_floor_bot_vacuous)
open Dregg2.Circuit.VacuitySweepTeeth (babyBearP finite_width8_bounded)
open Dregg2.Circuit.HashFloorHonesty (not_injective_of_finite_range)
open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)
open Dregg2.Crypto.KeyedRomFloor (KeyedRomFamily keyedRomGame keyedRom_top_false)
open Dregg2.Crypto.RomChainedReduction
  (chainEval chainComp chainComp_eval chainComp_queryBounded chainEval_const
   RomChainedCarrier romChainedGame romChainedGame_wins_iff RomChainedComp romChainedAdv
   RomChainedEff romChained_binds romChained_choiceForger_excluded fixedChainedComp
   fixedChainedForger_in_eff fixedChainedForger_negl romChainedGame_win_at_const)

set_option autoImplicit false

/-- The deployed endpoint payload width — READ from
`Dregg2.Circuit.Emit.RotatedLayout.rotatedNumPreLimbs`, not mirrored.

⚑ It was the literal `184` with a comment saying it mirrors that constant, a `#guard` at the foot of
this file pinning it against its own definition, and `deployed_blockCount` carrying the matching
schedule by hand.  When the 2026-08-01 KEY-NONET flag day took the extent to 187, none of that went
red: the width, the block count, the query budget and the ROM carrier's chain length all agreed WITH
EACH OTHER about a payload the deployed committer had stopped folding, and §Q's "the model IS the
deployed object" became false silently.  The whole schedule below is now derived from this one
constant, and this one constant is read from the layout. -/
def kernelPayloadWidth : Nat := Dregg2.Circuit.Emit.rotatedNumPreLimbs

/-- A full-width kernel payload.  Limb zero is the binding full-kernel commitment;
the remaining positions are explicit zero headroom in this abstract boundary codec.
The deployed descriptor refines this codec by replacing those zeroes with its named
rotated lanes; binding of the endpoint needs only the already-binding first limb. -/
def kernelPayload (S : CommitSurface) (k : RecordKernelState) (t : BoundaryTurn) : List ℤ :=
  S.commit k t :: List.replicate (kernelPayloadWidth - 1) 0

set_option maxRecDepth 1000 in
theorem kernelPayload_length (S : CommitSurface) (k : RecordKernelState) (t : BoundaryTurn) :
    (kernelPayload S k t).length = kernelPayloadWidth := by
  unfold kernelPayload
  rw [List.length_cons, List.length_replicate]
  decide

/-- The variable preimage of the deployed `hash_fact` chip.  Its fixed namespace
and padding words do not affect the injectivity argument, so the boundary keeps
only the predicate followed by its terms. -/
def factHash (hash : List ℤ → ℤ) (pred : ℤ) (terms : List ℤ) : ℤ :=
  hash (pred :: terms)

/-- One truthful balance receipt.  Ring actions have `actor = src`, but both
fields remain in the digest because both belong to `Turn`. -/
def turnDigest (hash : List ℤ → ℤ) (t : Turn) : ℤ :=
  factHash hash t.actor [t.src, t.dst, t.amt]

/-- The exact preimage the turn-digest absorption feeds the sponge, named so the collision event
below is stated at precisely the list the digest is taken of (`turnDigest hash t = hash (turnPre t)`
by `rfl`). -/
def turnPre (t : Turn) : List ℤ := t.actor :: [t.src, t.dst, t.amt]

/-- **⚑ THE TURN-DIGEST EXTRACTOR.** One absorption, so there is exactly one place two digests can
break: if the two preimages differ they ARE the collision. Total and decidable. -/
def turnDigestFind (a b : Turn) : List ℤ × List ℤ := (turnPre a, turnPre b)

/-- **⚑ THE TURN-DIGEST EXTRACTOR IS CORRECT — UNCONDITIONAL, NO FLOOR.** Two turns with the same
receipt digest EITHER are the same turn, OR the pair `turnDigestFind` returns is a GENUINE collision
of the deployed sponge. Nothing is assumed about `hash`, so — unlike `turnDigest_binds`'s old form —
this holds at deployed BabyBear parameters. -/
theorem turnDigest_binds_or_collides (hash : List ℤ → ℤ) (a b : Turn)
    (h : turnDigest hash a = turnDigest hash b) :
    a = b ∨ SpongeColl hash (turnDigestFind a b) := by
  by_cases hne : turnPre a = turnPre b
  · refine Or.inl ?_
    cases a
    cases b
    simp only [turnPre, List.cons.injEq, Nat.cast_inj] at hne
    simp_all
  · exact Or.inr ⟨hne, h⟩

/-- **`turnDigest_binds`, PORTED OFF `Poseidon2SpongeCR` (2026-08-01).** The floor is FALSE at
deployed BabyBear (`Circuit.HashFloorHonesty.poseidon2SpongeCR_false_babyBear`), so this said nothing
about the deployed committer. What it carries now is the DECIDABLE per-instance residual at the ONE
pair `turnDigestFind` names for THESE two turns; the honest single-turn case discharges it for every
sponge, and a caller holding the floor supplies
`Poseidon2Binding.spongeColl_refutable_of_injective _ hCR _`. -/
theorem turnDigest_binds (hash : List ℤ → ℤ)
    {a b : Turn} (hno : ¬ SpongeColl hash (turnDigestFind a b))
    (h : turnDigest hash a = turnDigest hash b) : a = b :=
  (turnDigest_binds_or_collides hash a b h).resolve_right hno

/-- Receipt-index root with the executor's prepend update.  The empty root has a
one-word preimage; every action step has a two-word preimage, so log length is
also bound by collision resistance. -/
def receiptRoot (hash : List ℤ → ℤ) : List Turn → ℤ
  | [] => factHash hash 0 []
  | t :: ts => factHash hash (receiptRoot hash ts) [turnDigest hash t]

/-- The exact preimage each receipt-root absorption feeds the sponge — one word at the empty log,
two at every prepend (`receiptRoot hash L = hash (receiptPre hash L)` by `rfl` on either
constructor). The length difference is what makes an empty/non-empty equivocation a genuine
collision rather than a length coincidence. -/
def receiptPre (hash : List ℤ → ℤ) : List Turn → List ℤ
  | [] => [0]
  | t :: ts => [receiptRoot hash ts, turnDigest hash t]

/-- **⚑ THE RECEIPT-ROOT EXTRACTOR.** Two logs folding to the same root break in exactly one of
three places, and the walk visits them in the order the fold does: the OUTER absorption (differing
preimages — this also catches every length mismatch), then the DEEPER root (recursively), then this
step's TURN DIGEST. Total and decidable, so it is a computation and never `Classical.choose` of an
existential; it bottoms out at a trivially non-colliding pair when nothing differs. -/
def receiptRootFind (hash : List ℤ → ℤ) : List Turn → List Turn → List ℤ × List ℤ
  | [], [] => ([], [])
  | [], y :: ys => (receiptPre hash [], receiptPre hash (y :: ys))
  | x :: xs, [] => (receiptPre hash (x :: xs), receiptPre hash [])
  | x :: xs, y :: ys =>
      if receiptPre hash (x :: xs) ≠ receiptPre hash (y :: ys) then
        (receiptPre hash (x :: xs), receiptPre hash (y :: ys))
      else if (receiptRootFind hash xs ys).1 ≠ (receiptRootFind hash xs ys).2 then
        receiptRootFind hash xs ys
      else turnDigestFind x y

/-- **THE EXTRACTOR BOTTOMS OUT AT AN EQUAL PAIR** on one and the same log — the honest committer,
who publishes ONE receipt index, pays no cryptographic assumption at all. -/
theorem receiptRootFind_self (hash : List ℤ → ℤ) :
    ∀ L : List Turn, (receiptRootFind hash L L).1 = (receiptRootFind hash L L).2
  | [] => rfl
  | _ :: xs => by
      rw [receiptRootFind, if_neg (by simp),
        if_neg (not_not.mpr (receiptRootFind_self hash xs))]
      rfl

/-- **⚑ THE RECEIPT-ROOT EXTRACTOR IS CORRECT — UNCONDITIONAL, NO FLOOR.** Two logs folding to the
SAME receipt-index root are EITHER the same log, OR the pair `receiptRootFind` returns is a GENUINE
collision of the deployed sponge. Nothing is assumed about `hash`, so this holds at deployed
parameters — where the old `Function.Injective (receiptRoot hash)` was refuted on BOTH sides at once
(`List Turn` is infinite, one BabyBear felt is not, so the premise `Poseidon2SpongeCR hash` AND the
conclusion `Function.Injective (receiptRoot hash)` are each false by the same pigeonhole). -/
theorem receiptRoot_binds_or_collides (hash : List ℤ → ℤ) :
    ∀ xs ys : List Turn, receiptRoot hash xs = receiptRoot hash ys →
      xs = ys ∨ SpongeColl hash (receiptRootFind hash xs ys) := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      cases ys with
      | nil => exact Or.inl rfl
      | cons y ys =>
          refine Or.inr ⟨?_, h⟩
          rw [receiptRootFind]
          simp [receiptPre]
  | cons x xs ih =>
      intro ys h
      cases ys with
      | nil =>
          refine Or.inr ⟨?_, h⟩
          rw [receiptRootFind]
          simp [receiptPre]
      | cons y ys =>
          by_cases hpre : receiptPre hash (x :: xs) ≠ receiptPre hash (y :: ys)
          · rw [receiptRootFind, if_pos hpre]
            exact Or.inr ⟨hpre, h⟩
          · have hpre' := not_not.mp hpre
            simp only [receiptPre, List.cons.injEq, and_true] at hpre'
            obtain ⟨hroot, hdigest⟩ := hpre'
            by_cases hdeep :
                (receiptRootFind hash xs ys).1 ≠ (receiptRootFind hash xs ys).2
            · rw [receiptRootFind, if_neg hpre, if_pos hdeep]
              rcases ih ys hroot with rfl | hc
              · exact absurd (receiptRootFind_self hash xs) hdeep
              · exact Or.inr hc
            · rw [receiptRootFind, if_neg hpre, if_neg hdeep]
              rcases turnDigest_binds_or_collides hash x y hdigest with rfl | hc
              · rcases ih ys hroot with rfl | hc2
                · exact Or.inl rfl
                · exact absurd (not_not.mp hdeep) hc2.1
              · exact Or.inr hc

/-- **`receiptRoot_binds`, PORTED OFF `Poseidon2SpongeCR` (2026-08-01).** The old form asserted
`Function.Injective (receiptRoot hash)` under `Poseidon2SpongeCR hash` — a refuted premise carried to
a refuted conclusion, which says nothing in either direction. It now carries the DECIDABLE
per-instance residual at the ONE pair `receiptRootFind` names for THESE two logs. Dischargeable by
the honest committer (`receiptRootFind_self`), refutable (`receiptRootColl_refutable`), and it
REFUTES the old premise (`receiptRootColl_refutes_poseidon2CR`) — strictly STRONGER, conclusion
unchanged on the pair.

⚑ HONEST PRICE: the receipt root is ONE BabyBear felt, so this residual is worth ≈2^15.5 queries.
That is a BREAK, not a security level. The port does not make the 1-felt receipt root safe; it makes
the price VISIBLE where a refuted floor had assumed it away. -/
theorem receiptRoot_binds (hash : List ℤ → ℤ) {xs ys : List Turn}
    (hno : ¬ SpongeColl hash (receiptRootFind hash xs ys))
    (h : receiptRoot hash xs = receiptRoot hash ys) : xs = ys :=
  (receiptRoot_binds_or_collides hash xs ys h).resolve_right hno

/-- **REFUTABLE.** At the constant sponge the extractor really does hand back a colliding pair, so
`¬ SpongeColl … (receiptRootFind …)` is not free — the residual is not `True` in disguise, and the
disjunction above is not a free pass. -/
theorem receiptRootColl_refutable (t : Turn) :
    SpongeColl (fun _ => (0 : ℤ)) (receiptRootFind (fun _ => (0 : ℤ)) [] [t]) := by
  refine ⟨?_, rfl⟩
  rw [receiptRootFind]
  simp [receiptPre]

/-- **A REFUTATION, NOT A NEW FLOOR.** Exhibiting the residual REFUTES `Poseidon2SpongeCR` outright,
so the port is a strict WEAKENING of the premise it replaces. Stated contrapositively, so it assumes
no floor content and the ratchet reads it as the tooth it is. -/
theorem receiptRootColl_refutes_poseidon2CR {hash : List ℤ → ℤ} {xs ys : List Turn}
    (hc : SpongeColl hash (receiptRootFind hash xs ys)) : ¬ Poseidon2SpongeCR hash :=
  fun hCR => hc.1 (hCR _ _ hc.2)

/-- Exactly eight felts, with width carried by the type rather than a side premise. -/
structure Felt8 where
  vals : List ℤ
  width : vals.length = 8

@[ext] theorem Felt8.ext {a b : Felt8} (h : a.vals = b.vals) : a = b := by
  cases a
  cases b
  simp_all

/-- `wireCommitR8` always returns the deployed eight-lane width. -/
theorem wireCommitR8_length (permW : List ℤ → List ℤ) (hW : Poseidon2Width8 permW)
    (limbs : List ℤ) (iroot : ℤ) : (wireCommitR8 permW limbs iroot).length = 8 := by
  unfold wireCommitR8
  rw [chainFrom8_snoc]
  exact hW _

/-- The faithful eight-lane commitment of one chained kernel state. -/
def commit8 (permW : List ℤ → List ℤ) (hW : Poseidon2Width8 permW)
    (hash : List ℤ → ℤ) (S : CommitSurface) (s : RecChainedState)
    (t : BoundaryTurn) : Felt8 :=
  ⟨wireCommitR8 permW (kernelPayload S s.kernel t) (receiptRoot hash s.log),
    wireCommitR8_length permW hW _ _⟩

/-- Published endpoint surface for the shielded-ring batch. -/
structure PublishedCommit8 where
  pubPre : Felt8
  pubPost : Felt8
  turn : BoundaryTurn
  creators : Fin 2 → CellId
  turnCount : Nat
  preReceiptRoot : ℤ
  postReceiptRoot : ℤ

/-- Faithful decode of the eight-lane endpoint, including its receipt-chain roots. -/
structure StateDecode8 (permW : List ℤ → List ℤ) (hW : Poseidon2Width8 permW)
    (hash : List ℤ → ℤ) (S : CommitSurface) (pc : PublishedCommit8)
    (pre post : RecChainedState) : Prop where
  preBinds : pc.pubPre = commit8 permW hW hash S pre pc.turn
  postBinds : pc.pubPost = commit8 permW hW hash S post pc.turn
  preReceiptBinds : pc.preReceiptRoot = receiptRoot hash pre.log
  postReceiptBinds : pc.postReceiptRoot = receiptRoot hash post.log
  preWF : Dregg2.Circuit.StateCommit.AccountsWF pre.kernel
  postWF : Dregg2.Circuit.StateCommit.AccountsWF post.kernel

/-- **EXACT-PROP BACKBONE (NOT the headline binding — see §R).** Equal faithful pre endpoints
determine the entire chained pre-state — OR exhibit a genuine collision of the deployed wide
permutation.  The headline anchor binding is the REDUCTION `stateCommit_binds_advantage_bound` (§R);
this deterministic disjunction is retained as the win relation's exact-Prop skeleton and to name the
two SEPARATELY-priced residuals of the `pre = pre'` branch.

⚑ **NO WIDE CR FLOOR IS CARRIED.** The old form took `hWideCR : Poseidon2WideCR permW` — DELETED,
because the deployed `single_perm_compress` REFUTES it, so the theorem was VACUOUSLY TRUE at deployed
parameters.  The `WireColl` disjunct is now priced by §R's reduction (negligible under the wide
collision floor `HashCRHardQuant (wideFamily D) Eff`).  The `pre = pre'` branch is closed by TWO named
residuals: the kernel commit and the RECEIPT-ROOT one.

⚑ **THE RECEIPT-ROOT RESIDUAL IS NOW A FOURTH DISJUNCT TOO (2026-08-01).**  It used to be
`hReceiptCR : Poseidon2SpongeCR hash` — the 1-felt receipt-root sponge's injectivity, which
`Circuit.HashFloorHonesty.poseidon2SpongeCR_false_babyBear` PROVES FALSE at deployed parameters, so
this theorem was vacuous on that leg exactly as it had been on the wide-CR and kernel-commit legs.
It is now `SpongeColl hash (receiptRootFind hash pre.log pre'.log)`: the deployed receipt sponge
collided at the SPECIFIC pair a TOTAL extractor hands back for THESE two logs — the same kind of
object as `WireColl` and `S.CommitColl` beside it, priced rather than assumed away.  The theorem now
carries NO floor at all.  ⚑ HONEST PRICE: one BabyBear felt, so ≈2^15.5 queries — a BREAK, not a
security level; the port makes that visible where the floor had hidden it.

⚑ **THE KERNEL-COMMIT RESIDUAL IS A THIRD DISJUNCT, AND IT NAMES A PAIR (2026-08-01, corrected the
same day).**  This used to read "`CommitSurface.commit_binds` (the kernel commit, UNCONDITIONAL)", and
that word was the wound: `commit_binds` consumed the four `CommitSurface` injectivity FIELDS, each
FALSE at deployed BabyBear width by pigeonhole, so the "unconditional" leg was VACUOUS and this
theorem inherited it.  The first repair made the third disjunct `S.StateBreak` — but that is a GLOBAL
collision existential over the frame sponge, which pigeonhole SUPPLIES at every BabyBear-bounded
sponge, so the whole disjunction became `True` and the theorem was vacuous a second time.  The third
disjunct is now `S.CommitColl pre.kernel pre'.kernel pc.turn`: the kernel-surface primitives collide
at the SPECIFIC argument pairs the binding visits — the same kind of object as `WireColl` beside it,
priced rather than free.  The shape is: the endpoints agree, OR the deployed wide permutation
equivocated at a named pair, OR the kernel surface collided at a named pair. -/
theorem stateDecode8_pre_faithful (permW : List ℤ → List ℤ)
    (hW : Poseidon2Width8 permW)
    (hash : List ℤ → ℤ)
    (S : CommitSurface) (pc : PublishedCommit8)
    {pre post pre' post' : RecChainedState}
    (hfin : Dregg2.Circuit.RestFrameFin.FiniteRepresentable pre.kernel)
    (hfin' : Dregg2.Circuit.RestFrameFin.FiniteRepresentable pre'.kernel)
    (h : StateDecode8 permW hW hash S pc pre post)
    (h' : StateDecode8 permW hW hash S pc pre' post') :
    pre = pre' ∨ WireColl permW (kernelPayload S pre.kernel pc.turn)
      (receiptRoot hash pre.log) (kernelPayload S pre'.kernel pc.turn)
      (receiptRoot hash pre'.log) ∨ S.CommitColl pre.kernel pre'.kernel pc.turn
      ∨ SpongeColl hash (receiptRootFind hash pre.log pre'.log) := by
  have hwide :
      wireCommitR8 permW (kernelPayload S pre.kernel pc.turn) (receiptRoot hash pre.log) =
        wireCommitR8 permW (kernelPayload S pre'.kernel pc.turn) (receiptRoot hash pre'.log) := by
    have := congrArg Felt8.vals (h.preBinds.symm.trans h'.preBinds)
    simpa [commit8] using this
  rcases wireCommitR8_binds_or_collides permW hW
    (by rw [kernelPayload_length, kernelPayload_length]) hwide with ⟨hpayload, hroot⟩ | hcoll
  swap
  · exact Or.inr (Or.inl hcoll)
  have hkcommit : S.commit pre.kernel pc.turn = S.commit pre'.kernel pc.turn := by
    simpa [kernelPayload] using congrArg List.head? hpayload
  rcases S.commit_binds_or_collides pre.kernel pre'.kernel pc.turn h.preWF h'.preWF hfin hfin'
    hkcommit with hk | hbrk
  swap
  · exact Or.inr (Or.inr (Or.inl hbrk))
  rcases receiptRoot_binds_or_collides hash pre.log pre'.log hroot with hlog | hrc
  swap
  · exact Or.inr (Or.inr (Or.inr hrc))
  refine Or.inl ?_
  cases pre
  cases pre'
  simp_all

/-- **EXACT-PROP BACKBONE (NOT the headline binding — see §R).** Equal faithful post endpoints
determine the entire chained post-state — OR exhibit a genuine collision of the deployed wide
permutation.  The `post` twin of `stateDecode8_pre_faithful`; the headline anchor binding is the
REDUCTION `stateCommit_binds_advantage_bound` (§R).

⚑ **NO WIDE CR FLOOR IS CARRIED.** The old form took `hWideCR : Poseidon2WideCR permW` — DELETED,
because the deployed `single_perm_compress` REFUTES it, so the theorem was VACUOUSLY TRUE at deployed
parameters.  The `WireColl` disjunct is priced by §R's reduction; the `post = post'` branch is closed
by the kernel commit and the receipt-root residual.  The kernel commit's residual is the THIRD
disjunct `S.CommitColl` — see the `pre` twin for why `CommitSurface.commit_binds` could not stay
"unconditional", and why the intermediate `S.StateBreak` disjunct was no better — and (⚑ 2026-08-01)
the receipt root's is the FOURTH, `SpongeColl hash (receiptRootFind hash post.log post'.log)`,
replacing the refuted `hReceiptCR : Poseidon2SpongeCR hash` binder. -/
theorem stateDecode8_post_faithful (permW : List ℤ → List ℤ)
    (hW : Poseidon2Width8 permW)
    (hash : List ℤ → ℤ)
    (S : CommitSurface) (pc : PublishedCommit8)
    {pre post pre' post' : RecChainedState}
    (hfin : Dregg2.Circuit.RestFrameFin.FiniteRepresentable post.kernel)
    (hfin' : Dregg2.Circuit.RestFrameFin.FiniteRepresentable post'.kernel)
    (h : StateDecode8 permW hW hash S pc pre post)
    (h' : StateDecode8 permW hW hash S pc pre' post') :
    post = post' ∨ WireColl permW (kernelPayload S post.kernel pc.turn)
      (receiptRoot hash post.log) (kernelPayload S post'.kernel pc.turn)
      (receiptRoot hash post'.log) ∨ S.CommitColl post.kernel post'.kernel pc.turn
      ∨ SpongeColl hash (receiptRootFind hash post.log post'.log) := by
  have hwide :
      wireCommitR8 permW (kernelPayload S post.kernel pc.turn) (receiptRoot hash post.log) =
        wireCommitR8 permW (kernelPayload S post'.kernel pc.turn) (receiptRoot hash post'.log) := by
    have := congrArg Felt8.vals (h.postBinds.symm.trans h'.postBinds)
    simpa [commit8] using this
  rcases wireCommitR8_binds_or_collides permW hW
    (by rw [kernelPayload_length, kernelPayload_length]) hwide with ⟨hpayload, hroot⟩ | hcoll
  swap
  · exact Or.inr (Or.inl hcoll)
  have hkcommit : S.commit post.kernel pc.turn = S.commit post'.kernel pc.turn := by
    simpa [kernelPayload] using congrArg List.head? hpayload
  rcases S.commit_binds_or_collides post.kernel post'.kernel pc.turn h.postWF h'.postWF hfin hfin'
    hkcommit with hk | hbrk
  swap
  · exact Or.inr (Or.inr (Or.inl hbrk))
  rcases receiptRoot_binds_or_collides hash post.log post'.log hroot with hlog | hrc
  swap
  · exact Or.inr (Or.inr (Or.inr hrc))
  refine Or.inl ?_
  cases post
  cases post'
  simp_all

/-- A one-lane endpoint forgery cannot equal an honest eight-lane publication. -/
theorem Felt8.set_ne (x : Felt8) (i : Fin 8) (v : ℤ)
    (hne : some v ≠ x.vals[i.val]?) :
    x.vals.set i v ≠ x.vals := by
  have hi : i.val < x.vals.length := by simpa [x.width] using i.isLt
  intro h
  have this := congrArg (fun ys => ys[i.val]?) h
  simp [List.getElem?_set, hi] at this
  apply hne
  simpa [hi] using congrArg some this

/-! ## §R — the state-commit anchor binding, as a SECURITY REDUCTION.

⚑ **THE HEADLINE.** This section replaces the bare `_binds_or_collides` disjunction as the deployed
binding of the wide `STATE_COMMIT` carrier (`turn/src/state_commit.rs`).  The disjunction quantified
over SOLUTIONS ("a collision exists"); this reduction quantifies over EFFICIENT ADVERSARIES ("every
`Eff`-adversary that forges the state commit finds a `permW` collision, negligible under the floor").
The extractors (`wireCommit8Find` → `wireBreakToFinder`) are the reduction's WITNESS, not the export.

The wide layer reuses the `InjectiveFloorRegrounded` §3 machinery whole: `wideFamily` (the deployed
`single_perm_compress` as a keyed collision family), `wireCommitBreakGame` (the wire-commit
equivocation game), `wire_adv_le` (its advantage ≤ the extracted collision-finder's), and
`wireCommitR8_binds_advantage_bound` (the reduction to `HashCRHardQuant (wideFamily D) Eff`).  What
§R ADDS is the STATE ENDPOINT: the game whose answers are chained states decoding to a published
commit, and the map of adversaries lifting it onto the wire game. -/

/-- **THE STATE-COMMIT FORGERY GAME.** The adversary is handed a sampled domain-separation tag and
WINS iff it outputs two chained states whose wide-chain inputs `(kernelPayload, receiptRoot)` DIFFER
yet publish the SAME eight-felt wide commitment — i.e. it breaks the anchor's binding on the deployed
`wireCommitR8`.  The break is IN the win relation; the wide-input inequality is the honest side
condition that makes this a WIDE forgery (a state equivocation whose wide inputs AGREE is a receipt- or
kernel-commit collision, priced elsewhere). -/
def stateCommitBreakGame (D : WideKeyed) (S : CommitSurface) (hash : List ℤ → ℤ)
    (t : BoundaryTurn) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => RecChainedState × RecChainedState
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ tag c =>
    ((kernelPayload S c.1.kernel t, receiptRoot hash c.1.log)
        ≠ (kernelPayload S c.2.kernel t, receiptRoot hash c.2.log)) ∧
      wireCommitR8 (D.permWAt tag) (kernelPayload S c.1.kernel t) (receiptRoot hash c.1.log)
        = wireCommitR8 (D.permWAt tag) (kernelPayload S c.2.kernel t) (receiptRoot hash c.2.log)
  winsDec := fun _ tag c => inferInstance

/-- **THE PROBLEM IS IN THE STATEMENT** — the win relation is a genuine equivocation of the deployed
wide state anchor. -/
theorem stateCommitBreakGame_wins_iff (D : WideKeyed) (S : CommitSurface) (hash : List ℤ → ℤ)
    (t : BoundaryTurn) (l : ℕ) (tag : D.Tag) (c : RecChainedState × RecChainedState) :
    (stateCommitBreakGame D S hash t).wins l tag c ↔
      (((kernelPayload S c.1.kernel t, receiptRoot hash c.1.log)
          ≠ (kernelPayload S c.2.kernel t, receiptRoot hash c.2.log)) ∧
        wireCommitR8 (D.permWAt tag) (kernelPayload S c.1.kernel t) (receiptRoot hash c.1.log)
          = wireCommitR8 (D.permWAt tag) (kernelPayload S c.2.kernel t) (receiptRoot hash c.2.log)) :=
  Iff.rfl

/-- **⚑ THE FORGERY IS THE DEPLOYED DECODE OBJECT.** Two faithful `StateDecode8` witnesses of the SAME
published commit at the deployed tag, whose wide-chain inputs differ, ARE a `stateCommitBreakGame`
win.  This ties the abstract game to the very endpoint `turn/src/state_commit.rs` anchors — the game is
not a free-floating construction. -/
theorem stateDecode8_forgery_is_break (D : WideKeyed) (S : CommitSurface) (hash : List ℤ → ℤ)
    (pc : PublishedCommit8) {pre post pre' post' : RecChainedState}
    (h : StateDecode8 (D.permWAt D.deployedTag) (D.width8At D.deployedTag) hash S pc pre post)
    (h' : StateDecode8 (D.permWAt D.deployedTag) (D.width8At D.deployedTag) hash S pc pre' post')
    (hne : (kernelPayload S pre.kernel pc.turn, receiptRoot hash pre.log)
        ≠ (kernelPayload S pre'.kernel pc.turn, receiptRoot hash pre'.log)) :
    (stateCommitBreakGame D S hash pc.turn).wins 0 D.deployedTag (pre, pre') := by
  refine ⟨hne, ?_⟩
  have := congrArg Felt8.vals (h.preBinds.symm.trans h'.preBinds)
  simpa [commit8] using this

/-- **THE EXTRACTOR, AS A MAP OF ADVERSARIES.** A state-commit forger becomes a wire-commit
equivocator by reading off the two states' wide-chain inputs.  Composed with
`InjectiveFloorRegrounded.wireBreakToFinder` (the chain-walk `wireCommit8Find`), this is the full
reduction from a state forgery to a genuine `permW` collision. -/
def stateBreakToWireBreak (D : WideKeyed) (S : CommitSurface) (hash : List ℤ → ℤ)
    (t : BoundaryTurn) (A : Adversary (stateCommitBreakGame D S hash t)) :
    Adversary (wireCommitBreakGame D) where
  run := fun l tag =>
    let c := A.run l tag
    ((kernelPayload S c.1.kernel t, receiptRoot hash c.1.log),
     (kernelPayload S c.2.kernel t, receiptRoot hash c.2.log))

/-- **⚑ WIN-PRESERVATION — the reduction, at the game level.** Every tag the state forger wins, the
extracted wire-commit equivocator wins: the wide inputs are distinct (the forgery's side condition),
of EQUAL length (both `kernelPayload`s are `kernelPayloadWidth` limbs), with EQUAL `wireCommitR8` (the equal published
commit).  That is exactly `wireCommitBreakGame`'s win. -/
theorem state_wins_imp (D : WideKeyed) (S : CommitSurface) (hash : List ℤ → ℤ)
    (t : BoundaryTurn) (A : Adversary (stateCommitBreakGame D S hash t)) (l : ℕ) (tag : D.Tag)
    (hwin : (stateCommitBreakGame D S hash t).wins l tag (A.run l tag)) :
    (wireCommitBreakGame D).wins l tag ((stateBreakToWireBreak D S hash t A).run l tag) := by
  refine ⟨?_, hwin.1, hwin.2⟩
  show (kernelPayload S (A.run l tag).1.kernel t).length
      = (kernelPayload S (A.run l tag).2.kernel t).length
  rw [kernelPayload_length, kernelPayload_length]

/-- **THE ADVANTAGE INEQUALITY.** The state forger's advantage is at most the extracted wire-commit
equivocator's, at every parameter — over the SAME sampled tag space. -/
theorem state_adv_le (D : WideKeyed) (S : CommitSurface) (hash : List ℤ → ℤ)
    (t : BoundaryTurn) (A : Adversary (stateCommitBreakGame D S hash t)) (l : ℕ) :
    gameAdv (stateCommitBreakGame D S hash t) A l
      ≤ gameAdv (wireCommitBreakGame D) (stateBreakToWireBreak D S hash t A) l := by
  refine @winProb_le_of_imp _ (D.tagFintype) _ _ (fun tag ht => ?_)
  replace ht := (Adversary.hit_eq_true _ _ _).mp ht
  refine (Adversary.hit_eq_true _ _ _).mpr ?_
  exact state_wins_imp D S hash t A l tag ht

/-- **⚑ THE REDUCED ANCHOR BINDING — from the wide permutation's collision floor, VIA the reduction.**

Under the DEPLOYED `single_perm_compress`'s collision floor at the class `Eff`, a state-commit forger
whose extracted (state → wire → collision) finder is in that class has NEGLIGIBLE advantage: the
faithful eight-felt state anchor binds the whole wide-chain input (payload + receipt root) except with
negligible probability.  This is the REDUCTION that replaces the bare `_binds_or_collides` disjunction
as the headline binding of the deployed `STATE_COMMIT` carrier.

The advantage inequality is `state_adv_le` (state forger → wire equivocator); the wire → collision
composition and the floor closure both live INSIDE `wireCommitR8_binds_advantage_bound` (which itself
composes `InjectiveFloorRegrounded.wire_adv_le`), so this domination step is the single new layer.

⚑ `hEff` is UNDISCHARGED — the standard "the reduction is efficient", a PARAMETER, in the open, on the
COMPOSED finder `wireBreakToFinder D (stateBreakToWireBreak … A)`.  It CANNOT be honestly discharged
over THIS game: §P proves the floor at `Eff := IsPolyTime` FALSE at deployed BabyBear parameters, and
no query-counted class repairs a FIXED-function game either (the function is public — a bounded
adversary brute-forces it; `RomBindingReduction` header).  The honest discharge moves the GAME to the
sampled-oracle model — §Q/§S.  The floor here is priced by §R's two poles below: `⊤` FALSE at deployed
BabyBear params, `⊥` vacuous. -/
theorem stateCommit_binds_advantage_bound (D : WideKeyed) (S : CommitSurface) (hash : List ℤ → ℤ)
    (t : BoundaryTurn)
    (Eff : Adversary (hashGame (wideFamily D)) → Prop)
    (A : Adversary (stateCommitBreakGame D S hash t))
    (hEff : Eff (wireBreakToFinder D (stateBreakToWireBreak D S hash t A)))
    (hCR : HashCRHardQuant (wideFamily D) Eff) :
    Negl (gameAdv (stateCommitBreakGame D S hash t) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (stateCommitBreakGame D S hash t) A l).1)
    (state_adv_le D S hash t A)
    (wireCommitR8_binds_advantage_bound D Eff (stateBreakToWireBreak D S hash t A) hEff hCR)

/-- **⚑ THE ⊤ POLE — the floor is FALSE at the REAL BabyBear parameters** (the honest price of `hEff`).
Re-exported from `InjectiveFloorRegrounded.wide_floor_top_false_babyBear`: an eight-lane squeeze into
bounded lanes has finite range while `List ℤ` is infinite, so a collision exists at every tag and the
floor at `Eff := ⊤` is FALSE.  What the reduction buys is not a floor the deployed permutation
satisfies at ⊤ — no such floor exists — it is that the residual is ONE named parameter with both poles
proved, in place of an unclosed disjunction whose right branch is unconditionally available. -/
theorem stateCommit_floor_top_false_babyBear (D : WideKeyed)
    (hb : ∀ (tag : D.Tag) (xs : List ℤ), ∀ x ∈ D.permWAt tag xs, 0 ≤ x ∧ x < Dregg2.Circuit.VacuitySweepTeeth.babyBearP) :
    ¬ HashCRHardQuant (wideFamily D) (fun _ => True) :=
  wide_floor_top_false_babyBear D hb

/-- **THE ⊥ POLE — vacuous.** Recorded so the floor's satisfiability cannot be mistaken for evidence. -/
theorem stateCommit_floor_bot_vacuous (D : WideKeyed) :
    HashCRHardQuant (wideFamily D) (fun _ => False) :=
  wide_floor_bot_vacuous D

/-- **(CANARY — the keystone does NOT follow from the floor applied at ANOTHER finder.)** Strip the
reduction: try to conclude the state forger's negligibility from the wide collision floor applied at
some OTHER finder `B`, not the one EXTRACTED from the forger.  It does not go through — only
`state_adv_le`/`wire_adv_le` connect the extracted finder to the state game.  A disjunction whose right
branch is always available would carry no more content than `True`; this tooth reds if a future edit
reconnects the games. -/
example (D : WideKeyed) (S : CommitSurface) (hash : List ℤ → ℤ) (t : BoundaryTurn)
    (Eff : Adversary (hashGame (wideFamily D)) → Prop)
    (A : Adversary (stateCommitBreakGame D S hash t))
    (B : Adversary (hashGame (wideFamily D))) (hB : Eff B)
    (hCR : HashCRHardQuant (wideFamily D) Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (stateCommitBreakGame D S hash t) A) := hCR B hB)
  trivial

/-- **THE POSITIVE POLE — the RIGHT floor DOES discharge it.** A gate that refuses everything is a
broken keystone, not a fixed one: with the wide collision floor at the EXTRACTED (composed) finder, the
anchor binding fires. -/
theorem the_reduced_stateCommit_bound_fires (D : WideKeyed) (S : CommitSurface) (hash : List ℤ → ℤ)
    (t : BoundaryTurn)
    (Eff : Adversary (hashGame (wideFamily D)) → Prop)
    (A : Adversary (stateCommitBreakGame D S hash t))
    (hEff : Eff (wireBreakToFinder D (stateBreakToWireBreak D S hash t A)))
    (hCR : HashCRHardQuant (wideFamily D) Eff) :
    Negl (gameAdv (stateCommitBreakGame D S hash t) A) :=
  stateCommit_binds_advantage_bound D S hash t Eff A hEff hCR

/-! ## §P — the `IsPolyTime` discharge is REFUTED, and the theorem that carried it is GONE.

⚑ **WHAT STOOD HERE.** `stateCommit_binds_from_polyTime` instantiated §R's `Eff` at
`Dregg2.Crypto.CostAdversary.IsPolyTime` and PROVED the composed finder stays in that class — the
efficiency bookkeeping was real, and its output-growth lemmas remain below.  But the floor it then
consumed,

    HashCRHardQuant (wideFamily D) (IsPolyTime (hashAnsSize D)),

is **FALSE at deployed BabyBear parameters**, and this section now PROVES that
(`stateCommit_floor_polyTime_false_babyBear`) by the same construction that felled the sponge floor
(`Exec.SystemRootsBindingReduction.sysRoots_floor_polyTime_false_babyBear`): `IsPolyTime` prices the
answer's SIZE, never the difficulty of finding it, so the `Classical.choice` adversary that answers
every sampled tag with a two-limb collision — which EXISTS, by pigeonhole, in the fixed compressing
wide permutation — is in the class and wins with probability `1`.  A binding conditioned on a refuted
floor asserts nothing at the deployed hash; it was VACUOUS, and it is DELETED rather than retained as
costume.  Its honest successor is §Q/§S: the same reduction shape over a game whose hash is a SAMPLED
ORACLE the adversary can only QUERY, where the floor is a theorem (`KeyedRomFloor.keyedRom_hard`) and
the choice-answerer is PROVABLY excluded.

The extractor output-size facts (`chunk31_len_le`, `chainCollFind_len_le`, `wireCommit8Find_len_le`)
are RETAINED: true deployed-width facts about the chain walk, independent of the cost model that used
to consume them. -/

/-- **THE COLLISION GAME'S ANSWER ENCODING** — the two claimed preimages of the wide permutation.
This is the size measure the REFUTED class `IsPolyTime (hashAnsSize D)` prices (§P header). -/
def hashAnsSize (D : WideKeyed) : AnsSize (hashGame (wideFamily D)) :=
  fun _ (p : List ℤ × List ℤ) => p.1.length + p.2.length

/-- Every `chunk31` block is at most three limbs wide (the deployed body arity is `carrier ‖ 3`). -/
theorem chunk31_len_le : ∀ (xs : List ℤ) (c : List ℤ), c ∈ chunk31 xs → c.length ≤ 3
  | a :: b :: d :: rest, c, hc => by
      simp only [chunk31, List.mem_cons] at hc
      rcases hc with h | h
      · subst h; simp
      · exact chunk31_len_le rest c h
  | [a, b], c, hc => by
      simp only [chunk31, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with h | h <;> subst h <;> simp
  | [a], c, hc => by
      simp only [chunk31, List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc; simp
  | [], c, hc => by simp [chunk31] at hc

/-- **THE CHAIN WALK RETURNS BOUNDED LISTS.** Every value `chainCollFind` can return is either a carrier
(width `8`, since `permW` squeezes eight felts) or a carrier concatenated with one body block (`≤ 3`), so
at most `11` felts. This is what makes the wire→collision reduction's OUTPUT SIZE a proved constant
instead of an assumption. -/
theorem chainCollFind_len_le (permW : List ℤ → List ℤ) (hW : Poseidon2Width8 permW) :
    ∀ (cs cs' : List (List ℤ)) (acc acc' : List ℤ),
      acc.length ≤ 8 → acc'.length ≤ 8 →
      (∀ c ∈ cs, c.length ≤ 3) → (∀ c ∈ cs', c.length ≤ 3) →
      (chainCollFind permW acc cs acc' cs').1.length ≤ 11
        ∧ (chainCollFind permW acc cs acc' cs').2.length ≤ 11 := by
  intro cs
  induction cs with
  | nil =>
      intro cs' acc acc' ha ha' _ _
      have hnil : chainCollFind permW acc [] acc' cs' = (acc, acc') := by cases cs' <;> rfl
      rw [hnil]
      refine ⟨?_, ?_⟩
      · show acc.length ≤ 11; omega
      · show acc'.length ≤ 11; omega
  | cons c ds ih =>
      intro cs' acc acc' ha ha' hcs hcs'
      cases cs' with
      | nil =>
          have hnil : chainCollFind permW acc (c :: ds) acc' [] = (acc, acc') := rfl
          rw [hnil]
          refine ⟨?_, ?_⟩
          · show acc.length ≤ 11; omega
          · show acc'.length ≤ 11; omega
      | cons c' ds' =>
          by_cases hif : permW (acc ++ c) = permW (acc' ++ c') ∧ (acc ++ c) ≠ (acc' ++ c')
          · rw [chainCollFind, if_pos hif]
            have h1 := hcs c (by simp)
            have h2 := hcs' c' (by simp)
            exact ⟨by simp only [List.length_append]; omega,
                   by simp only [List.length_append]; omega⟩
          · rw [chainCollFind, if_neg hif]
            exact ih ds' (permW (acc ++ c)) (permW (acc' ++ c'))
              (le_of_eq (hW _)) (le_of_eq (hW _))
              (fun x hx => hcs x (List.mem_cons_of_mem _ hx))
              (fun x hx => hcs' x (List.mem_cons_of_mem _ hx))

/-- **⚑ THE WIRE→COLLISION EXTRACTOR DOES NOT BLOW UP ITS INPUT** — it returns at most `11 + 11` felts,
a CONSTANT, whichever branch it takes. Proved, not assumed; this is the output-size obligation the cost
model's `pure`-leaf charge creates, discharged. -/
theorem wireCommit8Find_len_le (permW : List ℤ → List ℤ) (hW : Poseidon2Width8 permW)
    (l : List ℤ) (ir : ℤ) (l' : List ℤ) (ir' : ℤ) :
    (wireCommit8Find permW l ir l' ir').1.length
      + (wireCommit8Find permW l ir l' ir').2.length ≤ 22 := by
  have hchunks : ∀ (xs : List ℤ) (z : ℤ) (c : List ℤ),
      c ∈ chunk31 xs ++ [[z, 0, 0]] → c.length ≤ 3 := by
    intro xs z c hc
    rcases List.mem_append.mp hc with h | h
    · exact chunk31_len_le xs c h
    · simp only [List.mem_singleton] at h; subst h; simp
  by_cases hif : IsCollW permW (chainCollFind permW (permW (l.take 4))
      (chunk31 (l.drop 4) ++ [[ir, 0, 0]]) (permW (l'.take 4)) (chunk31 (l'.drop 4) ++ [[ir', 0, 0]]))
  · rw [wireCommit8Find, if_pos hif]
    have h := chainCollFind_len_le permW hW
      (chunk31 (l.drop 4) ++ [[ir, 0, 0]]) (chunk31 (l'.drop 4) ++ [[ir', 0, 0]])
      (permW (l.take 4)) (permW (l'.take 4))
      (le_of_eq (hW (l.take 4))) (le_of_eq (hW (l'.take 4)))
      (hchunks (l.drop 4) ir) (hchunks (l'.drop 4) ir')
    omega
  · rw [wireCommit8Find, if_neg hif]
    have h1 : (l.take 4).length ≤ 4 := List.length_take_le 4 l
    have h2 : (l'.take 4).length ≤ 4 := List.length_take_le 4 l'
    show (l.take 4).length + (l'.take 4).length ≤ 22
    omega

/-- **A SHORT COLLISION AT EVERY TAG.** The one-limb messages `[n]` are an infinite family whose
images under the deployed wide permutation all land in the finite box of 8-lane BabyBear squeezes —
so two of them collide, and the witness is TWO LIMBS TOTAL.  Pure pigeonhole; no Poseidon2 structure
used.  (`Exec.SystemRootsBindingReduction.exists_short_collision`, transplanted to the WIDE family —
the same disease, at the anchor THIS file exports.) -/
theorem exists_short_wide_collision (D : WideKeyed)
    (hb : ∀ (t : D.Tag) (xs : List ℤ), ∀ x ∈ D.permWAt t xs, 0 ≤ x ∧ x < babyBearP)
    (l : ℕ) (t : D.Tag) :
    ∃ p : List ℤ × List ℤ, (hashGame (wideFamily D)).wins l t p
      ∧ p.1.length + p.2.length ≤ 2 := by
  have hfin : (Set.range (fun n : ℤ => D.permWAt t [n])).Finite := by
    refine (finite_width8_bounded babyBearP).subset ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨D.width8At t [n], fun x hx => ⟨(hb t [n] x hx).1, (hb t [n] x hx).2⟩⟩
  have hni := not_injective_of_finite_range _ hfin
  rw [Function.not_injective_iff] at hni
  obtain ⟨n, m, himg, hne⟩ := hni
  refine ⟨([n], [m]), ⟨fun h => hne ?_, himg⟩, by simp⟩
  injection h

/-- **THE SHORT-COLLISION ADVERSARY** — answers every sampled tag with a two-limb collision of the
wide permutation.  Nothing in `Adversary` demands computability, and nothing in `IsPolyTime` prices
the FINDING — only the writing. -/
noncomputable def shortWideCollAdv (D : WideKeyed)
    (hb : ∀ (t : D.Tag) (xs : List ℤ), ∀ x ∈ D.permWAt t xs, 0 ≤ x ∧ x < babyBearP) :
    Adversary (hashGame (wideFamily D)) where
  run := fun l t => (exists_short_wide_collision D hb l t).choose

/-- It wins at EVERY tag. -/
theorem shortWideCollAdv_wins (D : WideKeyed)
    (hb : ∀ (t : D.Tag) (xs : List ℤ), ∀ x ∈ D.permWAt t xs, 0 ≤ x ∧ x < babyBearP)
    (l : ℕ) (t : D.Tag) :
    (hashGame (wideFamily D)).wins l t ((shortWideCollAdv D hb).run l t) :=
  (exists_short_wide_collision D hb l t).choose_spec.1

/-- And it is IN the class the deleted discharge instantiated the floor at — two limbs is poly-size. -/
theorem shortWideCollAdv_isPolyTime (D : WideKeyed)
    (hb : ∀ (t : D.Tag) (xs : List ℤ), ∀ x ∈ D.permWAt t xs, 0 ≤ x ∧ x < babyBearP) :
    IsPolyTime (hashAnsSize D) (shortWideCollAdv D hb) :=
  Dregg2.Crypto.CostAdversary.isPolyTime_inhabited _ _
    ⟨2, 0, fun l t => by
      have h := (exists_short_wide_collision D hb l t).choose_spec.2
      simpa [hashAnsSize, shortWideCollAdv] using h.trans (by omega)⟩

/-- **⚑ THE INSTANTIATED FLOOR IS FALSE AT THE DEPLOYED WIDE PERMUTATION** — the death certificate
of the deleted `stateCommit_binds_from_polyTime`: its `hCR` hypothesis is refutable at deployed
BabyBear parameters, so everything conditioned on it was VACUOUS there.  The defect is the shared
cost model (`IsPolyTime` cannot separate "writes a short string" from "finds a collision"), not this
site; the repair is §Q/§S, not a better `Eff` over the same fixed-function game. -/
theorem stateCommit_floor_polyTime_false_babyBear (D : WideKeyed)
    (hb : ∀ (t : D.Tag) (xs : List ℤ), ∀ x ∈ D.permWAt t xs, 0 ≤ x ∧ x < babyBearP) :
    ¬ HashCRHardQuant (wideFamily D) (IsPolyTime (hashAnsSize D)) := by
  intro hHard
  have hneg := hHard (shortWideCollAdv D hb) (shortWideCollAdv_isPolyTime D hb)
  have hone : gameAdv (hashGame (wideFamily D)) (shortWideCollAdv D hb) = fun _ => (1 : ℝ) := by
    funext l
    show @Dregg2.Crypto.ProbCrypto.winProb _ ((hashGame (wideFamily D)).instFin l) _ = 1
    have hall : (shortWideCollAdv D hb).hit l = fun _ => true := by
      funext t
      exact ((shortWideCollAdv D hb).hit_eq_true l t).mpr (shortWideCollAdv_wins D hb l t)
    rw [hall]
    exact @winProb_top _ ((hashGame (wideFamily D)).instFin l) ((hashGame (wideFamily D)).instNe l)
  rw [hone] at hneg
  exact not_negl_one hneg

/-- **(TOOTH — the refuted class is NOT EMPTY.)** The constant finder is in
`IsPolyTime (hashAnsSize D)` (the answer it writes has size `0` under the game's own encoding), so
§P's refutation is not about a vacuous class: the class is inhabited AND contains a probability-`1`
winner.  The floor fails WITH content. -/
theorem hashFloor_isPolyTime_inhabited (D : WideKeyed) :
    IsPolyTime (hashAnsSize D)
      (Dregg2.Crypto.CostAdversary.idAdv (O := Unit) (Q := fun _ => Unit) (R := fun _ => Unit)
        (fun _ _ => (([] : List ℤ), ([] : List ℤ)))).toAdversary :=
  Dregg2.Crypto.CostAdversary.isPolyTime_inhabited _ _
    ⟨0, 0, fun _ _ => by simp [hashAnsSize]⟩

/-! ## §Q — the deployed chain, AS AN ORACLE COMPUTATION.

⚑ **THE MODEL THE RE-GROUNDING NEEDS, ON THE REAL OBJECT.** `wireCommitR8` is a CHAINED absorption:
the 4-limb head, the body's 3-limb `chunk31` chunks each re-absorbing the previous 8-felt digest,
the receipt root last.  `wireCommitComp` is that chain as an ORACLE PROGRAM — one `query` node per
absorption step, the previous ANSWER threaded into the next query point — and `wireCommitComp_eval`
proves its run at the deployed permutation IS `wireCommitR8`, step for step.  NOTHING in this
section is idealized: the oracle type is the deployed `List ℤ → List ℤ`, and the budget
(`wireCommitComp_queryBounded`: exactly `deployedBlockCount + 1` queries at the proved payload width) is a fact
of the deployed schedule. -/

/-- The deployed fold IS the generic chain: `chainFrom8` is `chainEval` at the fixed-width
concatenation encoding `enc acc c = acc ++ c`. -/
theorem chainEval_append_eq_chainFrom8 (permW : List ℤ → List ℤ) :
    ∀ (cs : List (List ℤ)) (acc : List ℤ),
      chainEval permW (fun acc c => acc ++ c) acc cs = chainFrom8 permW acc cs
  | [], _ => rfl
  | c :: cs, acc => chainEval_append_eq_chainFrom8 permW cs (permW (acc ++ c))

/-- **⚑ THE DEPLOYED CHAINED COMMITMENT, AS AN ORACLE PROGRAM** — the head query, then one query per
`chunk31` block, then the iroot block: `wireCommitR8`'s exact absorption schedule, with each
absorption a `query` node.  This is the object the re-pointing campaign named as the missing piece
for the chained STATE_COMMIT. -/
def wireCommitComp (l : List ℤ) (ir : ℤ) : OracleComp (List ℤ) (List ℤ) (List ℤ) :=
  .query (l.take 4)
    (fun h => chainComp (fun acc c => acc ++ c) h (chunk31 (l.drop 4) ++ [[ir, 0, 0]]))

/-- **THE MODEL IS THE DEPLOYED OBJECT**: running the program at the deployed permutation is
`wireCommitR8`, on the nose. -/
theorem wireCommitComp_eval (permW : List ℤ → List ℤ) (l : List ℤ) (ir : ℤ) :
    (wireCommitComp l ir).eval permW = wireCommitR8 permW l ir := by
  show (chainComp (fun acc c => acc ++ c) (permW (l.take 4))
      (chunk31 (l.drop 4) ++ [[ir, 0, 0]])).eval permW = _
  rw [chainComp_eval, chainEval_append_eq_chainFrom8]
  rfl

/-- Every chunk of a body whose length is divisible by 3 is EXACTLY 3 limbs wide — the deployed
body (`kernelPayloadWidth` minus the 4-limb head) feeds only 3-wide blocks, which is what pins the chained
carrier's block type in §S. -/
theorem chunk31_three_wide :
    ∀ (xs : List ℤ), xs.length % 3 = 0 → ∀ c ∈ chunk31 xs, c.length = 3
  | [], _, c, hc => by simp [chunk31] at hc
  | [a], h, c, hc => by simp at h
  | [a, b], h, c, hc => by simp at h
  | a :: b :: d :: rest, h, c, hc => by
      simp only [chunk31, List.mem_cons] at hc
      rcases hc with rfl | hc
      · rfl
      · refine chunk31_three_wide rest ?_ c hc
        simp only [List.length_cons] at h
        omega

/-- The absorption BLOCKS the deployed chain feeds after the 4-limb head: one per `chunk31` chunk of
the body, plus the receipt-root block.  DERIVED from `kernelPayloadWidth`, so a rotation flag day
moves the schedule here instead of leaving this section modelling a payload nothing emits. -/
def deployedBlockCount : Nat := chunkCount (kernelPayloadWidth - 4) + 1

/-- The extractor re-walks BOTH chains and pays two queries besides — `romChained_binds`'s budget,
as a function of the schedule rather than a transcribed total. -/
def deployedExtractorBudget : Nat := 2 * deployedBlockCount + 2

/-- The schedule's two derived totals, evaluated once.  These are the ONLY place a number appears,
and they are consequences of `kernelPayloadWidth`, not inputs to it. -/
theorem deployedBlockCount_eq : deployedBlockCount = 62 := by decide

theorem deployedExtractorBudget_eq : deployedExtractorBudget = 126 := by decide

/-- The deployed block count: the payload's body feeds `chunk31` chunks, then the iroot block. -/
theorem deployed_blockCount (l : List ℤ) (ir : ℤ) (hlen : l.length = kernelPayloadWidth) :
    (chunk31 (l.drop 4) ++ [[ir, 0, 0]]).length = deployedBlockCount := by
  rw [List.length_append, chunk31_length, List.length_drop, hlen]
  rfl

/-- **THE DEPLOYED COMMITTER PAYS ONE QUERY PER BLOCK PLUS THE HEAD'S**, at the proved payload
width.  The budget is a fact of the schedule, not a declaration — and not a literal, which is what
let it go on describing a 184-limb payload after the extent moved. -/
theorem wireCommitComp_queryBounded (l : List ℤ) (ir : ℤ) (hlen : l.length = kernelPayloadWidth) :
    QueryBounded (deployedBlockCount + 1) (wireCommitComp l ir) := by
  unfold wireCommitComp
  refine QueryBounded.query deployedBlockCount _ _ (fun h => ?_)
  have hq := chainComp_queryBounded (fun acc c => acc ++ c)
    (chunk31 (l.drop 4) ++ [[ir, 0, 0]]) h
  rwa [deployed_blockCount l ir hlen] at hq

/-- **THE DEPLOYED STATE COMMIT IS THE PROGRAM'S RUN**: `commit8`'s eight felts are
`wireCommitComp`'s output at the deployed permutation, at the deployed payload and receipt root. -/
theorem commit8_as_oracleComp (permW : List ℤ → List ℤ) (hW : Poseidon2Width8 permW)
    (hash : List ℤ → ℤ) (S : CommitSurface) (s : RecChainedState) (t : BoundaryTurn) :
    (wireCommitComp (kernelPayload S s.kernel t) (receiptRoot hash s.log)).eval permW
      = (commit8 permW hW hash S s t).vals := by
  rw [wireCommitComp_eval]
  rfl

/-- The deployed committer program is `deployedBlockCount + 1`-query-bounded at the real payload. -/
theorem commit8_queryBounded (hash : List ℤ → ℤ) (S : CommitSurface) (s : RecChainedState)
    (t : BoundaryTurn) :
    QueryBounded (deployedBlockCount + 1)
      (wireCommitComp (kernelPayload S s.kernel t) (receiptRoot hash s.log)) :=
  wireCommitComp_queryBounded _ _ (kernelPayload_length S s.kernel t)

/-! ## §S — the state-commit binding, RE-GROUNDED on the keyed sampled-oracle floor.

⚑⚑ **THE HEADLINE SUCCESSOR to the deleted `stateCommit_binds_from_polyTime`.**  §R's reduction
shape is kept — a state forgery becomes a collision — but the GAME moves to the model where a
collision floor is PROVABLE: the hash is a SAMPLED ORACLE the adversary can only QUERY
(`Dregg2.Crypto.RomChainedReduction`, resting on `KeyedRomFloor.keyedRom_hard` — the birthday
bound, a theorem).  The carrier below is §Q's DEPLOYED SCHEDULE: a 4-limb head, then `deployedBlockCount` three-limb
blocks (the body's `chunk31` chunks + the iroot block — `deployed_blockCount`, `chunk31_three_wide`), each
step re-absorbing the previous digest, tag-separated by the four-tag space `WideKeyed` samples.
The binding takes NO floor hypothesis — `stateCommitRom_binds`'s only inputs are a polynomial query
budget and the forger — and §P's `Classical.choice` collision-answerer is PROVABLY excluded at this
layer (`stateCommitRom_choiceForger_excluded`).

⚑ **THE MODELLING STEP, OUT LOUD (not smuggled).**  The floor demands a `λ`-GROWING digest space
(`hw : |R l| = 2^l`).  The deployed Poseidon2 squeeze is a FIXED vector of 31-bit BabyBear felts —
there is NO `l` at which its cardinality is `2^l`.  So this section idealizes the felt at width
`2^l` (digests `Fin (2^l)`, limbs `Fin (2^l)`), exactly the standard random-oracle idealization of
the deployed sponge at an asymptotic digest width, and exactly the deliberate labelled step
`Dregg2.lean` §DomainSeparatedCREffRegrounded demands.  What IS proved: the deployed CHAIN
SCHEDULE's binding, over a sampled oracle, against query-counted adversaries, with no false
hypothesis.  What is NOT claimed: that the fixed BabyBear Poseidon2 is a random oracle, or any
derivation from the deployed permutation's algebra.  The un-idealizable residual is priced by §P's
refutation: NO floor over the fixed public function survives, at any honest adversary class. -/

/-- **THE IDEALIZED STATE-COMMIT ORACLE FAMILY** — four domain-separation tags (the `WideKeyed`
shape), a domain of head blocks (4 idealized limbs) ⊕ step inputs (digest × 3-limb block), and a
`λ`-bit digest space.  The sum gives head/step domain separation for free. -/
def stateCommitRomFamily : KeyedRomFamily where
  Key := fun _ => Fin 4
  D := fun l => (Fin 4 → Fin (2 ^ l)) ⊕ (Fin (2 ^ l) × (Fin 3 → Fin (2 ^ l)))
  R := fun l => Fin (2 ^ l)
  keyFin := fun _ => inferInstance
  keyDec := fun _ => inferInstance
  keyNe := fun _ => ⟨0⟩
  dFin := fun _ => inferInstance
  dDec := fun _ => inferInstance
  dNe := fun l => ⟨Sum.inl (fun _ => ⟨0, by positivity⟩)⟩
  rFin := fun _ => inferInstance
  rDec := fun _ => inferInstance
  rNe := fun l => ⟨⟨0, by positivity⟩⟩

/-- **THE DEPLOYED-SCHEDULE CHAINED CARRIER**: 4-limb head, `deployedBlockCount` three-limb blocks, step encoding
`(digest, block)` — §Q's fixed-width concatenation `acc ++ c`, made type-level, which is what turns
its injectivity into a LAYOUT fact.  The context is the tag both chains share, exactly as in §R's
`stateCommitBreakGame`, where one sampled tag prices both commits. -/
def stateCommitRomCarrier : RomChainedCarrier stateCommitRomFamily where
  Ctx := fun _ => Fin 4
  Hd := fun l => Fin 4 → Fin (2 ^ l)
  Blk := fun l => Fin 3 → Fin (2 ^ l)
  len := fun _ => deployedBlockCount
  hdDec := fun _ => inferInstance
  blkDec := fun _ => inferInstance
  encHd := fun _ c h => (c, Sum.inl h)
  encStep := fun _ c r b => (c, Sum.inr (r, b))
  encHd_inj := fun _ _ _ _ h => Sum.inl_injective (congrArg Prod.snd h)
  encStep_inj := fun _ _ r b r' b' h => by
    have h2 := Sum.inr_injective (congrArg Prod.snd h)
    exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩

/-- The carrier's chain length IS §Q's deployed block count — the schedule weld. -/
theorem stateCommitRomCarrier_len_eq_deployed (l : ℕ) (xs : List ℤ) (ir : ℤ)
    (hlen : xs.length = kernelPayloadWidth) :
    stateCommitRomCarrier.len l = (chunk31 (xs.drop 4) ++ [[ir, 0, 0]]).length := by
  rw [deployed_blockCount xs ir hlen]
  rfl

/-- The idealized digest space is exactly `2^l` — the `hw` obligation, DISCHARGED.  (This is the one
obligation the deployed fixed BabyBear felt cannot meet; §S header.) -/
theorem stateCommitRom_card_R (l : ℕ) :
    letI := stateCommitRomFamily.rFin l
    Fintype.card (stateCommitRomFamily.R l) = 2 ^ l := by
  show Fintype.card (Fin (2 ^ l)) = 2 ^ l
  simp

/-- The tag-separated domain is strictly larger than the digest space — compressing, as deployed. -/
theorem stateCommitRom_compressing (l : ℕ) :
    letI := (stateCommitRomFamily.toRomFamily).dFin l
    letI := (stateCommitRomFamily.toRomFamily).rFin l
    Fintype.card (stateCommitRomFamily.toRomFamily.R l)
      < Fintype.card (stateCommitRomFamily.toRomFamily.D l) := by
  show Fintype.card (Fin (2 ^ l))
      < Fintype.card (Fin 4 × ((Fin 4 → Fin (2 ^ l)) ⊕ (Fin (2 ^ l) × (Fin 3 → Fin (2 ^ l)))))
  simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fun, Fintype.card_fin]
  have h1 : 0 < 2 ^ l := by positivity
  nlinarith [h1, Nat.one_le_pow 3 (2 ^ l) h1]

/-- **⚑⚑ THE RE-GROUNDED STATE-COMMIT BINDING — NO floor hypothesis; the floor is a THEOREM.**
A query-bounded chained forger against the deployed state-commit schedule has NEGLIGIBLE advantage:
the eight-felt chained anchor binds the head and every block of its payload except with negligible
probability, over the sampled tag-separated oracle.  Budget accounting: the forger's `Q` plus the
extractor's re-walk of both chains (`deployedExtractorBudget = 2·deployedBlockCount + 2`).  This is what the deleted
`stateCommit_binds_from_polyTime` pretended to be — same reduction shape, but what sits under it is
`keyedRom_hard` (proved) instead of a floor §P refutes. -/
theorem stateCommitRom_binds (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => (((Q l + deployedExtractorBudget : ℕ) : ℝ)
      * ((Q l + deployedExtractorBudget : ℕ) : ℝ) + 1)))
    (A : Adversary (romChainedGame stateCommitRomFamily stateCommitRomCarrier))
    (hA : RomChainedEff stateCommitRomFamily stateCommitRomCarrier Q A) :
    Negl (gameAdv (romChainedGame stateCommitRomFamily stateCommitRomCarrier) A) :=
  romChained_binds stateCommitRomFamily stateCommitRomCarrier Q
    (fun l => Q l + deployedExtractorBudget)
    (fun l => by
      show Q l + (2 * deployedBlockCount + 2) ≤ Q l + deployedExtractorBudget
      simp only [deployedExtractorBudget]
      omega)
    hQ stateCommitRom_card_R A hA

/-- **⚑ THE `Classical.choice` COLLISION-ANSWERER IS EXCLUDED AT THE STATE-COMMIT LAYER** — §P's
refutation strategy, transplanted to the sampled-oracle state-commit game, cannot produce a member
of the query-bounded class: any forger with non-negligible advantage is outside it.  It would have
to know a collision of an oracle it never queried
(`RomOracle.OracleComp.eval_congr_of_agree_on_queried` forbids that). -/
theorem stateCommitRom_choiceForger_excluded (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => (((Q l + deployedExtractorBudget : ℕ) : ℝ)
      * ((Q l + deployedExtractorBudget : ℕ) : ℝ) + 1)))
    (A : Adversary (romChainedGame stateCommitRomFamily stateCommitRomCarrier))
    (hnn : ¬ Negl (gameAdv (romChainedGame stateCommitRomFamily stateCommitRomCarrier) A)) :
    ¬ RomChainedEff stateCommitRomFamily stateCommitRomCarrier Q A :=
  fun hA => hnn (stateCommitRom_binds Q hQ A hA)

/-- **THE ⊤ POLE at the idealized family** — the UNRESTRICTED floor over the same keyed game is
FALSE (compressing pigeonhole), so the query bound is load-bearing here exactly as at deployed
parameters. -/
theorem stateCommitRom_top_false :
    ¬ Hard (keyedRomGame stateCommitRomFamily) (fun _ => True) :=
  keyedRom_top_false stateCommitRomFamily stateCommitRom_compressing

/-- **⚑⚑ THE WHOLE VERDICT AT THE DEPLOYED SCHEDULE AND A CONCRETE BUDGET**
(`Q = deployedExtractorBudget` — enough for a forger to compute both its chains honestly, §Q's
`deployedBlockCount + 1` queries each).  Four facts at once:

  1. the re-grounded binding FIRES: every such chained forger's advantage is negligible;
  2. the class is INHABITED (a fixed-answer 0-query member), and its advantage is negligible by 1 —
     the general defanging of the DISTINCT fixed-pair refuter shape (the one that wins with
     probability `1` against the fixed public function) is `fixedChainedForger_negl`: admitted by
     the class, collapsed by the sampling, not excluded by fiat;
  3. the game is WINNABLE (`l ≥ 1`: at a constant oracle any two distinct payloads equivocate), so
     the negligible advantage is earned against a live event;
  4. the UNRESTRICTED floor at the same game is FALSE — the query bound does the work.

The budget is not special: `stateCommitRom_binds` takes any polynomially bounded `Q`. -/
theorem stateCommitRom_verdict :
    (∀ A, RomChainedEff stateCommitRomFamily stateCommitRomCarrier (fun _ => 124) A →
        Negl (gameAdv (romChainedGame stateCommitRomFamily stateCommitRomCarrier) A))
      ∧ (∃ A, RomChainedEff stateCommitRomFamily stateCommitRomCarrier (fun _ => 124) A
            ∧ Negl (gameAdv (romChainedGame stateCommitRomFamily stateCommitRomCarrier) A))
      ∧ (∀ l, 1 ≤ l →
          ∃ (H : (romChainedGame stateCommitRomFamily stateCommitRomCarrier).Inst l)
            (p : (romChainedGame stateCommitRomFamily stateCommitRomCarrier).Ans l),
            (romChainedGame stateCommitRomFamily stateCommitRomCarrier).wins l H p)
      ∧ ¬ Hard (keyedRomGame stateCommitRomFamily) (fun _ => True) := by
  have hpoly : PolyBounded
      (fun l => ((((fun _ : ℕ => 124) l + deployedExtractorBudget : ℕ) : ℝ)
        * (((fun _ : ℕ => 124) l + deployedExtractorBudget : ℕ) : ℝ) + 1)) := by
    simp only [deployedExtractorBudget_eq]
    refine ⟨0, 62501, ?_⟩   -- (124 + 126)² + 1 = 250² + 1 at the 187-limb schedule
    filter_upwards with n
    norm_num
  refine ⟨fun A hA => stateCommitRom_binds (fun _ => 124) hpoly A hA, ?_, ?_,
    stateCommitRom_top_false⟩
  · refine ⟨romChainedAdv stateCommitRomFamily stateCommitRomCarrier
      (fixedChainedComp stateCommitRomFamily stateCommitRomCarrier
        (fun _ => (0 : Fin 4))
        (fun l => ((fun _ => (⟨0, by positivity⟩ : Fin (2 ^ l))),
          fun _ _ => (⟨0, by positivity⟩ : Fin (2 ^ l))))
        (fun l => ((fun _ => (⟨0, by positivity⟩ : Fin (2 ^ l))),
          fun _ _ => (⟨0, by positivity⟩ : Fin (2 ^ l))))), ?_, ?_⟩
    · exact fixedChainedForger_in_eff stateCommitRomFamily stateCommitRomCarrier _ _ _ _
    · exact stateCommitRom_binds (fun _ => 124) hpoly _
        (fixedChainedForger_in_eff stateCommitRomFamily stateCommitRomCarrier _ _ _ _)
  · intro l hl
    have h2 : 1 < 2 ^ l := Nat.one_lt_two_pow_iff.mpr (by omega)
    have hpos : 0 < 2 ^ l := by positivity
    refine ⟨fun _ => (⟨0, hpos⟩ : Fin (2 ^ l)),
      ((0 : Fin 4),
       ((fun _ => (⟨0, hpos⟩ : Fin (2 ^ l))), fun _ _ => (⟨0, hpos⟩ : Fin (2 ^ l))),
       ((fun _ => (⟨1, h2⟩ : Fin (2 ^ l))), fun _ _ => (⟨0, hpos⟩ : Fin (2 ^ l)))), ?_⟩
    refine romChainedGame_win_at_const stateCommitRomFamily stateCommitRomCarrier l _ _ _ ?_ _
    intro h
    have h0 : (⟨0, hpos⟩ : Fin (2 ^ l)) = ⟨1, h2⟩ := congrFun (congrArg Prod.fst h) 0
    simp [Fin.ext_iff] at h0

-- ⚑ CROSS-SOURCE GATE (was `kernelPayloadWidth == 184`, a constant against its own definition that
-- the key-nonet flag day moved without reddening).  The boundary codec's payload width against the
-- verified layout's extent, and the whole modelled schedule against that width.
#guard kernelPayloadWidth == Dregg2.Circuit.Emit.rotatedNumPreLimbs
#guard deployedBlockCount == chunkCount (Dregg2.Circuit.Emit.rotatedNumPreLimbs - 4) + 1
#guard deployedExtractorBudget == 2 * deployedBlockCount + 2
#guard stateCommitRomCarrier.len 0 == deployedBlockCount
#guard receiptRoot (fun xs => xs.sum)
  [{ actor := 1, src := 1, dst := 2, amt := 3 }] == 7

#assert_axioms kernelPayload_length
#assert_axioms turnDigest_binds_or_collides
#assert_axioms turnDigest_binds
#assert_axioms receiptRootFind_self
#assert_axioms receiptRoot_binds_or_collides
#assert_axioms receiptRoot_binds
#assert_axioms receiptRootColl_refutable
#assert_axioms receiptRootColl_refutes_poseidon2CR
#assert_axioms wireCommitR8_length
#assert_axioms stateDecode8_pre_faithful
#assert_axioms stateDecode8_post_faithful
#assert_axioms Felt8.set_ne
#assert_axioms stateCommitBreakGame_wins_iff
#assert_axioms stateDecode8_forgery_is_break
#assert_axioms state_wins_imp
#assert_axioms state_adv_le
#assert_axioms stateCommit_binds_advantage_bound
#assert_axioms chunk31_len_le
#assert_axioms chainCollFind_len_le
#assert_axioms wireCommit8Find_len_le
#assert_axioms hashFloor_isPolyTime_inhabited
#assert_axioms stateCommit_floor_top_false_babyBear
#assert_axioms stateCommit_floor_bot_vacuous
#assert_axioms the_reduced_stateCommit_bound_fires
#assert_axioms exists_short_wide_collision
#assert_axioms shortWideCollAdv_wins
#assert_axioms shortWideCollAdv_isPolyTime
#assert_axioms stateCommit_floor_polyTime_false_babyBear
#assert_axioms chainEval_append_eq_chainFrom8
#assert_axioms wireCommitComp_eval
#assert_axioms chunk31_three_wide
#assert_axioms deployed_blockCount
#assert_axioms wireCommitComp_queryBounded
#assert_axioms commit8_as_oracleComp
#assert_axioms commit8_queryBounded
#assert_axioms stateCommitRomCarrier_len_eq_deployed
#assert_axioms stateCommitRom_card_R
#assert_axioms stateCommitRom_compressing
#assert_axioms stateCommitRom_binds
#assert_axioms stateCommitRom_choiceForger_excluded
#assert_axioms stateCommitRom_top_false
#assert_axioms stateCommitRom_verdict

end Market.WideCommitBoundary
