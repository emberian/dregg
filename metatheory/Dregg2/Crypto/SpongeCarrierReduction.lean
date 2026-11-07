/-
# `Dregg2.Crypto.SpongeCarrierReduction` — the ONE-FELT SPONGE reduction spine.

## What this is for

`Circuit.InjectiveFloorRegrounded` gave the WIDE (8-lane) carriers a security reduction: a forgery as a
`Game`, an extractor as a map of adversaries, an unconditional advantage inequality, and the conclusion
under `FloorGames.HashCRHardQuant`. `Market.WideCommitBoundary` then discharged the efficiency
obligation with `CostTactics.poly_time`, so `hEff` stopped being a floating parameter.

The ~1-felt sponge carriers never got that treatment. Dozens of deployed bindings across the umem/heap,
cap-root, rotation, membership and accumulator lanes are still stated as

    theorem X_binds (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) … : a = b

and `Poseidon2SpongeCR` is **FALSE at deployed BabyBear parameters** —
`Circuit.HashFloorHonesty.poseidon2SpongeCR_false_babyBear`: the sponge lands in one bounded field
while `List ℤ` is infinite, so collisions exist by pigeonhole. Every such theorem is **VACUOUSLY TRUE
at the deployed hash**: it is a true implication whose hypothesis nothing deployed satisfies, and
`#assert_axioms` cannot see it, because the proofs are clean and the HYPOTHESIS is the flaw.

This module is the shared spine that lets each of those sites be rebuilt as a real reduction, ONCE,
instead of forty times.

## The shape

  * **§1 — `SpongeKeyed`**: the deployed unkeyed sponge together with its domain-separation tag space.
    Keying is the standard keyed-from-unkeyed model: an unkeyed fixed hash lets an adversary hardcode a
    known collision (advantage `1`), so the collision game must sample something. The deployed "key" is
    the domain-separation tag the prover already absorbs ahead of each message.
    `spongeFamily` lifts it to a `HashFloorHonesty.KeyedHashFamily`, and `deployedSponge_is_family_instance`
    pins that the family's instance at `deployedTag` IS the function the prover computes — `rfl`.

    ⚑ This is the SAME OBJECT as `Circuit.Poseidon2KeyedBridge.DomainSeparatedSponge`, not a
    re-derivation of it. It is restated here only because `Poseidon2KeyedBridge` sits ABOVE
    `Circuit.OodCommitmentBinding` in the import graph (via `FloorRegroundedConsumers`), and
    `OodCommitmentBinding` is one of the sites that has to consume this spine. The identification is
    PROVED, not asserted, in `Dregg2.Crypto.SpongeCarrierBridge`
    (`spongeFamily_ofDomainSeparated`, by `rfl`), so nothing here is a mirror of an interface — it is
    the same interface, reachable from lower down.

  * **§2 — `SpongeCarrier`**: what a deployed 1-felt commitment site must supply, and the ONLY thing it
    must supply. A context `Ctx` both claims agree on (a Merkle index and sibling path, a turn, an
    address list — whatever the deployment fixes), a payload `Val` the commitment is supposed to BIND,
    the commitment `enc`, and — the real content — a **collision extractor** `find` with its spec:
    two DISTINCT payloads carrying the SAME commitment yield two DISTINCT lists on which the sponge
    genuinely collides. That is a total function and an unconditional theorem; it assumes nothing.

  * **§3 — the reduction**: `carrierBreakGame` (the forgery, with the break IN the win relation),
    `carrierBreakToFinder` (the extractor AS A MAP OF ADVERSARIES), `carrier_adv_le` (the advantage
    inequality — note the adversary class does NOT appear in it), and
    `carrier_binds_advantage_bound` (the security conclusion under `HashCRHardQuant (spongeFamily D) Eff`).

  * **§4 — the answer-size cost model** (`carrierAnsSize`/`spongeAnsSize`): the honest record of what
    that model prices. ⚑ The `IsPolyTime` discharge that stood here is DELETED — see the SUPERSEDED
    section below; the discharged successor is `RomBindingReduction.romCarrier_binds`.

  * **§5 — both poles, and the canary.** `Eff := ⊤` is FALSE at real BabyBear parameters
    (`carrierFloor_top_false_babyBear`); `Eff := ⊥` is vacuous (`carrierFloor_bot_vacuous`); the class
    at which §4 instantiates is PROVED INHABITED (`carrierFloor_isPolyTime_inhabited`) while the
    ⊤-collapse witness is PROVED EXCLUDED (`CostAdversary.bruteForce_not_polyTime`). The canary
    (`the_carrier_bound_needs_the_extracted_finder`) reds if a future edit lets the conclusion follow
    from the floor applied at some OTHER adversary.

## ⚑ The `_from_polyTime` discharges are DELETED (07-24); the successor is LANDED

`Exec.SystemRootsBindingReduction.sysRoots_floor_polyTime_false_babyBear` REFUTES
`HashCRHardQuant (spongeFamily D) (IsPolyTime (spongeAnsSize D))` at the deployed sponge, so §4's
`carrier_binds_from_polyTime` (and §6's `idCarrier_binds_from_polyTime` inhabitation form) were
VACUOUS at deployed parameters — and `Crypto.RomBindingReduction`'s header proves the fixed-function
game cannot be repaired by ANY `Eff`.  BOTH ARE DELETED.  The DISCHARGED successor is
`Crypto.RomBindingReduction.romCarrier_binds` on the PROVED keyed-ROM floor (with
`Crypto.RomCarrierSites` as the per-site kit), and the inhabitation witness the deleted
`idCarrier_binds_from_polyTime` supplied lives there as `RomBindingReduction.idRomCarrier_binds`
(the identity carrier fires end-to-end on the proved floor).  Every deployed consumer is re-pointed
(SystemRoots §7, Heap §2.4, FloorRegroundedConsumers, OodCommitmentBinding, the `Emit/*` sites).
§4's answer-size encodings and both-poles teeth remain as the honest record of what the answer-size
cost model can and cannot price; the `_advantage_bound` forms (`hEff` in the open) stay the honest
fixed-hash statements.

## What this does NOT buy

The reduction does not make the deployed sponge collision-resistant, and it does not close the gap
between the exact-Prop AIR layer and the computational game layer (the game samples a tag; a deployed
trace fixes `deployedTag`). What it buys is exact: the residual is ONE named floor over EFFICIENT
adversaries with both poles proved, in place of a hypothesis that is false at the deployed hash. A
`binds ∨ collides` disjunction would not be enough either — a collision EXISTS by pigeonhole, so that
disjunction is satisfiable through its right branch without binding ever holding. It quantifies over
SOLUTIONS; hardness quantifies over EFFICIENT ADVERSARIES. Hence a game, not a disjunction.

No `sorry`, no `axiom`, no `native_decide`, no `decide` on an opaque `Prop`. Cost stays SYNTACTIC.
-/
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Crypto.CostTactics

namespace Dregg2.Crypto.SpongeCarrierReduction

open Dregg2.Circuit.HashFloorHonesty
  (KeyedHashFamily not_injective_of_finite_range finite_range_of_field_bound)
open Dregg2.Crypto.FloorGames
  (Game Adversary gameAdv gameAdv_mem_unit hashGame HashCRHardQuant hard_bot_vacuous
   hashCRHardQuant_top_false_of_compressing)
open Dregg2.Crypto.ConcreteSecurity (Negl)
open Dregg2.Crypto.ProbCrypto (winProb_le_of_imp negl_of_le)
open Dregg2.Crypto.CostAdversary (AnsSize IsPolyTime isPolyTime_inhabited)
open Dregg2.Crypto.CostTactics

set_option autoImplicit false

/-! ## §1 — the deployed 1-felt sponge, keyed by its domain-separation tag. -/

/-- **THE DEPLOYED SPONGE, KEYED — carrying NO collision-resistance field.** The Rust
`poseidon2::hash_many` / `PaddingFreeSponge` at BabyBear width 16, together with the finite
domain-separation tag space the deployment already absorbs ahead of every message.

⚑ What is NOT a field here: any injectivity or collision-resistance claim. That is the whole point.
`Poseidon2SpongeCR` used to be carried (sometimes as a structure field, so a real deployed value could
not exist at all); it is FALSE at BabyBear, and it is gone. Only the deployed data remains. -/
structure SpongeKeyed where
  /-- The deployed unkeyed sponge — the `Poseidon2Binding` `List ℤ → ℤ` object. -/
  sponge : List ℤ → ℤ
  /-- The domain-separation tag space (the effective key the collision game samples). -/
  Tag : Type
  /-- The tag space is finite (the game samples a uniform tag). -/
  tagFintype : Fintype Tag
  /-- The tag space is inhabited. -/
  tagNonempty : Nonempty Tag
  /-- How a domain-separation tag is absorbed: as a felt prefix ahead of the message. -/
  tagCode : Tag → List ℤ
  /-- The specific tag the deployment computes at this use-site. -/
  deployedTag : Tag

/-- The deployed sponge domain-separated by a specific tag — a fixed unkeyed function per tag. -/
def SpongeKeyed.hashAt (D : SpongeKeyed) (t : D.Tag) (xs : List ℤ) : ℤ :=
  D.sponge (D.tagCode t ++ xs)

/-- The DEPLOYED fixed function the prover actually computes. -/
def SpongeKeyed.deployedHash (D : SpongeKeyed) : List ℤ → ℤ := D.hashAt D.deployedTag

/-- **`spongeFamily D`** — the deployed sponge lifted to a `KeyedHashFamily`, keyed by its
domain-separation tag. Input `List ℤ` (the sponge domain), output `ℤ` (the BabyBear felt). -/
def spongeFamily (D : SpongeKeyed) : KeyedHashFamily where
  Key := fun _ => D.Tag
  Input := List ℤ
  Out := ℤ
  H := fun _ t xs => D.sponge (D.tagCode t ++ xs)
  keyFintype := fun _ => D.tagFintype
  keyNonempty := fun _ => D.tagNonempty
  inputDecEq := inferInstance
  outDecEq := inferInstance

/-- **FAITHFULNESS.** The DEPLOYED fixed function IS the family's instance at the deployed tag — a
definitional equality, so the collision game below is a game about the very function the prover
computes, not an idealization of it. -/
theorem deployedSponge_is_family_instance (D : SpongeKeyed) (n : ℕ) :
    D.deployedHash = (spongeFamily D).H n D.deployedTag := rfl

/-- **THE PROBLEM IS IN THE STATEMENT** — a win of the family's collision game at ANY tag is
definitionally a genuine collision of the deployed domain-separated sponge. -/
theorem spongeGame_wins_iff (D : SpongeKeyed) (n : ℕ) (t : (spongeFamily D).Key n)
    (p : List ℤ × List ℤ) :
    (hashGame (spongeFamily D)).wins n t p ↔
      (p.1 ≠ p.2 ∧ D.hashAt t p.1 = D.hashAt t p.2) :=
  Iff.rfl

/-! ## §2 — what a deployed 1-felt commitment site supplies: an EXTRACTOR, and nothing else.

The per-site content of every rebuilt binding is one total function and one unconditional theorem
about it. Note what is NOT here: no collision-resistance hypothesis, no injectivity, no floor. The
extractor is where the old proof's combinatorics go — the induction that used to peel a CR hypothesis
now LOCATES the colliding pair instead of assuming it away. -/

/-- **`IsSpongeColl h p`** — the pair `p` is a genuine collision of `h`: two DISTINCT lists with the
same digest. The extractor's postcondition, and definitionally the collision game's win relation. -/
def IsSpongeColl (h : List ℤ → ℤ) (p : List ℤ × List ℤ) : Prop :=
  p.1 ≠ p.2 ∧ h p.1 = h p.2

/-- **A DEPLOYED 1-FELT COMMITMENT CARRIER, with its collision extractor.**

`Ctx` is what both claims agree on and the deployment fixes (a Merkle index and sibling path, a turn,
a declared address list); `Val` is the payload the commitment is supposed to BIND; `enc` is the
deployed commitment. The load-bearing field is `find` with `find_spec`: given two DISTINCT payloads
that carry the SAME commitment, it RETURNS two distinct lists on which the sponge actually collides.

`find_spec` is unconditional — it assumes nothing about `h` at all, so unlike the binding it replaces
it is a true theorem at deployed BabyBear parameters. `size`/`outCo`/`outBo`/`find_len_le` are the
cost model's output-growth obligation: the extractor must not blow up its input, or the reduction
would not preserve efficiency. That fact is PROVED per site, never assumed. -/
structure SpongeCarrier where
  /-- The shared context both claims agree on (the deployment's fixed opening data). -/
  Ctx : Type
  /-- The payload the commitment is supposed to bind. -/
  Val : Type
  /-- Decidable equality on payloads (the win event compares two of them, and is counted). -/
  valDecEq : DecidableEq Val
  /-- The DEPLOYED commitment, as a function of the sponge. -/
  enc : (List ℤ → ℤ) → Ctx → Val → ℤ
  /-- **THE EXTRACTOR** — a total function from an equivocation to a claimed sponge collision. -/
  find : (List ℤ → ℤ) → Ctx → Val → Val → List ℤ × List ℤ
  /-- **THE EXTRACTOR IS CORRECT, UNCONDITIONALLY.** Two distinct payloads with the same commitment
  yield a genuine collision of the sponge. No floor, no injectivity, no hypothesis on `h`. -/
  find_spec : ∀ (h : List ℤ → ℤ) (c : Ctx) (a b : Val), a ≠ b → enc h c a = enc h c b →
    IsSpongeColl h (find h c a b)
  /-- The answer-encoding size of one payload in its context — the game's OWN size measure, concrete
  on purpose (a degenerate `0` would make output free and the cost model vacuous). -/
  size : Ctx → Val → ℕ
  /-- The extractor's output-growth slope. -/
  outCo : ℕ
  /-- The extractor's output-growth intercept. -/
  outBo : ℕ
  /-- **THE EXTRACTOR DOES NOT BLOW UP ITS INPUT** — proved per site, the cost model's obligation. -/
  find_len_le : ∀ (h : List ℤ → ℤ) (c : Ctx) (a b : Val),
    (find h c a b).1.length + (find h c a b).2.length ≤ outCo * (size c a + size c b) + outBo

/-- **THE COMMONEST CARRIER SHAPE — a flat, injectively-encoded preimage.** Most deployed 1-felt
commitments are `hash (encode v)` for a STRUCTURAL encoding that is injective on the nose: a fixed
tuple of felts laid out in a fixed order (`hash [holder, target, rights, op]`,
`hash [domain_tag, coll, key]`, `hash [addr, value]`, …). For those the extractor is simply the two
encodings, and the old CR-peeling proof — `hCR _ _ h` followed by `List.cons.injEq` as many times as
the arity — collapses into `encode_inj`, which is pure combinatorics and carries no floor.

⚑ Note what moved. The old proofs used collision-resistance to invert the HASH. Here injectivity is
required only of the ENCODING, which is a layout fact the deployment genuinely satisfies, and the
hash's contribution is priced by the reduction instead of assumed. -/
def SpongeCarrier.ofFlatEncoding {V : Type} (dec : DecidableEq V)
    (encode : V → List ℤ) (encode_inj : ∀ a b : V, encode a = encode b → a = b)
    (w : ℕ) (hw : ∀ v, (encode v).length ≤ w) : SpongeCarrier where
  Ctx := Unit
  Val := V
  valDecEq := dec
  enc := fun h _ v => h (encode v)
  find := fun _ _ a b => (encode a, encode b)
  find_spec := fun _ _ a b hne heq => ⟨fun hc => hne (encode_inj a b hc), heq⟩
  size := fun _ _ => w
  outCo := 1
  outBo := 0
  find_len_le := fun _ _ a b => by
    have ha := hw a
    have hb := hw b
    simp only [Nat.one_mul, Nat.add_zero]
    omega

/-- The flat carrier's commitment IS the deployed `hash (encode v)`, by `rfl` — so a site that builds
its carrier this way is landing on the function it actually computes, not on a re-derivation. -/
theorem ofFlatEncoding_enc {V : Type} (dec : DecidableEq V) (encode : V → List ℤ)
    (hinj : ∀ a b : V, encode a = encode b → a = b) (w : ℕ) (hw : ∀ v, (encode v).length ≤ w)
    (h : List ℤ → ℤ) (v : V) :
    (SpongeCarrier.ofFlatEncoding dec encode hinj w hw).enc h () v = h (encode v) := rfl

/-! ## §3 — the reduction: the forgery as a GAME, the extractor as a MAP OF ADVERSARIES. -/

/-- **THE CARRIER FORGERY GAME.** The adversary is handed a uniformly sampled domain-separation tag and
WINS iff it outputs a context and two DISTINCT payloads carrying the SAME deployed commitment — i.e. it
equivocates the very commitment the circuit publishes. The break is IN the win relation; this is the
statement the old `X_binds` was trying to make, with the quantifier over efficient adversaries that
cryptographic hardness actually has. -/
def carrierBreakGame (D : SpongeKeyed) (C : SpongeCarrier) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => C.Ctx × C.Val × C.Val
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t p =>
    p.2.1 ≠ p.2.2 ∧ C.enc (D.hashAt t) p.1 p.2.1 = C.enc (D.hashAt t) p.1 p.2.2
  winsDec := fun _ t p => by
    letI := C.valDecEq
    infer_instance

/-- **THE PROBLEM IS IN THE STATEMENT** — the win relation is a genuine equivocation of the deployed
commitment at the sampled tag. -/
theorem carrierBreakGame_wins_iff (D : SpongeKeyed) (C : SpongeCarrier) (l : ℕ) (t : D.Tag)
    (p : C.Ctx × C.Val × C.Val) :
    (carrierBreakGame D C).wins l t p ↔
      (p.2.1 ≠ p.2.2 ∧ C.enc (D.hashAt t) p.1 p.2.1 = C.enc (D.hashAt t) p.1 p.2.2) :=
  Iff.rfl

/-- **THE EXTRACTOR, AS A MAP OF ADVERSARIES.** A commitment equivocator becomes a sponge-collision
finder by running the carrier's extractor on its own output. This is the reduction; `find_spec` is why
it works, and it works at every tag, unconditionally. -/
def carrierBreakToFinder (D : SpongeKeyed) (C : SpongeCarrier)
    (A : Adversary (carrierBreakGame D C)) : Adversary (hashGame (spongeFamily D)) where
  run := fun l t => let p := A.run l t; C.find (D.hashAt t) p.1 p.2.1 p.2.2

/-- **⚑ WIN-PRESERVATION — the reduction, at the game level.** Every tag on which the equivocator wins,
the extracted finder wins the collision game of the DEPLOYED sponge. -/
theorem carrier_wins_imp (D : SpongeKeyed) (C : SpongeCarrier)
    (A : Adversary (carrierBreakGame D C)) (l : ℕ) (t : D.Tag)
    (hwin : (carrierBreakGame D C).wins l t (A.run l t)) :
    (hashGame (spongeFamily D)).wins l t ((carrierBreakToFinder D C A).run l t) :=
  C.find_spec (D.hashAt t) (A.run l t).1 (A.run l t).2.1 (A.run l t).2.2 hwin.1 hwin.2

/-- **⚑ THE ADVANTAGE INEQUALITY — UNCONDITIONAL, over ALL adversaries.** The equivocator's advantage
is at most the extracted collision finder's, at every security parameter, over the same sampled tag
space. Note what does NOT appear in this statement: the adversary class. The inequality is a fact
about the extractor, true of every adversary whatsoever; `Eff` enters only when the floor is applied. -/
theorem carrier_adv_le (D : SpongeKeyed) (C : SpongeCarrier)
    (A : Adversary (carrierBreakGame D C)) (l : ℕ) :
    gameAdv (carrierBreakGame D C) A l
      ≤ gameAdv (hashGame (spongeFamily D)) (carrierBreakToFinder D C A) l := by
  refine @winProb_le_of_imp _ (D.tagFintype) _ _ (fun t ht => ?_)
  replace ht := (Adversary.hit_eq_true _ _ _).mp ht
  exact (Adversary.hit_eq_true _ _ _).mpr (carrier_wins_imp D C A l t ht)

/-- **⚑ THE REDUCED BINDING — the security conclusion, from the DEPLOYED sponge's collision floor.**

Under the deployed sponge's collision floor at the class `Eff`, a commitment equivocator whose
extracted finder lies in that class has NEGLIGIBLE advantage: the deployed 1-felt commitment binds its
payload except with negligible probability.

This is what replaces `X_binds (hCR : Poseidon2SpongeCR hash)`. The difference is not cosmetic. The old
hypothesis is FALSE at BabyBear, so the old theorem said nothing about the deployed hash; this one
quantifies over efficient adversaries and is priced at both poles in §5.

⚑ `hEff` is a PARAMETER here — the standard "the reduction is efficient", in the open, at an arbitrary
class. §4 DISCHARGES it at `Eff := IsPolyTime`. -/
theorem carrier_binds_advantage_bound (D : SpongeKeyed) (C : SpongeCarrier)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (carrierBreakGame D C))
    (hEff : Eff (carrierBreakToFinder D C A))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (carrierBreakGame D C) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (carrierBreakGame D C) A l).1)
    (carrier_adv_le D C A) (hCR _ hEff)

/-! ## §4 — `hEff` DISCHARGED: efficiency preservation is a THEOREM, not a parameter. -/

/-- **THE FORGERY GAME'S ANSWER ENCODING** — the two payloads at their shared context, under the
carrier's own size measure. Concrete on purpose: the size measure belongs to the GAME, and leaving it
open would let a degenerate `sz := 0` make the adversary's output free. -/
def carrierAnsSize (D : SpongeKeyed) (C : SpongeCarrier) : AnsSize (carrierBreakGame D C) :=
  fun _ p => C.size p.1 p.2.1 + C.size p.1 p.2.2

/-- **THE COLLISION GAME'S ANSWER ENCODING** — the two claimed preimages of the deployed sponge. -/
def spongeAnsSize (D : SpongeKeyed) : AnsSize (hashGame (spongeFamily D)) :=
  fun _ p => p.1.length + p.2.length

/-! ## §5 — the floor, PRICED at both poles, plus the canary and the inhabitation tooth. -/

/-- **⚑ THE ⊤ POLE — the floor is FALSE at the REAL BabyBear parameters.** A sponge whose output is a
genuine BabyBear felt (`0 ≤ · < p`, `p = 2³¹ − 2²⁷ + 1`) has finite range while `List ℤ` is infinite,
so a collision exists at every tag and the floor at the UNRESTRICTED class is FALSE.

This is the honest price of `hEff`, stated as a theorem rather than a promise. What the reduction buys
is NOT a floor the deployed sponge satisfies at ⊤ — no such floor exists — it is that the residual is
ONE named class with both poles proved, in place of a hypothesis that is simply false.

⚑ The `⊤` is WRITTEN OUT in the statement. It used to be reachable through
`HashFloorHonesty.CollisionResistant`, which was a spelling of this very proposition; that name is
DELETED (2026-07-28) and the proof now applies `FloorGames.hashCRHardQuant_top_false_of_compressing`
directly, with no intermediate rewrite hiding which adversary class is in play. -/
theorem carrierFloor_top_false_babyBear (D : SpongeKeyed)
    (hb : ∀ xs, 0 ≤ D.sponge xs ∧ D.sponge xs < (2013265921 : ℤ)) :
    ¬ HashCRHardQuant (spongeFamily D) (fun _ => True) := by
  refine hashCRHardQuant_top_false_of_compressing (spongeFamily D) ⟨([] : List ℤ)⟩ (fun l t => ?_)
  have hfin : (Set.range (fun xs : List ℤ => D.sponge (D.tagCode t ++ xs))).Finite := by
    refine (finite_range_of_field_bound D.sponge _ hb).subset ?_
    rintro _ ⟨xs, rfl⟩
    exact ⟨D.tagCode t ++ xs, rfl⟩
  have hni := not_injective_of_finite_range (fun xs : List ℤ => D.sponge (D.tagCode t ++ xs)) hfin
  rw [Function.not_injective_iff] at hni
  obtain ⟨x, y, heq, hne⟩ := hni
  exact ⟨x, y, hne, heq⟩

/-- **THE ⊥ POLE — vacuous.** At the empty class the floor holds for ANY sponge, including a completely
broken one. Recorded so the floor's satisfiability can never be mistaken for evidence. -/
theorem carrierFloor_bot_vacuous (D : SpongeKeyed) :
    HashCRHardQuant (spongeFamily D) (fun _ => False) :=
  hard_bot_vacuous _

/-- **(TOOTH — the class §4 instantiates at is NOT EMPTY.)** `IsPolyTime (spongeAnsSize D)` contains
the constant finder, because the answer it writes has size `0` under the game's own encoding. Together
with `CostAdversary.bruteForce_not_polyTime` (the ⊤-collapse witness is PROVED excluded) this pins the
instantiated floor STRICTLY between the two poles — which is exactly what `Eff := ⊤` and `Eff := ⊥`
both fail to be. -/
theorem carrierFloor_isPolyTime_inhabited (D : SpongeKeyed) :
    IsPolyTime (spongeAnsSize D)
      (Dregg2.Crypto.CostAdversary.idAdv (O := Unit) (Q := fun _ => Unit) (R := fun _ => Unit)
        (fun _ _ => (([] : List ℤ), ([] : List ℤ)))).toAdversary :=
  isPolyTime_inhabited _ _ ⟨0, 0, fun _ _ => by simp [spongeAnsSize]⟩

/-- **(CANARY — the binding does NOT follow from the floor applied at ANOTHER finder.)** Strip the
reduction: try to conclude the equivocator's negligibility from the collision floor applied at some
OTHER adversary `B`, rather than the one EXTRACTED from it. It does not go through — only
`carrier_adv_le` connects the two games. This tooth REDS if a future edit accidentally reconnects them,
which is what would happen if the conclusion were ever weakened to something the floor implies for
free. -/
example (D : SpongeKeyed) (C : SpongeCarrier)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (carrierBreakGame D C))
    (B : Adversary (hashGame (spongeFamily D))) (hB : Eff B)
    (hCR : HashCRHardQuant (spongeFamily D) Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (carrierBreakGame D C) A) := hCR B hB)
  trivial

/-- **THE POSITIVE POLE — the RIGHT floor DOES discharge it.** A gate that refuses everything is a
broken keystone, not a fixed one: with the floor at the EXTRACTED finder, the binding fires. -/
theorem the_carrier_bound_needs_the_extracted_finder (D : SpongeKeyed) (C : SpongeCarrier)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (carrierBreakGame D C))
    (hEff : Eff (carrierBreakToFinder D C A))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (carrierBreakGame D C) A) :=
  carrier_binds_advantage_bound D C Eff A hEff hCR

/-! ## §6 — the trivial carrier, so the spine itself is witnessed non-vacuous.

The identity commitment `enc h _ v = h v` on `List ℤ` payloads: an equivocation IS a collision, so the
extractor is the identity pair. Small, but it proves the `SpongeCarrier` interface is INHABITED — a
structure nothing can satisfy is the failure mode this whole sweep exists to retire. -/

/-- The identity carrier: the commitment IS the sponge, so an equivocation IS a collision. -/
def idCarrier : SpongeCarrier where
  Ctx := Unit
  Val := List ℤ
  valDecEq := inferInstance
  enc := fun h _ v => h v
  find := fun _ _ a b => (a, b)
  find_spec := fun _ _ _ _ hne heq => ⟨hne, heq⟩
  size := fun _ v => v.length
  outCo := 1
  outBo := 0
  find_len_le := fun _ _ a b => by simp

/-! The identity carrier's inhabitation/fires witness now lives on the PROVED floor:
`RomBindingReduction.idRomCarrier` / `idRomCarrier_binds` (the deleted `idCarrier_binds_from_polyTime`
carried it on the refuted `IsPolyTime` floor, so it witnessed nothing at deployed parameters). -/

/-! ## §7 — axiom-hygiene pins. -/

#assert_axioms deployedSponge_is_family_instance
#assert_axioms spongeGame_wins_iff
#assert_axioms carrierBreakGame_wins_iff
#assert_axioms carrier_wins_imp
#assert_axioms carrier_adv_le
#assert_axioms carrier_binds_advantage_bound
#assert_axioms carrierFloor_top_false_babyBear
#assert_axioms carrierFloor_bot_vacuous
#assert_axioms carrierFloor_isPolyTime_inhabited
#assert_axioms the_carrier_bound_needs_the_extracted_finder

end Dregg2.Crypto.SpongeCarrierReduction
