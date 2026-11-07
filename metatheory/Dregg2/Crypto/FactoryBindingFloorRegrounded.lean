/-
# `Dregg2.Crypto.FactoryBindingFloorRegrounded` — the `Compress1CR` / factory-`HashInjective` /
`BindingHashCR` injective floors, swept: proved FALSE (or PRECISELY not-false) at deployed parameters,
and their consumers RE-GROUNDED onto REAL collision-game reductions carrying an explicit `Eff`.

## The bug this closes (`VACUITY-SWEEP.md` FINDING 2, cluster 2 — the factory/binding half)

`HashFloorHonesty` proved four injectivity floors FALSE and doc-marked them BROKEN; FINDING 2 found ~20
more with the identical shape, still doc-marked "REALIZABLE", **none re-grounded**. Three are here:

  * `Crypto.CommitmentBinding.Compress1CR c1 := ∀ a b : List ℤ, c1 a = c1 b → a = b` (`:52`)
  * `Exec.Factory.HashInjective := ∀ s₁ s₂ p₁ p₂, factoryHash s₁ p₁ = factoryHash s₂ p₂ → s₁=s₂ ∧ p₁=p₂` (`:75`)
  * `Authority.MacaroonDischarge.BindingHashCR bh := ∀ a b : Tag, bh a = bh b → a = b` (`:171`)

The commit-state siblings (`cellLeafInjective`/`logHashInjective`) are `Circuit.StateCommitFloorRegrounded`.

## ⚑ `Compress2` WAS non-inhabitable at deployed parameters — and the field is now DELETED (2026-07-25)

`Compress1CR` was not merely a hypothesis on a theorem: it was a **FIELD** of the `Compress2` structure
(`compress1CR`), so a deployed `Compress2` **value could not exist** — `List ℤ` is infinite, a BabyBear
squeeze is one bounded field element, pigeonhole. That was the `Compress8CR`-in-`Cap8Scheme` shape the
sweep named the priority, and the consequence was load-bearing:
`CommitmentBinding.compressInjective_of_compress2` is the route that discharges
`StateCommit.recStateCommit_binds`'s `compressInjective cmb` portal — advertised as *"the `StateCommit`
root-binding portal thereby stands on the permutation CR, NOT a separate assumption"* — and at BabyBear
that route stood on nothing, satisfied only by `Reference.refCompress2` (`compress1 = Encodable.encode`,
injective into ALL of `ℤ`). Toy witness satisfiable, real instantiation false: verbatim the FALSE
COMFORT `HashFloorHonesty`'s own header named.

**THE CUTOVER LANDED, so this file's §1a now reads differently.** The `compress1CR` field is DELETED;
`Compress2` carries the compression and nothing false about it;
`CommitmentBinding.deployedCompress2` is a real deployed-shaped INHABITANT; and
`compressInjective_of_compress2` keeps its name and conclusion under a PER-INSTANCE
`¬ Compress1Coll` side condition at the exact packed blocks (implied by the deleted field via
`compress1Coll_refutable_of_injective`, hence strictly stronger). The old
`compress2_uninhabitable_babyBear` is GONE — it projected the deleted field, and after the cure the
honest statement is not "no value exists" but `deployedCompress2_compress1_not_Compress1CR`: **the very
function the teeth refute now INHABITS the structure.** `compress1CR_field_uninhabitable_babyBear`
keeps the general falsifier alive for the next bundle that tries the same trick.

## ⚑ `BindingHashCR` is the ONE carrier in this cluster that is NOT false by pigeonhole — and that
   matters more than a fifth refutation would

The sweep lists all ~20 as one class ("FALSE-AS-NAMED at deployed parameters"). **That is not uniform, and
§4 proves the exception rather than assuming it.** `bindingHash : Tag → Bytes` is `crypto::binding_hash` =
SHA-256 of a 32-byte macaroon tail into a 32-byte caveat body: the domain is NOT larger than the range, so
the counting core **does not bite**, and injectivity is *consistent* (a permutation of a 32-byte set is
injective). §4 therefore proves the conditional teeth honestly — FALSE exactly when `bindingHash`
compresses (`bindingHashCR_false_of_compressing`, `bindingHashCR_false_of_infinite_tag`) — and NOT a
deployed refutation, because there is none to prove and manufacturing one would be the disease.

The defect at `BindingHashCR` is the OTHER one, and it is still real: injectivity is an
adversary-independent statement about EXISTENCE, while what `binding_not_replayable_to_other_root` and
`rebinding_changes_replay` actually need is that an attacker cannot FIND a colliding tail. And the Lean
carrier quantifies over a GENERIC `Tag`: at any instantiation where the tail type is unbounded — which is
how this model treats tags, `MacKernel.mac` mapping unbounded `Bytes` into `Tag` with nothing bounding it
— `bindingHashCR_false_of_infinite_tag` makes it FALSE. So it is re-grounded on the same terms as the
others (§4), with its verdict stated precisely instead of rounded up.

## The re-grounding does NOT go through the `⊤`-class floor

`FloorGames.hashCRHardQuant_top_false_of_compressing`: `HashCRHardQuant F (fun _ => True)` is ITSELF false
at deployed parameters — the `Classical.choice` finder is in the unrestricted class and wins with
probability `1`. At the unrestricted class every floor is false-at-deployed or vacuous, and
`hard_top_iff_solvableFrac_negl` is an `↔` — no restatement of the win relation escapes. **The only honest
escape is the `Eff` parameter** (`FloorGames` §8). Every keystone below takes it, and carries the
`Eff`-membership obligation for the finder its reduction builds, in the open, at the use site.

⚑ This used to be phrased against `HashFloorHonesty.CollisionResistant F`, a `def` that spelled the same
floor at `⊤` under a name that HID the class. It is DELETED (2026-07-28) and the class is written out
wherever it appears below — §4's `bindingHashFamily_CR_of_bindingHashCR` is the one statement in this
file that carries it, and it now says so on its face.

## The reductions (each with a canary that REDS if the reduction is deleted)

  * **§2 `nodeToCompress1Adv`** — a collision of the 2-to-1 node hash `h` becomes a collision of the
    single-permutation-call `compress1`, by the INJECTIVE packing: `pack₂ a b ≠ pack₂ c d` (contraposed
    `pack₂_inj`) while `compress1 (pack₂ a b) = h a b = h c d = compress1 (pack₂ c d)` (`factor`). This is
    `compressInjective_of_compress2`, contraposed into an extractor.
  * **§3 `forgerToFactoryHashAdv`** — a factory forger outputs two WELL-FORMED descriptors with equal
    `vk` and different content; well-formedness converts the `vk` equality into a hash equality, so the
    two contents are a genuine collision of `factoryHash`. This is `vk_determines_invariants`, contraposed.
  * **§4 `rebinderToBindingAdv`** — a re-binder outputs one discharge and two DISTINCT parent tails with
    the SAME replay; `hmacInj` peels the final MAC step, leaving `bindingHash p = bindingHash p'` — a
    genuine binding-hash collision. This is `rebinding_changes_replay`, contraposed.

## Non-fake

Both poles PROVED for every derived floor (`Eff := ⊤` FALSE at compressing parameters, `Eff := ⊥`
vacuous). Old injective-floor consumers KEPT untouched; siblings ADDED. `#assert_all_clean`; no `sorry`,
no fresh `axiom`.
-/
import Dregg2.Crypto.FloorGames
import Dregg2.Crypto.CommitmentBinding
import Dregg2.Authority.MacaroonDischarge
import Dregg2.Exec.Factory
import Dregg2.Crypto.RomCarrierSites

namespace Dregg2.Crypto.FactoryBindingFloorRegrounded

open Dregg2.Crypto.ConcreteSecurity (Negl)
open Dregg2.Crypto.ProbCrypto (winProb negl_of_le)
open Dregg2.Circuit.HashFloorHonesty
  (KeyedHashFamily not_injective_of_finite_range)
open Dregg2.Crypto.FloorGames
  (Game Adversary gameAdv gameAdv_mem_unit Hard hard_bot_vacuous hashGame HashCRHardQuant
   not_hard_top_of_always_solvable hashCRHardQuant_top_of_injective)
open Dregg2.Crypto.CommitmentBinding (Compress1CR Compress2)
open Dregg2.Authority.MacaroonDischarge (BindingHashCR Discharge bindTo foldBytes)
open Dregg2.Authority.CaveatChain (MacKernel Key)
open Dregg2.Exec (Value Schema RecordProgram)
open Dregg2.Exec.Factory (FactoryVk factoryHash HashInjective FactoryDescriptor)

set_option autoImplicit false

/-! ## §1 — FALSIFIABILITY TEETH (the counting core, three carriers).

`HashFloorHonesty.not_injective_of_finite_range`: an injective map out of an INFINITE domain has an
INFINITE range; a real hash's range is a bounded field. Nobody had tried to prove these three false. -/

/-- A function into a bounded integer window has finite range. (`Circuit.StateCommitFloorRegrounded` has
the same helper for the leaf/log side; kept local so the two lanes stay independently importable.) -/
theorem finite_range_of_field_window {α : Type*} (f : α → ℤ) (q : ℤ)
    (hb : ∀ x, 0 ≤ f x ∧ f x < q) : (Set.range f).Finite := by
  refine (Set.finite_Ico (0 : ℤ) q).subset ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨(hb x).1, (hb x).2⟩

/-- A function into a bounded natural window has finite range (the factory `vk` is a `Nat`). -/
theorem finite_range_of_nat_window {α : Type*} (f : α → ℕ) (q : ℕ)
    (hb : ∀ x, f x < q) : (Set.range f).Finite := by
  refine (Set.finite_Iio q).subset ?_
  rintro _ ⟨x, rfl⟩
  exact hb x

/-! ### §1a — `Compress1CR` is FALSE, and `Compress2` is UNINHABITABLE, at BabyBear. -/

/-- **TOOTH — `Compress1CR` is FALSE for a range-bounded compression.** `List ℤ` is infinite; a single
permutation call squeezes it into one field element. Same predicate, same fate, as the already-flagged
`StateCommit.compressNInjective` / `Poseidon2Binding.Poseidon2SpongeCR`. -/
theorem compress1CR_false_of_finite_range (c1 : List ℤ → ℤ) (hfin : (Set.range c1).Finite) :
    ¬ Compress1CR c1 := fun hinj =>
  not_injective_of_finite_range c1 hfin (fun a b h => hinj a b h)

/-- **TOOTH (deployed form) — `Compress1CR` is FALSE at the REAL BabyBear parameters.** Every real
Poseidon2 `hash_2_to_1` squeeze lands in `[0, p)` with `p = 2³¹ − 2²⁷ + 1`. -/
theorem compress1CR_false_babyBear (c1 : List ℤ → ℤ)
    (hb : ∀ xs, 0 ≤ c1 xs ∧ c1 xs < (2013265921 : ℤ)) : ¬ Compress1CR c1 :=
  compress1CR_false_of_finite_range c1 (finite_range_of_field_window c1 _ hb)

/-- **⚑ THE REFUTATION TOOTH — the deployed `Compress2` inhabitant's own compression REFUTES the
deleted field.** This SUPERSEDES `compress2_uninhabitable_babyBear` (deleted in the 2026-07-25 bundle
cutover), which proved `Compress2 h → False` from the `compress1CR` FIELD. That theorem could not
survive its own finding: once the field is deleted the bundle is INHABITED, and the honest statement is
no longer "no value exists" but "the value that exists refutes what the field asserted".

`CommitmentBinding.deployedCompress2` is a real `Compress2` value whose `compress1` squeezes the
infinite `List ℤ` into ONE BabyBear felt — exactly the shape `compress1CR_false_babyBear` refutes. Had
the field survived, THIS value could not have been built and every `∀ R : Compress2 h, …` theorem
would still be vacuous. -/
theorem deployedCompress2_compress1_not_Compress1CR :
    ¬ Compress1CR Dregg2.Crypto.CommitmentBinding.deployedCompress2.compress1 :=
  compress1CR_false_babyBear _
    Dregg2.Crypto.CommitmentBinding.deployedShapedCompress1_bounded

/-- **The general form, kept as the falsifier for any not-yet-cut-over bundle in this shape**: a
`Compress2`-like structure that still carries a BabyBear-range-bounded `Compress1CR` FIELD is
uninhabitable. Stated over the field's TYPE rather than a projection, so it stays provable after the
`Compress2` cutover and still bites the next bundle that tries the same trick.

⚑ SPELLED AS A REFUTATION (`¬ Compress1CR c1`), not as `… → Compress1CR c1 → False`. The two are
definitionally equal and every application site is unchanged, but only the first is READABLE as
anti-floor content, and `Verify.FloorRatchet.antiFloor` now requires it: keying the exemption on
where the floor binder sat let `HermineMSIS.no_forgery_under_msis` — a signature-unforgeability
claim on a refuted floor — out of the census entirely (the B4 hole). -/
theorem compress1CR_field_uninhabitable_babyBear (c1 : List ℤ → ℤ)
    (hb : ∀ xs, 0 ≤ c1 xs ∧ c1 xs < (2013265921 : ℤ)) : ¬ Compress1CR c1 :=
  compress1CR_false_babyBear c1 hb

/-! ### §1b — the factory content-hash `HashInjective` is FALSE at BLAKE3's output width. -/

/-- `Schema` is INFINITE (`List (FieldName × Ty)` over an inhabited pair). -/
instance : Infinite Schema :=
  Infinite.of_injective (fun n : ℕ => List.replicate n (("", Dregg2.Exec.Ty.scalar)))
    (fun n m h => by have := congrArg List.length h; simpa using this)

/-- `Schema × RecordProgram` is INFINITE — the published content a factory content-addresses is unbounded
data. This is what makes the content-address floor false: BLAKE3 pins it into 256 bits. -/
instance : Infinite (Schema × RecordProgram) :=
  Infinite.of_injective (fun s : Schema => (s, RecordProgram.none))
    (fun _ _ h => congrArg Prod.fst h)

/-- **TOOTH — `HashInjective` is FALSE for a range-bounded content hash.** The published content
`(schema, program)` is infinite; a content address is a fixed-width digest. So two distinct contracts
share a `vk` by pigeonhole, and the floor claims none do. -/
theorem hashInjective_false_of_finite_range
    (hfin : (Set.range (fun q : Schema × RecordProgram => factoryHash q.1 q.2)).Finite) :
    ¬ HashInjective := by
  intro hinj
  refine not_injective_of_finite_range (fun q : Schema × RecordProgram => factoryHash q.1 q.2) hfin ?_
  rintro ⟨s₁, p₁⟩ ⟨s₂, p₂⟩ heq
  obtain ⟨hs, hp⟩ := hinj s₁ s₂ p₁ p₂ heq
  simp [hs, hp]

/-- **TOOTH (deployed form) — `HashInjective` is FALSE at BLAKE3's REAL output width.**
`STORAGE-AS-CELL-PROGRAMS.md §2` pins `factory_vk` = *"BLAKE3 of the descriptor"* — a 256-bit digest. A
`factoryHash` bounded by `2²⁵⁶` cannot inject the infinite published-content space, so
`Exec.Factory.vk_determines_invariants` / `vk_determines_program` — the formal content of CONSTRUCTOR
TRANSPARENCY, *"reading the `vk` tells you the cell's whole life"* — are VACUOUSLY TRUE at deployed
parameters. -/
theorem hashInjective_false_blake3
    (hb : ∀ (s : Schema) (p : RecordProgram), factoryHash s p < 2 ^ 256) : ¬ HashInjective :=
  hashInjective_false_of_finite_range
    (finite_range_of_nat_window (fun q : Schema × RecordProgram => factoryHash q.1 q.2) (2 ^ 256)
      (fun q => hb q.1 q.2))

/-! ### §1c — ⚑ `BindingHashCR`: the conditional teeth, and the HONEST non-verdict.

Unlike every other carrier in this cluster, `BindingHashCR` is **NOT refuted at deployed parameters**, and
the sweep's blanket "FALSE-AS-NAMED at deployed parameters" is wrong about it. `crypto::binding_hash` is
SHA-256 of a 32-byte macaroon tail producing a 32-byte caveat body: `|Tag| = |Bytes| = 2²⁵⁶`, the map does
NOT compress, and pigeonhole has nothing to say. Injectivity there is *consistent* — unprovable and
unfalsifiable, but not false.

So the teeth below are stated at their REAL scope: the carrier is false exactly when the binding hash
compresses, or when the tail type is unbounded (which is how this model treats `Tag` — nothing in
`MacaroonDischarge` bounds it, and `MacKernel.mac` maps unbounded `Bytes` into it). Proving a refutation
here would require manufacturing a hypothesis the deployment does not satisfy; the discipline is to say so.
The defect that IS present — injectivity is adversary-independent EXISTENCE where the consumer needs
computational FINDING — is what §4 repairs. -/

/-- **TOOTH — `BindingHashCR` is FALSE exactly when the binding hash COMPRESSES.** If the tail space is
larger than the caveat-body space, pigeonhole pins two distinct tails to one binding body. ⚑ At the
DEPLOYED SHA-256 instantiation (32-byte tail → 32-byte body) this hypothesis is NOT satisfied, so this
tooth does not fire there — recorded honestly rather than rounded up to a refutation. -/
theorem bindingHashCR_false_of_compressing {Tag Bytes : Type} [Fintype Tag] [Fintype Bytes]
    (bh : Tag → Bytes) (hcard : Fintype.card Bytes < Fintype.card Tag) : ¬ BindingHashCR bh := by
  obtain ⟨a, b, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt bh hcard
  exact fun hCR => hne (hCR a b heq)

/-- **TOOTH — `BindingHashCR` is FALSE for an UNBOUNDED tail type with a fixed-width body.** This IS the
Lean model's own situation: `MacaroonDischarge` quantifies over a GENERIC `Tag` with nothing bounding it,
and `MacKernel.mac : Key → Bytes → Tag` produces tags from unbounded messages. At any such instantiation
with a finite-range binding hash the carrier is false — so the generic consumers
(`binding_body_distinguishes_roots`, `rebinding_changes_replay`) are vacuous there, even though the
32-byte-tail reading escapes. -/
theorem bindingHashCR_false_of_infinite_tag {Tag Bytes : Type} [Infinite Tag] (bh : Tag → Bytes)
    (hfin : (Set.range bh).Finite) : ¬ BindingHashCR bh := fun hinj =>
  not_injective_of_finite_range bh hfin (fun a b h => hinj a b h)

/-! ## §2 — `Compress1CR` RE-GROUNDED: the node-hash collision REDUCES to a `compress1` collision.

`CommitmentBinding.compressInjective_of_compress2` proves `compressInjective h` from a `Compress2 h` by
peeling the one-permutation-call CR then the injective packing. CONTRAPOSED, that peel is an EXTRACTOR:
a collision of the 2-to-1 node hash IS a collision of the single permutation call. -/

/-- **THE 2-TO-1 REALIZATION FAMILY.** At each parameter `l` a finite sampled instance space, and per
instance the deployed `Compress2` data: the node hash `h`, the single-permutation compression `compress1`,
the rate-block packing `pack₂`, its STRUCTURAL injectivity, and the factorization `h = compress1 ∘ pack₂`.
Everything except the crypto carrier — which is exactly the point: `Compress1CR` is GONE from the bundle
(that is what made `Compress2` uninhabitable, §1a), and the collision floor enters at the use site. -/
structure Compress2Family where
  /-- The instance space (domain-separation / permutation-parameter sampling). -/
  Inst : ℕ → Type
  /-- The instance space is finite. -/
  instFin : ∀ l, Fintype (Inst l)
  /-- The instance space is inhabited. -/
  instNe : ∀ l, Nonempty (Inst l)
  /-- The 2-to-1 node hash at parameter `l`, instance `i` (`hash_2_to_1`, `poseidon2.rs:357`). -/
  h : ∀ l, Inst l → ℤ → ℤ → ℤ
  /-- The single-permutation-call compression it squeezes through. -/
  compress1 : ∀ l, Inst l → List ℤ → ℤ
  /-- The rate-block packing (`state[0]=a; state[1]=b`). -/
  pack₂ : ∀ l, Inst l → ℤ → ℤ → List ℤ
  /-- STRUCTURAL (not crypto): the packing is injective. -/
  pack₂_inj : ∀ l (i : Inst l) (a b c d : ℤ), pack₂ l i a b = pack₂ l i c d → a = c ∧ b = d
  /-- The node hash factors as `compress1 ∘ pack₂` — ONE permutation call over the packed block. -/
  factor : ∀ l (i : Inst l) (a b : ℤ), h l i a b = compress1 l i (pack₂ l i a b)

/-- The NODE hash as a keyed family — the game whose break the consumer's binding portal forbids. -/
def c2NodeFamily (F : Compress2Family) : KeyedHashFamily where
  Key := F.Inst
  Input := ℤ × ℤ
  Out := ℤ
  H := fun l i p => F.h l i p.1 p.2
  keyFintype := F.instFin
  keyNonempty := F.instNe
  inputDecEq := inferInstance
  outDecEq := inferInstance

/-- The single-permutation-call COMPRESSION as a keyed family — where the honest floor lives (primitive
#4, the SAME one permutation call as the sponge). Keys are the SAME sampled instances, so the reduction's
advantage inequality is over ONE `Ω`. -/
def c2Compress1Family (F : Compress2Family) : KeyedHashFamily where
  Key := F.Inst
  Input := List ℤ
  Out := ℤ
  H := F.compress1
  keyFintype := F.instFin
  keyNonempty := F.instNe
  inputDecEq := inferInstance
  outDecEq := inferInstance

/-- **THE PROBLEM IS IN THE STATEMENT** — the node game's win relation is a genuine collision of the real
2-to-1 hash, i.e. exactly the event `StateCommit.compressInjective` declared impossible. -/
theorem c2NodeGame_wins_iff (F : Compress2Family) (l : ℕ) (i : F.Inst l) (p : (ℤ × ℤ) × (ℤ × ℤ)) :
    (hashGame (c2NodeFamily F)).wins l i p ↔
      (p.1 ≠ p.2 ∧ F.h l i p.1.1 p.1.2 = F.h l i p.2.1 p.2.2) :=
  Iff.rfl

/-- **THE REDUCTION, AS A MAP OF ADVERSARIES.** A node-hash collision finder becomes a `compress1`
collision finder by PACKING its two input pairs into rate blocks. This is not a re-indexing and not a
rename — it is `compressInjective_of_compress2`'s peel, written as a function into the compression's
collision game. -/
def nodeToCompress1Adv (F : Compress2Family) (A : Adversary (hashGame (c2NodeFamily F))) :
    Adversary (hashGame (c2Compress1Family F)) where
  run := fun l i =>
    let p := A.run l i
    (F.pack₂ l i p.1.1 p.1.2, F.pack₂ l i p.2.1 p.2.2)

/-- **⚑ THE REDUCTION IS WIN-PRESERVING — and this IS `compressInjective_of_compress2`, contraposed.**
Every node collision the finder produces, the packed blocks are a genuine `compress1` collision: they are
DISTINCT (contraposed `pack₂_inj` — equal blocks would force equal inputs) and they hash EQUAL (`factor`
on both sides of the node collision). The permutation-CR content lives in proof terms, not in a sentence
about them. -/
theorem c2_wins_imp (F : Compress2Family) (A : Adversary (hashGame (c2NodeFamily F))) (l : ℕ)
    (i : F.Inst l) (hwin : (hashGame (c2NodeFamily F)).wins l i (A.run l i)) :
    (hashGame (c2Compress1Family F)).wins l i ((nodeToCompress1Adv F A).run l i) := by
  obtain ⟨hne, heq⟩ := hwin
  constructor
  · -- DISTINCT blocks: equal blocks would force equal inputs, contradicting the node collision.
    intro hpk
    exact hne (by
      obtain ⟨h1, h2⟩ := F.pack₂_inj l i _ _ _ _ hpk
      exact Prod.ext h1 h2)
  · -- EQUAL squeezes: `factor` on both sides of the node collision.
    show F.compress1 l i (F.pack₂ l i (A.run l i).1.1 (A.run l i).1.2)
      = F.compress1 l i (F.pack₂ l i (A.run l i).2.1 (A.run l i).2.2)
    rw [← F.factor, ← F.factor]
    exact heq

/-- **THE ADVANTAGE INEQUALITY.** The node-collision finder's advantage is at most the packed `compress1`
finder's, at every parameter — both play over the SAME sampled instance space, and every instance the node
finder wins the derived one wins. A genuine reduction inequality over real game advantages. -/
theorem c2_adv_le (F : Compress2Family) (A : Adversary (hashGame (c2NodeFamily F))) (l : ℕ) :
    gameAdv (hashGame (c2NodeFamily F)) A l
      ≤ gameAdv (hashGame (c2Compress1Family F)) (nodeToCompress1Adv F A) l := by
  refine @Dregg2.Crypto.ProbCrypto.winProb_le_of_imp _ (F.instFin l) _ _ (fun i hi => ?_)
  replace hi := (Adversary.hit_eq_true _ _ _).mp hi
  refine (Adversary.hit_eq_true _ _ _).mpr ?_
  exact c2_wins_imp F A l i hi

/-- **⚑ RE-GROUNDED `CommitmentBinding.compressInjective_of_compress2` (and through it
`StateCommit.recStateCommit_binds`'s `compressInjective cmb` portal) — from COLLISION HARDNESS of the ONE
permutation call, VIA the reduction.**

Under the collision floor at the single-permutation compression — at a NAMED adversary class `Eff` — a
2-to-1 node-hash collision finder whose packed image lies in that class has NEGLIGIBLE advantage. The
Boolean "equal node hashes ⇒ equal inputs", which needed the FALSE `Compress1CR` inside an UNINHABITABLE
`Compress2` (§1a), becomes an honest advantage bound over the SAME single permutation call. No new crypto:
the sole content is still primitive #4, now stated as something an adversary must FIND.

⚑ `hEff` is UNDISCHARGED and that is the honest state (`FloorGames` §8) — priced by §5's both poles.
The DISCHARGED successor on the PROVED keyed-ROM floor is §6a's `compress2_node_binds_rom`. -/
theorem compress2_node_advantage_bound (F : Compress2Family)
    (Eff : Adversary (hashGame (c2Compress1Family F)) → Prop)
    (A : Adversary (hashGame (c2NodeFamily F)))
    (hEff : Eff (nodeToCompress1Adv F A))
    (hC1 : HashCRHardQuant (c2Compress1Family F) Eff) :
    Negl (gameAdv (hashGame (c2NodeFamily F)) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (hashGame (c2NodeFamily F)) A l).1)
    (c2_adv_le F A) (hC1 _ hEff)

/-- **(CANARY — the node bound does NOT follow from the floor applied at ANOTHER finder.)** Strip the
reduction — try to conclude the node finder's negligibility from the `compress1` floor at some OTHER
finder `B`, NOT the one packed from it — and the proof does not go through: the floor bounds `B`, and only
`c2_adv_le` connects the PACKED finder to the node game. This tooth was unwritable under the old free
`Compress1CR` hypothesis (it and the conclusion shared no object to disconnect); it compiles now, and REDS
if a future edit reconnects the games. -/
example (F : Compress2Family) (Eff : Adversary (hashGame (c2Compress1Family F)) → Prop)
    (A : Adversary (hashGame (c2NodeFamily F)))
    (B : Adversary (hashGame (c2Compress1Family F))) (hB : Eff B)
    (hC1 : HashCRHardQuant (c2Compress1Family F) Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (hashGame (c2NodeFamily F)) A) := hC1 B hB)
  trivial

/-! ## §3 — the factory content-address `HashInjective` RE-GROUNDED.

`Exec.Factory.vk_determines_invariants` says two WELL-FORMED descriptors with equal `vk` published the
same `(schema, program)` — the formal content of CONSTRUCTOR TRANSPARENCY. Its BREAK is a factory forger:
two well-formed descriptors, equal `vk`, DIFFERENT content. Well-formedness is what turns the `vk`
equality into a HASH equality — which is why the reduction below is a reduction and not a rename. -/

/-- **THE CONTENT-HASH FAMILY.** Inputs are published contents `(schema, program)`, outputs `FactoryVk`
digests, the keyed hash the deployed `factoryHash` (BLAKE3 of the descriptor). -/
noncomputable def factoryHashFamily (Inst : ℕ → Type) (instFin : ∀ l, Fintype (Inst l))
    (instNe : ∀ l, Nonempty (Inst l)) : KeyedHashFamily where
  Key := Inst
  Input := Schema × RecordProgram
  Out := FactoryVk
  H := fun _ _ q => factoryHash q.1 q.2
  keyFintype := instFin
  keyNonempty := instNe
  -- `RecordProgram` carries `StateConstraint`s and has no in-tree `DecidableEq`; the game only ever
  -- COUNTS this event, so classical decidability is the honest supply (no computable encoder exists
  -- here, unlike `Value`'s `encV` route in the commit-state lane).
  inputDecEq := Classical.decEq _
  outDecEq := inferInstance

/-- **THE FACTORY-FORGERY GAME.** The adversary WINS iff it outputs two WELL-FORMED factory descriptors
that share a `vk` but publish DIFFERENT contracts — i.e. a `vk` that does NOT determine the cell's
lifetime invariants. Winning this game is exactly breaking constructor transparency; the well-formedness
and the content difference are IN the win predicate, read off the real `FactoryDescriptor`. -/
noncomputable def factoryForgeryGame (Inst : ℕ → Type) (instFin : ∀ l, Fintype (Inst l))
    (instNe : ∀ l, Nonempty (Inst l)) : Game where
  Inst := Inst
  Ans := fun _ => FactoryDescriptor × FactoryDescriptor
  instFin := instFin
  instNe := instNe
  wins := fun _ _ p =>
    p.1.WellFormed ∧ p.2.WellFormed ∧ p.1.vk = p.2.vk ∧
      ¬ (p.1.schema = p.2.schema ∧ p.1.program = p.2.program)
  winsDec := fun _ _ _ => Classical.propDecidable _

/-- **THE PROBLEM IS IN THE STATEMENT** — the forgery game's win relation is exactly the negation of
`vk_determines_invariants`'s conclusion under its own hypotheses. -/
theorem factoryForgeryGame_wins_iff (Inst : ℕ → Type) (instFin : ∀ l, Fintype (Inst l))
    (instNe : ∀ l, Nonempty (Inst l)) (l : ℕ) (i : Inst l)
    (p : FactoryDescriptor × FactoryDescriptor) :
    (factoryForgeryGame Inst instFin instNe).wins l i p ↔
      (p.1.WellFormed ∧ p.2.WellFormed ∧ p.1.vk = p.2.vk ∧
        ¬ (p.1.schema = p.2.schema ∧ p.1.program = p.2.program)) :=
  Iff.rfl

/-- **THE REDUCTION, AS A MAP OF ADVERSARIES.** A factory forger becomes a content-hash collision finder
by handing back its two descriptors' PUBLISHED CONTENTS. -/
noncomputable def forgerToFactoryHashAdv (Inst : ℕ → Type) (instFin : ∀ l, Fintype (Inst l))
    (instNe : ∀ l, Nonempty (Inst l)) (A : Adversary (factoryForgeryGame Inst instFin instNe)) :
    Adversary (hashGame (factoryHashFamily Inst instFin instNe)) where
  run := fun l i =>
    let p := A.run l i
    ((p.1.schema, p.1.program), (p.2.schema, p.2.program))

/-- **⚑ THE REDUCTION IS WIN-PRESERVING — and this IS `vk_determines_invariants`, contraposed.** Every
forgery, the two published contents are a genuine `factoryHash` collision: they are DISTINCT (the forger
published different contracts) and they hash EQUAL — because WELL-FORMEDNESS says each `vk` IS the hash of
its own content, so the shared `vk` becomes a shared digest. That step is the whole reduction; delete
well-formedness and it evaporates. -/
theorem factory_wins_imp (Inst : ℕ → Type) (instFin : ∀ l, Fintype (Inst l))
    (instNe : ∀ l, Nonempty (Inst l)) (A : Adversary (factoryForgeryGame Inst instFin instNe))
    (l : ℕ) (i : Inst l) (hwin : (factoryForgeryGame Inst instFin instNe).wins l i (A.run l i)) :
    (hashGame (factoryHashFamily Inst instFin instNe)).wins l i
      ((forgerToFactoryHashAdv Inst instFin instNe A).run l i) := by
  obtain ⟨hw₁, hw₂, hvk, hdiff⟩ := hwin
  refine ⟨?_, ?_⟩
  · -- DISTINCT contents: the forger published different contracts.
    intro hc
    exact hdiff ⟨congrArg Prod.fst hc, congrArg Prod.snd hc⟩
  · -- EQUAL digests: well-formedness turns the shared `vk` into a shared hash.
    show factoryHash (A.run l i).1.schema (A.run l i).1.program
      = factoryHash (A.run l i).2.schema (A.run l i).2.program
    unfold FactoryDescriptor.WellFormed at hw₁ hw₂
    rw [← hw₁, ← hw₂]
    exact hvk

/-- **THE ADVANTAGE INEQUALITY.** The forger's advantage is at most the extracted content-hash finder's,
at every parameter — over the SAME sampled instance space. -/
theorem factory_adv_le (Inst : ℕ → Type) (instFin : ∀ l, Fintype (Inst l))
    (instNe : ∀ l, Nonempty (Inst l)) (A : Adversary (factoryForgeryGame Inst instFin instNe))
    (l : ℕ) :
    gameAdv (factoryForgeryGame Inst instFin instNe) A l
      ≤ gameAdv (hashGame (factoryHashFamily Inst instFin instNe))
          (forgerToFactoryHashAdv Inst instFin instNe A) l := by
  refine @Dregg2.Crypto.ProbCrypto.winProb_le_of_imp _ (instFin l) _ _ (fun i hi => ?_)
  replace hi := (Adversary.hit_eq_true _ _ _).mp hi
  refine (Adversary.hit_eq_true _ _ _).mpr ?_
  exact factory_wins_imp Inst instFin instNe A l i hi

/-- **⚑ RE-GROUNDED `Exec.Factory.vk_determines_invariants` / `vk_determines_program` — from COLLISION
HARDNESS of the content hash, VIA the reduction.**

Under the collision floor at the `factoryHash` family, at a NAMED `Eff` class, a factory forger has
NEGLIGIBLE advantage: the published `vk` determines the cell's whole field layout and lifetime invariant
set EXCEPT with negligible probability. Constructor transparency — *"anyone with the `factory_vk` knows
exactly what invariants the cell will carry"* — survives the loss of the FALSE `HashInjective` (§1b) as an
honest concrete-security statement about BLAKE3, which is what `Factory.lean`'s own §8 note always said it
was (*"collision-resistance of BLAKE3, discharged by the hash circuit"*) — it just carried injectivity
instead.

⚑ `hEff` is UNDISCHARGED and that is the honest state (`FloorGames` §8). The DISCHARGED successor on
the PROVED keyed-ROM floor is §6b's `vk_determines_invariants_binds_rom`. -/
theorem vk_determines_invariants_advantage_bound (Inst : ℕ → Type) (instFin : ∀ l, Fintype (Inst l))
    (instNe : ∀ l, Nonempty (Inst l))
    (Eff : Adversary (hashGame (factoryHashFamily Inst instFin instNe)) → Prop)
    (A : Adversary (factoryForgeryGame Inst instFin instNe))
    (hEff : Eff (forgerToFactoryHashAdv Inst instFin instNe A))
    (hCR : HashCRHardQuant (factoryHashFamily Inst instFin instNe) Eff) :
    Negl (gameAdv (factoryForgeryGame Inst instFin instNe) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (factoryForgeryGame Inst instFin instNe) A l).1)
    (factory_adv_le Inst instFin instNe A) (hCR _ hEff)

/-- **(CANARY — the factory bound does NOT follow from the floor at ANOTHER finder.)** The floor bounds
`B`; only `factory_adv_le` connects the EXTRACTED finder to the forgery game. Unwritable under the old
free `HashInjective` hypothesis. -/
example (Inst : ℕ → Type) (instFin : ∀ l, Fintype (Inst l)) (instNe : ∀ l, Nonempty (Inst l))
    (Eff : Adversary (hashGame (factoryHashFamily Inst instFin instNe)) → Prop)
    (A : Adversary (factoryForgeryGame Inst instFin instNe))
    (B : Adversary (hashGame (factoryHashFamily Inst instFin instNe))) (hB : Eff B)
    (hCR : HashCRHardQuant (factoryHashFamily Inst instFin instNe) Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (factoryForgeryGame Inst instFin instNe) A) := hCR B hB)
  trivial

/-! ## §4 — the macaroon `BindingHashCR` RE-GROUNDED (existence → finding).

`MacaroonDischarge.rebinding_changes_replay` says: re-binding a discharge to a DIFFERENT parent changes
its replay tail, so you cannot silently swap the bound parent and keep the stored tail. It consumes
`BindingHashCR` (via `binding_body_distinguishes_roots`) plus the local `hmacInj` premise. Its BREAK is a
RE-BINDER: one discharge, two DISTINCT parent tails, ONE replay. `hmacInj` peels the final MAC step off
that break, leaving a genuine binding-hash collision — that peel is the reduction.

⚑ Per §1c this is the carrier that is NOT refuted at deployed parameters. The re-grounding still earns its
keep: it moves the consumer from adversary-independent EXISTENCE (which SHA-256-on-32-bytes may well
satisfy, unprovably) to computational FINDING (which is what "collision-resistance" has always meant, and
what `MacaroonDischarge`'s own §PORTAL note claims it is carrying). -/

/-- **THE MACAROON BINDING FAMILY.** At each parameter a finite sampled instance space, the tail/body
types, their decidable equality, the `MacKernel` the discharge chain runs on, and per instance the
deployed `bindingHash` (`crypto::binding_hash`, SHA-256 of a root tail). -/
structure BindingFamily where
  /-- The instance space (domain-separation sampling). -/
  Inst : ℕ → Type
  /-- The instance space is finite. -/
  instFin : ∀ l, Fintype (Inst l)
  /-- The instance space is inhabited. -/
  instNe : ∀ l, Nonempty (Inst l)
  /-- The macaroon tail type. -/
  Tag : Type
  /-- The caveat-body / message type. -/
  Bytes : Type
  /-- Decidable equality on tails (`verify_discharge`'s constant-time compare). -/
  tagDec : DecidableEq Tag
  /-- Decidable equality on caveat bodies (the collision game checks the bodies agree). -/
  bytesDec : DecidableEq Bytes
  /-- The keyed-hash portal the discharge chain runs on (`CaveatChain.MacKernel`, REUSED not re-derived). -/
  macK : letI := tagDec; MacKernel (Key Tag) Bytes Tag
  /-- The binding hash at parameter `l`, instance `i` (`crypto::binding_hash`). -/
  bindingHash : ∀ l, Inst l → Tag → Bytes

/-- The binding hash as a keyed family — the collision game the honest floor lives over. -/
def bindingHashFamily (F : BindingFamily) : KeyedHashFamily where
  Key := F.Inst
  Input := F.Tag
  Out := F.Bytes
  H := F.bindingHash
  keyFintype := F.instFin
  keyNonempty := F.instNe
  inputDecEq := F.tagDec
  outDecEq := F.bytesDec

/-- **THE RE-BINDING GAME.** The adversary is handed a sampled binding surface and WINS iff it outputs one
discharge and two DISTINCT parent tails whose `bindTo` replays COINCIDE — i.e. a discharge that can be
silently re-pointed at a different (less-attenuated) root while keeping its stored tail. Winning this game
is exactly the cross-root replay `bind_discharge` exists to stop; the real `Discharge.replay` and `bindTo`
are IN the win predicate. -/
noncomputable def rebindGame (F : BindingFamily) : Game where
  Inst := F.Inst
  Ans := fun _ => Discharge (Key F.Tag) F.Bytes F.Tag × F.Tag × F.Tag
  instFin := F.instFin
  instNe := F.instNe
  wins := fun l i a =>
    letI := F.tagDec; letI := F.macK
    a.2.1 ≠ a.2.2 ∧
      Discharge.replay (F.bindingHash l i) (bindTo a.1 a.2.1)
        = Discharge.replay (F.bindingHash l i) (bindTo a.1 a.2.2)
  winsDec := fun _ _ _ => Classical.propDecidable _

/-- **THE REDUCTION, AS A MAP OF ADVERSARIES.** A re-binder becomes a binding-hash collision finder by
handing back its two parent tails. -/
noncomputable def rebinderToBindingAdv (F : BindingFamily) (A : Adversary (rebindGame F)) :
    Adversary (hashGame (bindingHashFamily F)) where
  run := fun l i => let a := A.run l i; (a.2.1, a.2.2)

/-- **⚑ THE REDUCTION IS WIN-PRESERVING — and this IS `rebinding_changes_replay`, contraposed.** Given the
`hmacInj` premise the deployed theorem already carries (the MAC is injective in its message at a fixed
base tag — the collision-freedom EUF-CMA gives on a fixed key/prefix), every re-binding break yields a
genuine binding-hash collision: both replays reduce to `mac base (bindingHash p)` versus
`mac base (bindingHash p')`, so `hmacInj` peels the final step and leaves `bindingHash p = bindingHash p'`
at DISTINCT tails `p ≠ p'`. -/
theorem rebind_wins_imp (F : BindingFamily) (A : Adversary (rebindGame F))
    (hmacInj : letI := F.tagDec; letI := F.macK;
      ∀ (base : F.Tag) (x y : F.Bytes), (MacKernel.mac base x : F.Tag) = MacKernel.mac base y → x = y)
    (l : ℕ) (i : F.Inst l) (hwin : (rebindGame F).wins l i (A.run l i)) :
    (hashGame (bindingHashFamily F)).wins l i ((rebinderToBindingAdv F A).run l i) := by
  letI := F.tagDec; letI := F.macK
  obtain ⟨hne, heq⟩ := hwin
  refine ⟨hne, ?_⟩
  -- both replays unfold to `mac base (bindingHash · )`; `hmacInj` peels the final MAC step.
  unfold Discharge.replay bindTo at heq
  simp only at heq
  exact hmacInj _ _ _ heq

/-- **THE ADVANTAGE INEQUALITY.** The re-binder's advantage is at most the extracted binding-collision
finder's, at every parameter — over the SAME sampled instance space. -/
theorem rebind_adv_le (F : BindingFamily) (A : Adversary (rebindGame F))
    (hmacInj : letI := F.tagDec; letI := F.macK;
      ∀ (base : F.Tag) (x y : F.Bytes), (MacKernel.mac base x : F.Tag) = MacKernel.mac base y → x = y)
    (l : ℕ) :
    gameAdv (rebindGame F) A l
      ≤ gameAdv (hashGame (bindingHashFamily F)) (rebinderToBindingAdv F A) l := by
  refine @Dregg2.Crypto.ProbCrypto.winProb_le_of_imp _ (F.instFin l) _ _ (fun i hi => ?_)
  replace hi := (Adversary.hit_eq_true _ _ _).mp hi
  refine (Adversary.hit_eq_true _ _ _).mpr ?_
  exact rebind_wins_imp F A hmacInj l i hi

/-- **⚑ RE-GROUNDED `MacaroonDischarge.rebinding_changes_replay` / `binding_body_distinguishes_roots` —
from COLLISION HARDNESS of the binding hash, VIA the reduction.**

Under the collision floor at the binding-hash family, at a NAMED `Eff` class, a re-binder has NEGLIGIBLE
advantage: a discharge issued for a heavily-attenuated root cannot be re-pointed at a less-attenuated one,
EXCEPT with negligible probability. This is the property that defeats "strip caveats off the root, reuse
the old discharge" (`macaroon.rs:324-329`), now stated as something an attacker must FIND rather than as
injectivity of SHA-256.

⚑ **`hEff` is UNDISCHARGED, and `hmacInj` is the deployed theorem's own carried premise** — neither is
new debt; both are named. §5 prices the floor's poles. The DISCHARGED successor on the PROVED
keyed-ROM floor is §6c's `rebinding_binds_rom`. -/
theorem rebinding_advantage_bound (F : BindingFamily)
    (Eff : Adversary (hashGame (bindingHashFamily F)) → Prop)
    (A : Adversary (rebindGame F))
    (hmacInj : letI := F.tagDec; letI := F.macK;
      ∀ (base : F.Tag) (x y : F.Bytes), (MacKernel.mac base x : F.Tag) = MacKernel.mac base y → x = y)
    (hEff : Eff (rebinderToBindingAdv F A))
    (hCR : HashCRHardQuant (bindingHashFamily F) Eff) :
    Negl (gameAdv (rebindGame F) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (rebindGame F) A l).1)
    (rebind_adv_le F A hmacInj) (hCR _ hEff)

/-- **(CANARY — the rebinding bound does NOT follow from the floor at ANOTHER finder.)** The floor bounds
`B`; only `rebind_adv_le` connects the EXTRACTED finder to the rebinding game. -/
example (F : BindingFamily) (Eff : Adversary (hashGame (bindingHashFamily F)) → Prop)
    (A : Adversary (rebindGame F))
    (B : Adversary (hashGame (bindingHashFamily F))) (hB : Eff B)
    (hCR : HashCRHardQuant (bindingHashFamily F) Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (rebindGame F) A) := hCR B hB)
  trivial

/-- **`BindingHashCR` ⟹ the binding collision floor at the UNRESTRICTED class.** A valid bridge (unlike
the leaf carrier's — see `Circuit.StateCommitFloorRegrounded` §8): `BindingHashCR` is full injectivity, so
it forbids every collision and every adversary's advantage is `0`. ⚑ But — and this is §1c's whole point —
the companion refutation that would make this "strictly stronger AND empty" is NOT available at deployed
parameters here. So this bridge says only that the old carrier was strictly stronger than needed; whether
it was EMPTY depends on an instantiation the model never pins.

⚑ **`fun _ => True` is WRITTEN OUT in the conclusion.** It used to read
`CollisionResistant (bindingHashFamily F)`; that `def` was a spelling of exactly this and is DELETED,
because the adversary class is what prices a floor and it does not belong hidden inside a name. Here the
price is the unusual one recorded in §1c: the `⊤` class is refuted at every COMPRESSING family
(`binding_floor_top_false_of_compressing`), and the deployed 32-byte-tail → 32-byte-body SHA-256 is not
known to compress — so unlike its siblings this conclusion is not known to be false, and is not claimed
to be true either. -/
theorem bindingHashFamily_CR_of_bindingHashCR (F : BindingFamily)
    (hinj : ∀ l (i : F.Inst l), BindingHashCR (F.bindingHash l i)) :
    HashCRHardQuant (bindingHashFamily F) (fun _ => True) :=
  hashCRHardQuant_top_of_injective (bindingHashFamily F) (fun l i a b h => hinj l i a b h)

/-! ## §5 — the derived floors, priced honestly (both poles PROVED for each).

`FloorGames` §8's residual is that the tree has no cost model, so `Eff` cannot be given honest content
here. What CAN be proved is the price of both extremes — which is what makes the `hEff` parameters an
honest name for "the reduction is efficient" rather than a decoration. -/

/-- **(TOOTH — the `compress1` floor is SATISFIABLE, vacuously.)** Recorded honestly; worth nothing on its
own — `hard_bot_vacuous` is exactly the statement that this satisfiability is vacuous. -/
theorem c1_floor_satisfiable_vacuously (F : Compress2Family) :
    HashCRHardQuant (c2Compress1Family F) (fun _ => False) :=
  hard_bot_vacuous _

/-- **(TOOTH — the `compress1` floor is FALSE at the unrestricted class, when the compression is
compressing.)** The price of `hEff`, as a theorem: §1a proves pigeonhole FORCES such a collision at
BabyBear, so at `Eff := fun _ => True` the floor is FALSE — which is why this file's keystones take an
explicit `Eff` and do NOT route through the unrestricted class. (That class used to be reachable under
the name `HashFloorHonesty.CollisionResistant`; the `def` is deleted and the class is written out.) -/
theorem c1_floor_top_false_of_compressing (F : Compress2Family)
    (hcol : ∀ l (i : F.Inst l), ∃ xs ys : List ℤ, xs ≠ ys ∧ F.compress1 l i xs = F.compress1 l i ys) :
    ¬ HashCRHardQuant (c2Compress1Family F) (fun _ => True) := by
  refine not_hard_top_of_always_solvable (hashGame (c2Compress1Family F)) (fun _ => ⟨([], [])⟩) ?_
  intro l i
  obtain ⟨xs, ys, hne, heq⟩ := hcol l i
  exact ⟨(xs, ys), hne, heq⟩

/-- **(TOOTH — the factory content-hash floor is SATISFIABLE, vacuously.)** -/
theorem factory_floor_satisfiable_vacuously (Inst : ℕ → Type) (instFin : ∀ l, Fintype (Inst l))
    (instNe : ∀ l, Nonempty (Inst l)) :
    HashCRHardQuant (factoryHashFamily Inst instFin instNe) (fun _ => False) :=
  hard_bot_vacuous _

/-- **(TOOTH — the factory content-hash floor is FALSE at the unrestricted class, when the content hash is
compressing.)** §1b proves BLAKE3's 256-bit width forces such a collision. -/
theorem factory_floor_top_false_of_compressing (Inst : ℕ → Type) (instFin : ∀ l, Fintype (Inst l))
    (instNe : ∀ l, Nonempty (Inst l))
    (hcol : ∃ q r : Schema × RecordProgram, q ≠ r ∧ factoryHash q.1 q.2 = factoryHash r.1 r.2) :
    ¬ HashCRHardQuant (factoryHashFamily Inst instFin instNe) (fun _ => True) := by
  obtain ⟨q, r, hne, heq⟩ := hcol
  refine not_hard_top_of_always_solvable (hashGame (factoryHashFamily Inst instFin instNe))
    (fun _ => ⟨(q, r)⟩) ?_
  intro l i
  exact ⟨(q, r), hne, heq⟩

/-- **(TOOTH — the binding floor is SATISFIABLE, vacuously.)** -/
theorem binding_floor_satisfiable_vacuously (F : BindingFamily) :
    HashCRHardQuant (bindingHashFamily F) (fun _ => False) :=
  hard_bot_vacuous _

/-- **(TOOTH — the binding floor is FALSE at the unrestricted class, when the binding hash is
compressing.)** ⚑ Stated CONDITIONALLY and that is the honest state: §1c proves the deployed SHA-256
tail→body map does NOT compress, so — alone in this cluster — the hypothesis of this tooth is NOT known to
hold at deployed parameters. The floor is still the right SHAPE (finding, not existence); its `⊤` pole is
simply not refuted here. -/
theorem binding_floor_top_false_of_compressing (F : BindingFamily)
    (hin : Nonempty F.Tag)
    (hcol : ∀ l (i : F.Inst l), ∃ a b : F.Tag, a ≠ b ∧ F.bindingHash l i a = F.bindingHash l i b) :
    ¬ HashCRHardQuant (bindingHashFamily F) (fun _ => True) := by
  refine not_hard_top_of_always_solvable (hashGame (bindingHashFamily F))
    (fun _ => ⟨(hin.some, hin.some)⟩) ?_
  intro l i
  obtain ⟨a, b, hne, heq⟩ := hcol l i
  exact ⟨(a, b), hne, heq⟩

/-! ## §6 — ⚑ THE KEYED-ROM SUCCESSORS: all three bounds DISCHARGED on the PROVED floor.

§2-§4's `_advantage_bound` keystones are the honest fixed-hash statements; their
`HashCRHardQuant … Eff` hypotheses are PARAMETERS with no known non-vacuous instantiation (§5 prices
`⊤` FALSE at compressing parameters and `⊥` vacuous; there is no cost model). The DISCHARGED
successors move the floor where it is a THEOREM: the keyed random-oracle model
(`Crypto.KeyedRomFloor.keyedRom_hard`, the birthday bound), each forger an ORACLE PROGRAM with
QUERY-COUNTED cost, the oracle sampled AFTER the program is fixed (`Crypto.RomCarrierSites`, the
`Exec.SystemRootsBindingReduction` §7 pattern).

⚑ **THE MODELLING STEP, STATED (not smuggled)** — `RomCarrierSites`' header caveat, inherited at all
three sites: the sampled `H : Inst × Msg → Fin (2 ^ l)` replaces the fixed public function (a
deliberate labelled idealisation, NOT a derivation); the digest space is `λ`-growing where the
deployed digest is a FIXED-width felt/256-bit value; the message domains are the TRUNCATED deployed
shapes (an in-range BabyBear rate-block pair; a descriptor serialization of at most `m` bytes; the
32-byte macaroon tail). These families are keyed by the SITES' OWN λ-indexed sampled instance spaces
(`F.Inst`), so `flatFamily` (constant key) does not apply and `instRomFamily` below is its λ-indexed
sibling — same digest, same floor. -/

open Dregg2.Crypto.KeyedRomFloor (KeyedRomFamily)
open Dregg2.Crypto.RomBindingReduction
  (RomCarrier romCarrierGame RomCarrierEff romCarrierAdv romCarrier_binds
   romCarrier_choiceForger_excluded)
open Dregg2.Crypto.RomCarrierSites
  (taggedCarrier BVec bvecOfList bvecOfList_inj romOpenGame RomOpenEff romOpenAdv rom_open_binds
   constOpenComp constOpen_in_eff constOpen_gameAdv_pos constOpen_binds romOpen_forger_excluded
   constTripleComp constTriple_in_eff constTriple_gameAdv_pos constTriple_binds babyBearP
   babyBearP_pos one_lt_babyBearP)
open Dregg2.Crypto.ConcreteSecurity (PolyBounded)

/-- **A KEYED ROM FAMILY OVER A λ-INDEXED INSTANCE SPACE** — `RomCarrierSites.flatFamily` with the
key space the site's own sampled `Inst : ℕ → Type` instead of a constant tag type. The digest space
stays the ideal `Fin (2 ^ l)`, so the floor's width obligation closes by computation
(`instRomFamily_card_R`). -/
def instRomFamily (Inst : ℕ → Type) (instFin : ∀ l, Fintype (Inst l))
    (instDec : ∀ l, DecidableEq (Inst l)) (instNe : ∀ l, Nonempty (Inst l))
    (Msg : ℕ → Type) (mF : ∀ l, Fintype (Msg l)) (mD : ∀ l, DecidableEq (Msg l))
    (mN : ∀ l, Nonempty (Msg l)) : KeyedRomFamily where
  Key := Inst
  D := Msg
  R := fun l => Fin (2 ^ l)
  keyFin := instFin
  keyDec := instDec
  keyNe := instNe
  dFin := mF
  dDec := mD
  dNe := mN
  rFin := fun _ => inferInstance
  rDec := fun _ => inferInstance
  rNe := fun _ => ⟨⟨0, by positivity⟩⟩

/-- The `hw` obligation, closed by construction — as `flatFamily_card_R`, at λ-indexed keys. -/
theorem instRomFamily_card_R (Inst : ℕ → Type) (instFin : ∀ l, Fintype (Inst l))
    (instDec : ∀ l, DecidableEq (Inst l)) (instNe : ∀ l, Nonempty (Inst l))
    (Msg : ℕ → Type) (mF : ∀ l, Fintype (Msg l)) (mD : ∀ l, DecidableEq (Msg l))
    (mN : ∀ l, Nonempty (Msg l)) (l : ℕ) :
    letI := (instRomFamily Inst instFin instDec instNe Msg mF mD mN).rFin l
    Fintype.card ((instRomFamily Inst instFin instDec instNe Msg mF mD mN).R l) = 2 ^ l := by
  show Fintype.card (Fin (2 ^ l)) = 2 ^ l
  simp

/-! ### §6a — the 2-to-1 node hash (`Compress1CR`'s consumer), at the sampled oracle. -/

/-- **THE NODE ROM FAMILY** — keyed by the deployed `Compress2Family`'s own sampled instance space,
over the truncated rate block: a pair of in-range BabyBear felts, the deployed `hash_2_to_1` input
shape. -/
def c2NodeRomFamily (F : Compress2Family) (instDec : ∀ l, DecidableEq (F.Inst l)) :
    KeyedRomFamily :=
  instRomFamily F.Inst F.instFin instDec F.instNe (fun _ => Fin babyBearP × Fin babyBearP)
    (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ => ⟨(⟨0, babyBearP_pos⟩, ⟨0, babyBearP_pos⟩)⟩)

/-- **THE NODE CARRIER** — commitment `H (i, (a, b))`: one oracle query at the packed pair (the
`pack₂` of §2, with the packing now the identity on the truncated pair — injective on the nose). -/
def c2NodeRomCarrier (F : Compress2Family) (instDec : ∀ l, DecidableEq (F.Inst l)) :
    RomCarrier (c2NodeRomFamily F instDec) :=
  taggedCarrier _ (fun _ => Unit) (fun _ => Fin babyBearP × Fin babyBearP)
    (fun _ => inferInstance) (fun _ _ v => v) (fun _ _ _ _ h => h)

/-- The node collision game at the sampled oracle. -/
abbrev c2NodeRomGame (F : Compress2Family) (instDec : ∀ l, DecidableEq (F.Inst l)) : Game :=
  romCarrierGame (c2NodeRomFamily F instDec) (c2NodeRomCarrier F instDec)

/-- **⚑ THE DEPLOYED NODE COLLISION IS A WIN OF THE ROM GAME.** Two DISTINCT in-range input pairs
with one sampled digest ARE a win — `c2NodeGame_wins_iff`'s event at the sampled oracle. -/
theorem c2NodeRom_collision_is_break (F : Compress2Family)
    (instDec : ∀ l, DecidableEq (F.Inst l)) (l : ℕ)
    (H : (c2NodeRomGame F instDec).Inst l) {p q : Fin babyBearP × Fin babyBearP}
    (hne : p ≠ q) (heq : ∀ i : F.Inst l, H (i, p) = H (i, q)) (i : F.Inst l) :
    (c2NodeRomGame F instDec).wins l H ((i, ()), p, q) :=
  ⟨hne, heq i⟩

/-- **⚑⚑ RE-GROUNDED `compress2_node_advantage_bound`, DISCHARGED ON THE PROVED FLOOR** — every
query-bounded node-collision forger has NEGLIGIBLE advantage, in the keyed ROM model of §6's header.
No `HashCRHardQuant` hypothesis; the floor is `keyedRom_hard`, a THEOREM. -/
theorem compress2_node_binds_rom (F : Compress2Family)
    (instDec : ∀ l, DecidableEq (F.Inst l)) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (c2NodeRomGame F instDec))
    (hA : RomCarrierEff (c2NodeRomFamily F instDec) (c2NodeRomCarrier F instDec) Q A) :
    Negl (gameAdv (c2NodeRomGame F instDec) A) :=
  romCarrier_binds _ _ Q hQ (instRomFamily_card_R _ _ _ _ _ _ _ _) A hA

/-- **(TOOTH — class inhabited with positive advantage, node site.)** -/
theorem c2NodeRom_class_inhabited_pos (F : Compress2Family)
    (instDec : ∀ l, DecidableEq (F.Inst l)) (Q : ℕ → ℕ) :
    ∃ A, RomCarrierEff (c2NodeRomFamily F instDec) (c2NodeRomCarrier F instDec) Q A
      ∧ ∀ l, 0 < gameAdv (c2NodeRomGame F instDec) A l := by
  refine ⟨romCarrierAdv (c2NodeRomFamily F instDec) (c2NodeRomCarrier F instDec)
      (constTripleComp (c2NodeRomFamily F instDec) (c2NodeRomCarrier F instDec)
        (fun l => ((F.instNe l).some, ()))
        (fun _ => (⟨0, babyBearP_pos⟩, ⟨0, babyBearP_pos⟩))
        (fun _ => (⟨1, one_lt_babyBearP⟩, ⟨0, babyBearP_pos⟩))),
    constTriple_in_eff (c2NodeRomFamily F instDec) (c2NodeRomCarrier F instDec) _ _ _ Q,
    fun l => constTriple_gameAdv_pos (c2NodeRomFamily F instDec) (c2NodeRomCarrier F instDec)
      _ _ _ l ?_⟩
  intro hc
  have : (0 : ℕ) = 1 := congrArg (fun p : Fin babyBearP × Fin babyBearP => p.1.val) hc
  omega

/-- **(TOOTH — the constant answerer is DEFANGED; a non-negligible forger is EXCLUDED — node
site.)** -/
theorem c2NodeRom_nonNegl_forger_excluded (F : Compress2Family)
    (instDec : ∀ l, DecidableEq (F.Inst l)) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (c2NodeRomGame F instDec))
    (hnn : ¬ Negl (gameAdv (c2NodeRomGame F instDec) A)) :
    ¬ RomCarrierEff (c2NodeRomFamily F instDec) (c2NodeRomCarrier F instDec) Q A :=
  romCarrier_choiceForger_excluded _ _ Q hQ (instRomFamily_card_R _ _ _ _ _ _ _ _) A hnn

/-! ### §6b — the factory content address (`HashInjective`'s consumer), at the sampled oracle. -/

/-- **THE FACTORY ROM FAMILY** — keyed by a sampled instance space, over descriptor serializations of
at most `m` bytes: the truncated shape of what BLAKE3 absorbs to mint a `factory_vk`. -/
def factoryRomFamily (Inst : ℕ → Type) (instFin : ∀ l, Fintype (Inst l))
    (instDec : ∀ l, DecidableEq (Inst l)) (instNe : ∀ l, Nonempty (Inst l)) (m : ℕ) :
    KeyedRomFamily :=
  instRomFamily Inst instFin instDec instNe (fun _ => BVec (Fin 256) m)
    (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ => ⟨(⟨0, Nat.succ_pos m⟩, fun _ => none)⟩)

/-- **THE FACTORY CARRIER** — commitment `H (i, ser (schema, program))`: the `vk` binds the WHOLE
published content through its serialization. Per-site content: the serialization `ser` and its
injectivity — the layout facts BLAKE3's input encoding genuinely satisfies. The payloads are the
contents whose serialization FITS the truncation bound (`Subtype` on length ≤ `m`). -/
noncomputable def factoryRomCarrier (Inst : ℕ → Type) (instFin : ∀ l, Fintype (Inst l))
    (instDec : ∀ l, DecidableEq (Inst l)) (instNe : ∀ l, Nonempty (Inst l)) (m : ℕ)
    (ser : Schema × RecordProgram → List (Fin 256)) (serInj : Function.Injective ser) :
    RomCarrier (factoryRomFamily Inst instFin instDec instNe m) :=
  taggedCarrier _ (fun _ => Unit)
    (fun _ => {q : Schema × RecordProgram // (ser q).length ≤ m})
    (fun _ => Classical.decEq _)
    (fun _ _ q => bvecOfList m (ser q.1) q.2)
    (fun _ _ a b h => Subtype.ext (serInj (bvecOfList_inj a.2 b.2 h)))

/-- The factory forgery game at the sampled oracle: the adversary PUBLISHES a `vk` and exhibits two
DISTINCT contents that BOTH content-address to it — `romOpenGame`, the `factoryForgeryGame` event
with WELL-FORMEDNESS (each `vk` IS the hash of its own content) now the opening equations
themselves. -/
@[reducible] noncomputable def factoryRomGame (Inst : ℕ → Type) (instFin : ∀ l, Fintype (Inst l))
    (instDec : ∀ l, DecidableEq (Inst l)) (instNe : ∀ l, Nonempty (Inst l)) (m : ℕ)
    (ser : Schema × RecordProgram → List (Fin 256)) (serInj : Function.Injective ser) : Game :=
  romOpenGame (factoryRomFamily Inst instFin instDec instNe m)
    (factoryRomCarrier Inst instFin instDec instNe m ser serInj)

/-- **⚑⚑ RE-GROUNDED `vk_determines_invariants_advantage_bound`, DISCHARGED ON THE PROVED FLOOR** —
every query-bounded factory forger has NEGLIGIBLE advantage: the published `vk` determines the cell's
whole published contract EXCEPT with negligible probability, in the keyed ROM model of §6's header.
Constructor transparency on a floor that is a THEOREM, not a refutable hypothesis. -/
theorem vk_determines_invariants_binds_rom (Inst : ℕ → Type) (instFin : ∀ l, Fintype (Inst l))
    (instDec : ∀ l, DecidableEq (Inst l)) (instNe : ∀ l, Nonempty (Inst l)) (m : ℕ)
    (ser : Schema × RecordProgram → List (Fin 256)) (serInj : Function.Injective ser)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (factoryRomGame Inst instFin instDec instNe m ser serInj))
    (hA : RomOpenEff (factoryRomFamily Inst instFin instDec instNe m)
      (factoryRomCarrier Inst instFin instDec instNe m ser serInj) Q A) :
    Negl (gameAdv (factoryRomGame Inst instFin instDec instNe m ser serInj) A) :=
  rom_open_binds _ _ Q hQ (instRomFamily_card_R _ _ _ _ _ _ _ _) A hA

/-- **(TOOTH — class inhabited with positive advantage, factory site.)** Two contents with distinct
serializations-in-bound witness the game winnable at every parameter. -/
theorem factoryRom_class_inhabited_pos (Inst : ℕ → Type) (instFin : ∀ l, Fintype (Inst l))
    (instDec : ∀ l, DecidableEq (Inst l)) (instNe : ∀ l, Nonempty (Inst l)) (m : ℕ)
    (ser : Schema × RecordProgram → List (Fin 256)) (serInj : Function.Injective ser)
    (Q : ℕ → ℕ) {q q' : Schema × RecordProgram}
    (hq : (ser q).length ≤ m) (hq' : (ser q').length ≤ m) (hne : q ≠ q') :
    ∃ A, RomOpenEff (factoryRomFamily Inst instFin instDec instNe m)
        (factoryRomCarrier Inst instFin instDec instNe m ser serInj) Q A
      ∧ ∀ l, 0 < gameAdv (factoryRomGame Inst instFin instDec instNe m ser serInj) A l := by
  refine ⟨romOpenAdv (factoryRomFamily Inst instFin instDec instNe m)
      (factoryRomCarrier Inst instFin instDec instNe m ser serInj)
      (constOpenComp (factoryRomFamily Inst instFin instDec instNe m)
        (factoryRomCarrier Inst instFin instDec instNe m ser serInj)
        (fun l => ⟨0, by positivity⟩) (fun l => ((instNe l).some, ()))
        (fun _ => ⟨q, hq⟩) (fun _ => ⟨q', hq'⟩)),
    constOpen_in_eff (factoryRomFamily Inst instFin instDec instNe m)
      (factoryRomCarrier Inst instFin instDec instNe m ser serInj) _ _ _ _ Q,
    fun l => constOpen_gameAdv_pos (factoryRomFamily Inst instFin instDec instNe m)
      (factoryRomCarrier Inst instFin instDec instNe m ser serInj) _ _ _ _ l ?_⟩
  intro hc
  exact hne (congrArg Subtype.val hc)

/-- **(TOOTH — a non-negligible factory forger is OUTSIDE the class.)** -/
theorem factoryRom_nonNegl_forger_excluded (Inst : ℕ → Type) (instFin : ∀ l, Fintype (Inst l))
    (instDec : ∀ l, DecidableEq (Inst l)) (instNe : ∀ l, Nonempty (Inst l)) (m : ℕ)
    (ser : Schema × RecordProgram → List (Fin 256)) (serInj : Function.Injective ser)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (factoryRomGame Inst instFin instDec instNe m ser serInj))
    (hnn : ¬ Negl (gameAdv (factoryRomGame Inst instFin instDec instNe m ser serInj) A)) :
    ¬ RomOpenEff (factoryRomFamily Inst instFin instDec instNe m)
      (factoryRomCarrier Inst instFin instDec instNe m ser serInj) Q A :=
  romOpen_forger_excluded _ _ Q hQ (instRomFamily_card_R _ _ _ _ _ _ _ _) A hnn

/-! ### §6c — the macaroon binding hash (`BindingHashCR`'s consumer), at the sampled oracle.

⚑ Per §1c this is the one carrier NOT refuted at deployed parameters; the ROM successor still earns
its keep the same way §4 did — it states FINDING, not existence — and now with the floor a THEOREM.
The `hmacInj` MAC peel of `rebind_wins_imp` is deployed-side and oracle-independent: a deployed
re-binding break peels to exactly the two-distinct-tails-one-body event below. -/

/-- **THE BINDING ROM FAMILY** — keyed by the `BindingFamily`'s own sampled instance space, over the
(finite, e.g. 32-byte) macaroon tail space. -/
def bindingRomFamily (F : BindingFamily) (instDec : ∀ l, DecidableEq (F.Inst l))
    (tagFin : Fintype F.Tag) (tagNe : Nonempty F.Tag) : KeyedRomFamily :=
  instRomFamily F.Inst F.instFin instDec F.instNe (fun _ => F.Tag)
    (fun _ => tagFin) (fun _ => F.tagDec) (fun _ => tagNe)

/-- **THE BINDING CARRIER** — commitment `H (i, tail)`: the caveat body binds the parent tail in one
query; the embedding is the identity. -/
def bindingRomCarrier (F : BindingFamily) (instDec : ∀ l, DecidableEq (F.Inst l))
    (tagFin : Fintype F.Tag) (tagNe : Nonempty F.Tag) :
    RomCarrier (bindingRomFamily F instDec tagFin tagNe) :=
  taggedCarrier _ (fun _ => Unit) (fun _ => F.Tag) (fun _ => F.tagDec)
    (fun _ _ v => v) (fun _ _ _ _ h => h)

/-- The re-binding break at the sampled oracle: two DISTINCT parent tails, one binding body. -/
abbrev rebindRomGame (F : BindingFamily) (instDec : ∀ l, DecidableEq (F.Inst l))
    (tagFin : Fintype F.Tag) (tagNe : Nonempty F.Tag) : Game :=
  romCarrierGame (bindingRomFamily F instDec tagFin tagNe)
    (bindingRomCarrier F instDec tagFin tagNe)

/-- **⚑⚑ RE-GROUNDED `rebinding_advantage_bound`, DISCHARGED ON THE PROVED FLOOR** — every
query-bounded re-binder (after the deployed-side, oracle-independent `hmacInj` peel of
`rebind_wins_imp`) has NEGLIGIBLE advantage, in the keyed ROM model of §6's header. -/
theorem rebinding_binds_rom (F : BindingFamily) (instDec : ∀ l, DecidableEq (F.Inst l))
    (tagFin : Fintype F.Tag) (tagNe : Nonempty F.Tag) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (rebindRomGame F instDec tagFin tagNe))
    (hA : RomCarrierEff (bindingRomFamily F instDec tagFin tagNe)
      (bindingRomCarrier F instDec tagFin tagNe) Q A) :
    Negl (gameAdv (rebindRomGame F instDec tagFin tagNe) A) :=
  romCarrier_binds _ _ Q hQ (instRomFamily_card_R _ _ _ _ _ _ _ _) A hA

/-- **(TOOTH — class inhabited with positive advantage, binding site.)** Needs two distinct tails —
supplied as hypotheses, since `Tag` is abstract here. -/
theorem rebindRom_class_inhabited_pos (F : BindingFamily) (instDec : ∀ l, DecidableEq (F.Inst l))
    (tagFin : Fintype F.Tag) (tagNe : Nonempty F.Tag) (Q : ℕ → ℕ)
    {a b : F.Tag} (hne : a ≠ b) :
    ∃ A, RomCarrierEff (bindingRomFamily F instDec tagFin tagNe)
        (bindingRomCarrier F instDec tagFin tagNe) Q A
      ∧ ∀ l, 0 < gameAdv (rebindRomGame F instDec tagFin tagNe) A l :=
  ⟨romCarrierAdv (bindingRomFamily F instDec tagFin tagNe)
      (bindingRomCarrier F instDec tagFin tagNe)
      (constTripleComp (bindingRomFamily F instDec tagFin tagNe)
        (bindingRomCarrier F instDec tagFin tagNe)
        (fun l => ((F.instNe l).some, ())) (fun _ => a) (fun _ => b)),
    constTriple_in_eff (bindingRomFamily F instDec tagFin tagNe)
      (bindingRomCarrier F instDec tagFin tagNe) _ _ _ Q,
    fun l => constTriple_gameAdv_pos (bindingRomFamily F instDec tagFin tagNe)
      (bindingRomCarrier F instDec tagFin tagNe) _ _ _ l hne⟩

/-- **(TOOTH — a non-negligible re-binder is OUTSIDE the class.)** -/
theorem rebindRom_nonNegl_forger_excluded (F : BindingFamily)
    (instDec : ∀ l, DecidableEq (F.Inst l)) (tagFin : Fintype F.Tag) (tagNe : Nonempty F.Tag)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (rebindRomGame F instDec tagFin tagNe))
    (hnn : ¬ Negl (gameAdv (rebindRomGame F instDec tagFin tagNe) A)) :
    ¬ RomCarrierEff (bindingRomFamily F instDec tagFin tagNe)
      (bindingRomCarrier F instDec tagFin tagNe) Q A :=
  romCarrier_choiceForger_excluded _ _ Q hQ (instRomFamily_card_R _ _ _ _ _ _ _ _) A hnn

#assert_all_clean [
  finite_range_of_field_window,
  finite_range_of_nat_window,
  compress1CR_false_of_finite_range,
  compress1CR_false_babyBear,
  deployedCompress2_compress1_not_Compress1CR,
  compress1CR_field_uninhabitable_babyBear,
  hashInjective_false_of_finite_range,
  hashInjective_false_blake3,
  bindingHashCR_false_of_compressing,
  bindingHashCR_false_of_infinite_tag,
  c2NodeGame_wins_iff,
  c2_wins_imp,
  c2_adv_le,
  compress2_node_advantage_bound,
  factoryForgeryGame_wins_iff,
  factory_wins_imp,
  factory_adv_le,
  vk_determines_invariants_advantage_bound,
  rebind_wins_imp,
  rebind_adv_le,
  rebinding_advantage_bound,
  bindingHashFamily_CR_of_bindingHashCR,
  c1_floor_satisfiable_vacuously,
  c1_floor_top_false_of_compressing,
  factory_floor_satisfiable_vacuously,
  factory_floor_top_false_of_compressing,
  binding_floor_satisfiable_vacuously,
  binding_floor_top_false_of_compressing,
  instRomFamily_card_R,
  c2NodeRom_collision_is_break,
  compress2_node_binds_rom,
  c2NodeRom_class_inhabited_pos,
  c2NodeRom_nonNegl_forger_excluded,
  vk_determines_invariants_binds_rom,
  factoryRom_class_inhabited_pos,
  factoryRom_nonNegl_forger_excluded,
  rebinding_binds_rom,
  rebindRom_class_inhabited_pos,
  rebindRom_nonNegl_forger_excluded
]

end Dregg2.Crypto.FactoryBindingFloorRegrounded
