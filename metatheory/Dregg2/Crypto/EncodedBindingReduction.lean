/-
# `Dregg2.Crypto.EncodedBindingReduction` — the REUSABLE reduction spine for every
`digest binds the object` claim in the deployed circuit tree.

## The sin this retires, once, generically

The tree is full of keystones of the shape

    theorem foo_binds_or_collides … (h : dig x = dig x') : x = x' ∨ FooColl dig x x'

`FooColl` is a predicate about the pair a TOTAL extractor returns, so — unlike an `∃ collision` — it is
not unconditionally true by pigeonhole *at a fixed pair*.  But the DISJUNCTION still quantifies over
SOLUTIONS: at deployed BabyBear parameters a collision of the underlying sponge/chip EXISTS
(`VacuitySweepTeeth`), so nothing in the statement prevents an adversary from living in the right
branch forever.  `binds ∨ collides` NAMES the floor; it does not STAND on it.  Cryptographic hardness
quantifies over EFFICIENT ADVERSARIES, and that is the object this module supplies.

## What is generic here, and why that is the whole point

Every one of those keystones has the SAME anatomy:

  * a deployed keyed primitive `F : KeyedHashFamily` (the sponge `List ℤ → ℤ`, the arity-16 chip
    `List ℤ → Digest8`, the wide permutation `List ℤ → List ℤ`, the 4-to-1 compress `ℤ⁴ → ℤ`),
  * a DOMAIN `α` the circuit claims the digest binds (a `system_roots` sub-block, a cap leaf, a heap
    path, a transfer descriptor, a whole post-state, …),
  * an ENCODER `enc : ∀ l, F.Key l → α → F.Input` — the ordered limb list the deployed prover absorbs,
  * and the claim "equal `F.H ∘ enc` ⟹ equal `enc`".

So the reduction is the SAME reduction every time: the forgery is a `Game` whose win relation is
"two domain points with DISTINCT encodings and EQUAL images"; the extractor is `enc` applied to both
answers — a map of adversaries into `hashGame F`; win-preservation is definitional; the advantage
inequality is `winProb_le_of_imp` over the SAME sampled key space; the security conclusion is
domination under `HashCRHardQuant F Eff`.  Writing that ~60 times by hand is how the per-site copies
drift.  It is written ONCE here, and each site supplies only

  1. its encoder and the definitional fact that its deployed digest IS `F.H ∘ enc`,
  2. the STRUCTURAL injectivity of its encoder (`a ≠ a' → enc a ≠ enc a'`) — a real theorem about the
     limb layout, never about the hash,
  3. the output-size fact `hout` (the `poly_time` slot).

Everything else — the game, the extractor, the inequality, the negligibility, the efficiency
discharge, both poles, the canary — is inherited.

## The efficiency parameter is DISCHARGED, not carried

`encBinding_advantage_bound` is the statement at an ARBITRARY adversary class `Eff` (with the honest
`hEff` obligation in the open).  `encBinding_from_polyTime` instantiates `Eff` at
`CostAdversary.IsPolyTime` — a cost-vector model whose cost is derived from a deep-embedded program's
SYNTAX — and DERIVES `hEff` with `CostTactics.poly_time`, leaving `hout` as the only per-site input.
The ⊤-collapse witness (`CostAdversary.bruteForce`) is PROVED excluded from that class and the class is
PROVED inhabited, so the instantiated floor sits strictly between the two poles proved in §4.

## ⚑ The `_from_polyTime` discharges are DELETED; §7 is the DISCHARGED successor (07-24)

`Exec.SystemRootsBindingReduction.sysRoots_floor_polyTime_false_babyBear` refutes the
`IsPolyTime`-instantiated floor at the deployed sponge, and `Crypto.RomBindingReduction`'s header
proves no `Eff` repairs the fixed-function game.  `encBinding_from_polyTime` /
`encBinding_from_polyTime_fixedWidth` therefore discharged onto a hypothesis that is FALSE at
deployed parameters — they are DELETED, and §7 lands the successor in-file on the PROVED keyed-ROM
floor: the forger is an ORACLE PROGRAM over the sampled key-separated oracle, the site's
key-dependent encoder becomes a `RomCarrierSites.keyedEncCarrier`, and `encBinding_rom` concludes
`Negl` from `KeyedRomFloor.keyedRom_hard` (the birthday bound — a THEOREM) via `flatSite_binds`,
with nothing refutable carried.  The chained shape's successor is `RomCarrierSites.chained_rom_binds`.
The `_advantage_bound` forms here stay the honest fixed-hash statements with `hEff` in the open.

## Bars

No `sorry`, no `axiom`, no `native_decide`, no `decide` on an opaque `Prop`.  Cost stays SYNTACTIC.
-/
import Dregg2.Crypto.FloorGames
import Dregg2.Crypto.CostAdversary
import Dregg2.Crypto.CostTactics
import Dregg2.Crypto.HermineHashCRRegrounded
import Dregg2.Crypto.RomCarrierSites
import Dregg2.Tactics

namespace Dregg2.Crypto.EncodedBindingReduction

open Dregg2.Crypto.ConcreteSecurity (Negl)
open Dregg2.Crypto.ProbCrypto (winProb_le_of_imp negl_of_le)
open Dregg2.Circuit.HashFloorHonesty
  (KeyedHashFamily not_injective_of_finite_range)
open Dregg2.Crypto.FloorGames
  (Game Adversary gameAdv gameAdv_mem_unit hashGame HashCRHardQuant hard_bot_vacuous
   hashCRHardQuant_top_false_of_compressing)
open Dregg2.Crypto.CostAdversary (AnsSize IsPolyTime)
open Dregg2.Crypto.CostTactics (isPolyTime_postMap')

set_option autoImplicit false

/-! ## §1 — the ENCODED-DOMAIN BREAK GAME: the forgery, as a first-class `Game`.

The adversary is handed a uniformly sampled key (at every deployed site: the domain-separation tag the
prover absorbs) and WINS iff it outputs two points of the bound domain whose deployed ENCODINGS DIFFER
yet whose deployed DIGESTS agree.  That is exactly the forgery the `_binds_or_collides` disjunction
declined to price: the prover publishing one digest and opening it two ways.

The encoding inequality is the honest side condition, not a weakening — a "forgery" whose encodings
AGREE is not a break of this primitive at all (the two domain points are the same absorbed message;
any residual disagreement lives in a SEPARATELY-priced layer, e.g. a lower digest that fed a limb). -/

/-- **THE FORGERY GAME.** `α` is the domain the deployed digest claims to bind; `enc` is the ordered
limb list the prover absorbs.  A win is a genuine equivocation of `F` at the sampled key. -/
def encBreakGame (F : KeyedHashFamily) (α : Type) (enc : ∀ l, F.Key l → α → F.Input) : Game where
  Inst := F.Key
  Ans := fun _ => α × α
  instFin := F.keyFintype
  instNe := F.keyNonempty
  wins := fun l k c =>
    enc l k c.1 ≠ enc l k c.2 ∧ F.H l k (enc l k c.1) = F.H l k (enc l k c.2)
  winsDec := fun l k c => by
    letI := F.inputDecEq; letI := F.outDecEq; infer_instance

/-- **THE PROBLEM IS IN THE STATEMENT.** The win relation unfolds to a genuine equivocation of the real
deployed keyed primitive — no docstring carries the content. -/
theorem encBreakGame_wins_iff (F : KeyedHashFamily) (α : Type)
    (enc : ∀ l, F.Key l → α → F.Input) (l : ℕ) (k : F.Key l) (c : α × α) :
    (encBreakGame F α enc).wins l k c ↔
      (enc l k c.1 ≠ enc l k c.2 ∧ F.H l k (enc l k c.1) = F.H l k (enc l k c.2)) :=
  Iff.rfl

/-- **⚑ THE FORGERY IS THE DEPLOYED OBJECT.** Two domain points a site's `_binds_or_collides`
extractor lands on — DISTINCT encodings, EQUAL deployed digests — ARE a win.  Every site's bridge
theorem is this lemma at its own encoder, which is what keeps the game from being free-floating. -/
theorem encForgery_is_break (F : KeyedHashFamily) (α : Type) (enc : ∀ l, F.Key l → α → F.Input)
    {l : ℕ} {k : F.Key l} {a a' : α} (hne : enc l k a ≠ enc l k a')
    (heq : F.H l k (enc l k a) = F.H l k (enc l k a')) :
    (encBreakGame F α enc).wins l k (a, a') :=
  ⟨hne, heq⟩

/-- **THE STRUCTURAL BRIDGE.** When the encoder is injective — a real theorem about the deployed LIMB
LAYOUT, proved without touching the hash — distinct domain points are already distinct encodings, so a
digest equivocation on distinct points is a win.  This is the shape every tree/leaf/state site uses. -/
theorem encForgery_is_break_of_inj (F : KeyedHashFamily) (α : Type)
    (enc : ∀ l, F.Key l → α → F.Input)
    (hinj : ∀ l (k : F.Key l) (a a' : α), enc l k a = enc l k a' → a = a')
    {l : ℕ} {k : F.Key l} {a a' : α} (hne : a ≠ a')
    (heq : F.H l k (enc l k a) = F.H l k (enc l k a')) :
    (encBreakGame F α enc).wins l k (a, a') :=
  ⟨fun h => hne (hinj l k a a' h), heq⟩

/-! ## §2 — the EXTRACTOR, as a map of adversaries, and the advantage inequality. -/

/-- **THE EXTRACTOR.** A digest forger becomes a collision finder for the deployed primitive by
handing back the two ENCODINGS of its answers.  A Lean function on adversaries — not a
`Classical.choose` of an existential, which is what makes the result an advantage bound rather than a
restatement of pigeonhole. -/
def encBreakToFinder (F : KeyedHashFamily) (α : Type) (enc : ∀ l, F.Key l → α → F.Input)
    (A : Adversary (encBreakGame F α enc)) : Adversary (hashGame F) where
  run := fun l k => (enc l k (A.run l k).1, enc l k (A.run l k).2)

/-- **⚑ WIN-PRESERVATION — the reduction, at the game level.** Every key the forger wins, the extracted
finder wins the collision game of the REAL primitive: the two encodings are distinct (the forgery's own
side condition) with equal images (the equal published digest).  Definitional: the games agree on the
nose, which is the honest reading of "this reduction adds nothing but the encoding". -/
theorem enc_wins_imp (F : KeyedHashFamily) (α : Type) (enc : ∀ l, F.Key l → α → F.Input)
    (A : Adversary (encBreakGame F α enc)) (l : ℕ) (k : F.Key l)
    (hwin : (encBreakGame F α enc).wins l k (A.run l k)) :
    (hashGame F).wins l k ((encBreakToFinder F α enc A).run l k) :=
  hwin

/-- **THE ADVANTAGE INEQUALITY.** The forger's advantage is at most the extracted collision finder's,
at every security parameter — over the SAME uniformly sampled key space. -/
theorem enc_adv_le (F : KeyedHashFamily) (α : Type) (enc : ∀ l, F.Key l → α → F.Input)
    (A : Adversary (encBreakGame F α enc)) (l : ℕ) :
    gameAdv (encBreakGame F α enc) A l
      ≤ gameAdv (hashGame F) (encBreakToFinder F α enc A) l := by
  refine @winProb_le_of_imp _ (F.keyFintype l) _ _ (fun k hk => ?_)
  replace hk := (Adversary.hit_eq_true _ _ _).mp hk
  refine (Adversary.hit_eq_true _ _ _).mpr ?_
  exact enc_wins_imp F α enc A l k hk

/-- **⚑ THE HEADLINE BINDING, AS A SECURITY REDUCTION.**

Under the DEPLOYED primitive's collision floor at the class `Eff`, a digest forger whose extracted
finder is in that class has NEGLIGIBLE advantage: the deployed digest binds its whole encoded domain
EXCEPT with negligible probability.  This is what replaces `binds ∨ collides` as the exported claim —
it quantifies over EFFICIENT ADVERSARIES, where the disjunction quantified over SOLUTIONS.

`hEff` is the standard "the reduction is efficient", left in the open at an arbitrary class; §3
discharges it at `Eff := IsPolyTime` and §4 prices both poles. -/
theorem encBinding_advantage_bound (F : KeyedHashFamily) (α : Type)
    (enc : ∀ l, F.Key l → α → F.Input)
    (Eff : Adversary (hashGame F) → Prop)
    (A : Adversary (encBreakGame F α enc))
    (hEff : Eff (encBreakToFinder F α enc A))
    (hCR : HashCRHardQuant F Eff) :
    Negl (gameAdv (encBreakGame F α enc) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (encBreakGame F α enc) A l).1)
    (enc_adv_le F α enc A) (hCR _ hEff)

/-! ## §3 — the extractor is a pure post-map (the cost-model record; the `IsPolyTime` discharge that
stood here is DELETED — its floor is refuted — and §7 is the discharged keyed-ROM successor). -/

/-- The extractor IS a `CostAdversary.Adversary.postMap` — a pure output reshaping with the key passed
through.  Definitional, and it is what lets `poly_time` apply. -/
theorem encBreakToFinder_eq_postMap (F : KeyedHashFamily) (α : Type)
    (enc : ∀ l, F.Key l → α → F.Input) (A : Adversary (encBreakGame F α enc)) :
    encBreakToFinder F α enc A
      = Dregg2.Crypto.CostAdversary.Adversary.postMap (G := encBreakGame F α enc)
          (G' := hashGame F) (fun _ => rfl)
          (fun l k c => (enc l k c.1, enc l k c.2)) A :=
  rfl

/-- **THE STANDARD ANSWER ENCODING OF THE COLLISION GAME** — the two claimed preimages, measured by the
domain's own size.  Concrete on purpose: the size measure belongs to the GAME (`CostAdversary` design
commitment 4), and leaving it open would let a degenerate `sz := 0` make output free. -/
def pairAnsSize (F : KeyedHashFamily) (szI : ℕ → F.Input → ℕ) : AnsSize (hashGame F) :=
  fun l p => szI l p.1 + szI l p.2

/-- The forgery game's answer encoding — the two domain points. -/
def domainAnsSize (F : KeyedHashFamily) (α : Type) (enc : ∀ l, F.Key l → α → F.Input)
    (szD : ℕ → α → ℕ) : AnsSize (encBreakGame F α enc) :=
  fun l c => szD l c.1 + szD l c.2

/-! ## §4 — both poles of the floor, PROVED, so any instantiation can be priced exactly. -/

/-- **A NON-INJECTIVE primitive HAS a collision** — the bridge from the sweep's `¬ Function.Injective`
teeth to the compressing hypothesis the ⊤ pole consumes.  Pure logic. -/
theorem exists_collision_of_not_injective {β γ : Type} {h : β → γ}
    (hni : ¬ (∀ x y : β, h x = h y → x = y)) : ∃ x y : β, x ≠ y ∧ h x = h y := by
  by_contra hcon
  exact hni (fun x y hxy => by
    by_contra hne
    exact hcon ⟨x, y, hne, hxy⟩)

/-- **⚑ THE ⊤ POLE — the floor is FALSE at the unrestricted class, for any COMPRESSING primitive.**
The honest price of `hEff`, as a theorem rather than a promise: the `Classical.choice` finder that
outputs a collision at every key wins with probability `1`, and pigeonhole supplies one at deployed
BabyBear parameters.  What the reduction buys is NOT a floor the deployed hash satisfies at ⊤ — no such
floor exists — it is that the residual is ONE named parameter with both poles proved, in place of a
disjunction whose right branch is unconditionally available.

⚑ The `⊤` is WRITTEN OUT in the statement. It used to be reachable through
`HashFloorHonesty.CollisionResistant`, which was a spelling of this very proposition; that name is
DELETED (2026-07-28) and this now applies `FloorGames.hashCRHardQuant_top_false_of_compressing`
directly, with no intermediate rewrite hiding which adversary class is in play. -/
theorem floor_top_false_of_compressing (F : KeyedHashFamily) (hin : Nonempty F.Input)
    (hcol : ∀ l (k : F.Key l), ∃ x y : F.Input, x ≠ y ∧ F.H l k x = F.H l k y) :
    ¬ HashCRHardQuant F (fun _ => True) :=
  hashCRHardQuant_top_false_of_compressing F hin hcol

/-- **THE ⊥ POLE — vacuous.** Recorded so the floor's satisfiability cannot be mistaken for evidence:
at the empty class it holds for a completely broken primitive too. -/
theorem floor_bot_vacuous (F : KeyedHashFamily) : HashCRHardQuant F (fun _ => False) :=
  hard_bot_vacuous _

/-- **(TOOTH — the `IsPolyTime` class is NOT EMPTY.)** The constant finder that writes the fixed answer
`a₀` is in the class whenever that answer is poly-size.  Together with
`CostAdversary.bruteForce_not_polyTime` (the ⊤-collapse witness is EXCLUDED) this pins the instantiated
floor STRICTLY between the two poles above — the instantiation is neither ⊤ (false) nor ⊥ (vacuous). -/
theorem isPolyTime_class_inhabited (F : KeyedHashFamily) (szI : ℕ → F.Input → ℕ)
    (a₀ : ∀ l, F.Key l → F.Input × F.Input)
    (hsz : ∃ C k : ℕ, ∀ l (i : F.Key l), pairAnsSize F szI l (a₀ l i) ≤ C * l ^ k + C) :
    IsPolyTime (pairAnsSize F szI)
      (Dregg2.Crypto.CostAdversary.idAdv (G := hashGame F) (O := Unit) (Q := fun _ => Unit)
        (R := fun _ => Unit) a₀).toAdversary :=
  Dregg2.Crypto.CostAdversary.isPolyTime_inhabited _ _ hsz

/-! ## §5 — the CANARY: strip the reduction and the keystone goes RED.

A gate that refuses everything is a broken keystone, not a fixed one, so both teeth are here: the
floor at the WRONG finder does NOT close the forger, and the floor at the EXTRACTED finder DOES. -/

/-- **(CANARY.)** The collision floor applied at some OTHER finder `B` — not the one EXTRACTED from the
forger — cannot conclude the forger's negligibility.  Only `enc_adv_le` connects the two games.  This
tooth reds if a future edit collapses the games into each other (the `P → P` shape). -/
example (F : KeyedHashFamily) (α : Type) (enc : ∀ l, F.Key l → α → F.Input)
    (Eff : Adversary (hashGame F) → Prop)
    (A : Adversary (encBreakGame F α enc))
    (B : Adversary (hashGame F)) (hB : Eff B)
    (hCR : HashCRHardQuant F Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (encBreakGame F α enc) A) := hCR B hB)
  trivial

/-- **THE POSITIVE POLE — the RIGHT floor DOES discharge it.** With the floor at the EXTRACTED finder
the binding fires; refusal is discrimination only if acceptance still happens. -/
theorem the_reduced_binding_fires (F : KeyedHashFamily) (α : Type)
    (enc : ∀ l, F.Key l → α → F.Input)
    (Eff : Adversary (hashGame F) → Prop)
    (A : Adversary (encBreakGame F α enc))
    (hEff : Eff (encBreakToFinder F α enc A))
    (hCR : HashCRHardQuant F Eff) :
    Negl (gameAdv (encBreakGame F α enc) A) :=
  encBinding_advantage_bound F α enc Eff A hEff hCR

/-- **(CANARY — the game is not trivially unwinnable.)** A break at a REFLEXIVE answer is impossible at
EVERY primitive (a collision needs distinct encodings), so the game does not accidentally hand the
adversary a free win; combined with §5's `fail_if_success` this pins the game as two-valued. -/
theorem no_reflexive_break (F : KeyedHashFamily) (α : Type) (enc : ∀ l, F.Key l → α → F.Input)
    (l : ℕ) (k : F.Key l) (a : α) : ¬ (encBreakGame F α enc).wins l k (a, a) := by
  rintro ⟨hne, -⟩
  exact hne rfl

/-! ## §6 — CHAINED bindings: the union bound, once, for every `root ⟸ node ⟸ leaf` site.

Almost every deployed keystone is a CHAIN: a commitment absorbs a digest which absorbs a sub-block; a
Merkle root folds a node which folds a leaf.  Their `_or_collides` forms show it as a THREE-way bare
disjunction (`equal ∨ CommitColl ∨ InnerColl`), which is exactly where the shirk compounds — two escape
branches instead of one.

The honest form is the standard UNION BOUND: the composed forger's advantage is at most the SUM of the
two extracted finders' advantages, and a sum of negligibles is negligible.  Stated once here, over a
forgery game that shares the primitive's key space (which every deployed site does — one sampled
domain-separation tag runs the whole chain). -/

/-- **A FORGERY OVER `F`'s OWN KEY SPACE** — the composed (chained) break, before it is a `Game`.
Bundled so the union bound below can talk about "the same sampled tag" without transporting instance
spaces across an equality. -/
structure KeyedForgery (F : KeyedHashFamily) where
  /-- What the composed forger outputs. -/
  Ans : ℕ → Type
  /-- **THE PROBLEM** — the composed equivocation the deployed chain forbids. -/
  wins : ∀ l, F.Key l → Ans l → Prop
  /-- The win event is counted, so it is decidable. -/
  winsDec : ∀ l (k : F.Key l) (a : Ans l), Decidable (wins l k a)

/-- The composed forgery, as a first-class `Game` over the primitive's sampled key space. -/
def KeyedForgery.game {F : KeyedHashFamily} (P : KeyedForgery F) : Game where
  Inst := F.Key
  Ans := P.Ans
  instFin := F.keyFintype
  instNe := F.keyNonempty
  wins := P.wins
  winsDec := P.winsDec

/-- **⚑ THE UNION BOUND — a chained forgery is at most the SUM of its two layer breaks.** If every key
the composed forger wins is a win for at least ONE of the two extracted layer forgers, its advantage is
dominated by their sum.  This is the honest replacement for the three-way `∨`: the two escape branches
become two ADDED advantages, each of which the floor then kills. -/
theorem chained_adv_le {F : KeyedHashFamily} (P : KeyedForgery F) (α β : Type)
    (enc₁ : ∀ l, F.Key l → α → F.Input) (enc₂ : ∀ l, F.Key l → β → F.Input)
    (A : Adversary P.game)
    (B₁ : Adversary (encBreakGame F α enc₁)) (B₂ : Adversary (encBreakGame F β enc₂))
    (himp : ∀ l (k : F.Key l), P.wins l k (A.run l k) →
      (encBreakGame F α enc₁).wins l k (B₁.run l k)
        ∨ (encBreakGame F β enc₂).wins l k (B₂.run l k))
    (l : ℕ) :
    gameAdv P.game A l
      ≤ gameAdv (encBreakGame F α enc₁) B₁ l + gameAdv (encBreakGame F β enc₂) B₂ l := by
  refine @Dregg2.Crypto.HermineHashCRRegrounded.winProb_le_add_of_imp _ (F.keyFintype l)
    _ _ _ (fun k hk => ?_)
  replace hk := (Adversary.hit_eq_true _ _ _).mp hk
  rcases himp l k hk with h | h
  · exact Or.inl ((B₁.hit_eq_true l k).mpr h)
  · exact Or.inr ((B₂.hit_eq_true l k).mpr h)

/-- **⚑ THE CHAINED HEADLINE BINDING.** Under ONE collision floor for the deployed primitive, a
composed (commit ⟸ digest ⟸ sub-block, or root ⟸ node ⟸ leaf) forger has NEGLIGIBLE advantage — both
layer extractors are killed by the same floor and `Negl` is closed under addition.  The three-way bare
disjunction becomes one negligible advantage. -/
theorem chained_binding_advantage_bound {F : KeyedHashFamily} (P : KeyedForgery F) (α β : Type)
    (enc₁ : ∀ l, F.Key l → α → F.Input) (enc₂ : ∀ l, F.Key l → β → F.Input)
    (Eff : Adversary (hashGame F) → Prop)
    (A : Adversary P.game)
    (B₁ : Adversary (encBreakGame F α enc₁)) (B₂ : Adversary (encBreakGame F β enc₂))
    (himp : ∀ l (k : F.Key l), P.wins l k (A.run l k) →
      (encBreakGame F α enc₁).wins l k (B₁.run l k)
        ∨ (encBreakGame F β enc₂).wins l k (B₂.run l k))
    (hEff₁ : Eff (encBreakToFinder F α enc₁ B₁)) (hEff₂ : Eff (encBreakToFinder F β enc₂ B₂))
    (hCR : HashCRHardQuant F Eff) :
    Negl (gameAdv P.game A) :=
  negl_of_le (fun l => (gameAdv_mem_unit P.game A l).1)
    (chained_adv_le P α β enc₁ enc₂ A B₁ B₂ himp)
    (Dregg2.Crypto.ConcreteSecurity.negl_add
      (encBinding_advantage_bound F α enc₁ Eff B₁ hEff₁ hCR)
      (encBinding_advantage_bound F β enc₂ Eff B₂ hEff₂ hCR))

/-! ## §7 — ⚑⚑ THE DISCHARGED SUCCESSOR: the encoded-domain binding on the PROVED keyed-ROM floor.

⚑ **THE MODELLING STEP, STATED (not smuggled).** The deployed keyed primitive is idealised as ONE
SAMPLED oracle `H : Key × Msg → Fin (2 ^ l)` over the site's (finite, truncated-deployed-shape)
absorbed message space — the standard ROM idealisation at an ASYMPTOTIC digest width, a deliberate
labelled modelling step, NOT a derivation about the fixed public function.  The site's key-dependent
encoder `emb` and its STRUCTURAL payload-injectivity — the same two facts §1 takes — become a
`RomCarrierSites.keyedEncCarrier`; the adversary chooses which key to attack (the key is its
CONTEXT), and what it cannot choose is the sampled oracle. -/

section RomSuccessor

open Dregg2.Crypto.ConcreteSecurity (PolyBounded)
open Dregg2.Crypto.KeyedRomFloor (KeyedRomFamily)
open Dregg2.Crypto.RomBindingReduction (RomCarrier romCarrierGame RomCarrierEff)
open Dregg2.Crypto.RomCarrierSites (flatFamily keyedEncCarrier flatSite_binds)

variable (Key : Type) [Fintype Key] [DecidableEq Key] [Nonempty Key]
variable (Msg : ℕ → Type) [∀ l, Fintype (Msg l)] [∀ l, DecidableEq (Msg l)]
  [∀ l, Nonempty (Msg l)]
variable (α : ℕ → Type) [∀ l, DecidableEq (α l)]

/-- **THE ENCODED-DOMAIN KEYED-ROM FAMILY** — the site's key space and truncated message shape under
the ideal `λ`-bit digest. -/
def encRomFamily : KeyedRomFamily :=
  flatFamily Key inferInstance inferInstance inferInstance Msg
    (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance)

/-- **THE ENCODED-DOMAIN CARRIER** — the site's key-dependent encoder with its STRUCTURAL
payload-injectivity, verbatim §1's two per-site obligations, now over the sampled oracle
(`RomCarrierSites.keyedEncCarrier`: the key rides in the context). -/
def encRomCarrier (emb : ∀ l, Key → α l → Msg l)
    (emb_inj : ∀ l (k : Key) (a b : α l), emb l k a = emb l k b → a = b) :
    RomCarrier (encRomFamily Key Msg) :=
  keyedEncCarrier (encRomFamily Key Msg) α (fun _ => inferInstance) emb emb_inj

/-- **THE FORGERY IS THE DEPLOYED OBJECT, at the sampled oracle** — two DISTINCT domain points whose
encoded messages the oracle maps to ONE digest at the attacked key are a win of the carrier game
(`encForgery_is_break_of_inj`, restated at the sampled oracle). -/
theorem encRom_forgery_is_break (emb : ∀ l, Key → α l → Msg l)
    (emb_inj : ∀ l (k : Key) (a b : α l), emb l k a = emb l k b → a = b)
    (l : ℕ) (H : (romCarrierGame (encRomFamily Key Msg) (encRomCarrier Key Msg α emb emb_inj)).Inst l)
    (k : Key) {a b : α l} (hne : a ≠ b) (heq : H (k, emb l k a) = H (k, emb l k b)) :
    (romCarrierGame (encRomFamily Key Msg) (encRomCarrier Key Msg α emb emb_inj)).wins l H
      (k, a, b) :=
  ⟨hne, heq⟩

/-- **⚑⚑ THE RE-GROUNDED ENCODED-DOMAIN BINDING — floor PROVED, nothing refutable carried.** Every
query-bounded digest forger has NEGLIGIBLE advantage: the deployed digest binds its whole encoded
domain except with negligible probability, in the keyed ROM model of the header.  The hypotheses are
a polynomial query budget and the forger's membership in the query class.  This is what
`encBinding_from_polyTime(_fixedWidth)` (DELETED — floor refuted) claimed and could not have; the
fixed-width side condition dissolved into the finiteness of `Msg`. -/
theorem encBinding_rom (emb : ∀ l, Key → α l → Msg l)
    (emb_inj : ∀ l (k : Key) (a b : α l), emb l k a = emb l k b → a = b)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (romCarrierGame (encRomFamily Key Msg) (encRomCarrier Key Msg α emb emb_inj)))
    (hA : RomCarrierEff (encRomFamily Key Msg) (encRomCarrier Key Msg α emb emb_inj) Q A) :
    Negl (gameAdv (romCarrierGame (encRomFamily Key Msg)
      (encRomCarrier Key Msg α emb emb_inj)) A) :=
  flatSite_binds Key inferInstance inferInstance inferInstance Msg
    (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance)
    (encRomCarrier Key Msg α emb emb_inj) Q hQ A hA

end RomSuccessor

#assert_axioms encRom_forgery_is_break
#assert_axioms encBinding_rom
#assert_axioms encBreakGame_wins_iff
#assert_axioms encForgery_is_break
#assert_axioms encForgery_is_break_of_inj
#assert_axioms enc_wins_imp
#assert_axioms enc_adv_le
#assert_axioms encBinding_advantage_bound
#assert_axioms encBreakToFinder_eq_postMap
#assert_axioms exists_collision_of_not_injective
#assert_axioms floor_top_false_of_compressing
#assert_axioms floor_bot_vacuous
#assert_axioms isPolyTime_class_inhabited
#assert_axioms the_reduced_binding_fires
#assert_axioms no_reflexive_break
#assert_axioms chained_adv_le
#assert_axioms chained_binding_advantage_bound

end Dregg2.Crypto.EncodedBindingReduction
