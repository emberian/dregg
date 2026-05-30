/-
# Metatheory.EpistemicDial — the unified epistemic dial.

**Move #3 of the svenvs↔dregg2 triangle.** This module proves that two apparently
different disclosure stories are *the same dial at two resolutions*:

  * **svenvs's** single-party `{disclose, non-disclose}` testimony channel (a lone judge:
    *"the verifier learns `w` ⇒ an obligation; the small thing may speak for itself, never
    be seized"*); and
  * **dregg2's** three privacy modes `{Trusted, Selective, Fully-Private}` (many knowers:
    full cleartext+trace / chosen facts+conclusion / one acceptance bit),

are **both monotone order-embeddings into one `Dial`** — a bounded chain of disclosure
positions running from `fullDisclosure` (the verifier learns cleartext + trace) down
through `selective` (chosen facts + the conclusion) to `acceptanceOnly` (one bit: it
verifies). *Turning the dial down reveals less and proves the same.* The single-party
vertical disclosure and the multi-party horizontal disclosure become **one theorem**:
the dial law holds uniformly over an abstract verifier set, single (`Fin 1` = svenvs's
lone judge) or many (`Fintype ι` = dregg2's knowers), because each verifier learns only
*its own* dial position, independent of how many there are.

It EXTENDS `Metatheory.ConstructiveKnowledge` (`EpistemicPosition`, `Disclosure`,
`verifier_learns_only_acceptance`, `content_not_reached_from_acceptance`): the `Dial`'s
bottom `acceptanceOnly` IS the zero-knowledge position of that module
(`zk_is_dial_bottom`).

DISCIPLINE (candidate-independent, faithful Props): every carrier is abstract; the dial
is an honest `LinearOrder`/`BoundedOrder`. The PROVED keystones are pinned with
`#assert_axioms` (kernel-clean: only `propext`/`Classical.choice`/`Quot.sound`). The one
genuinely-cryptographic residue — that the *order* between positions reflects an actual
computational indistinguishability — is an honest `-- OPEN:` resting on the `Disclosure`
separation *parameter*, never an `axiom`/`admit`/`sorry`-alias.
-/
import Dregg2.Laws
import Dregg2.Tactics
import Metatheory.ConstructiveKnowledge
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Hom.Basic

namespace Metatheory

open Dregg2.Laws

universe u v w

/-! # §1. The dial — a bounded chain of disclosure positions

The dial is a *totally ordered* chain of how-much-a-verifier-learns positions. The top,
`fullDisclosure`, hands over cleartext and the whole trace; the middle, `selective`,
hands over chosen facts and the conclusion; the bottom, `acceptanceOnly`, hands over a
single bit — *it verifies*. "Turning the dial down" is descending this chain; the law to
come is that descending reveals strictly less while leaving WHETHER it verifies fixed. -/

/-- **`Dial`** — the three canonical positions of the unified epistemic dial, top-down.

This is a single chain `acceptanceOnly < selective < fullDisclosure`. It is the COMMON
refinement: svenvs's two-point channel and dregg2's three modes both land here (§4). We
give it a genuine `LinearOrder` + `BoundedOrder` below; nothing is `Nat`-for-semantics —
the order is the *meaning* (more disclosure is higher). -/
inductive Dial where
  /-- **One bit.** The verifier learns ONLY acceptance — that the statement is true. The
  zero-knowledge floor; svenvs's *non-disclose*, dregg2's *Fully-Private*. -/
  | acceptanceOnly
  /-- **Chosen facts + the conclusion.** The verifier learns a selected disclosure and the
  result, but not the full witness/trace. dregg2's *Selective*. -/
  | selective
  /-- **Cleartext + trace.** The verifier learns the full content and execution trace.
  svenvs's *disclose*; dregg2's *Trusted*. -/
  | fullDisclosure
  deriving DecidableEq, Repr

namespace Dial

/-- Rank a position by *how much is learned* (`0` = one bit, `2` = full). The order is
defined as the pullback of this rank along `≤` on `Nat`; the rank is an order-isomorphism
onto `{0,1,2}` and exists ONLY to transport `Nat`'s `LinearOrder` honestly — every law is
then stated on `Dial` itself, never on the `Nat`. -/
def rank : Dial → Nat
  | acceptanceOnly => 0
  | selective      => 1
  | fullDisclosure => 2

theorem rank_injective : Function.Injective rank := by
  intro a b h; cases a <;> cases b <;> simp_all [rank]

/-- **The dial is a `LinearOrder`** — a genuine total chain of disclosure, PROVED. The
positions really line up `acceptanceOnly ≤ selective ≤ fullDisclosure` with nothing
incomparable: there is a single axis of "how much the verifier learns." Defined by lifting
`Nat`'s order along the injective `rank` — the standard, fully-provable construction. -/
instance : LinearOrder Dial := LinearOrder.lift' rank rank_injective

/-- `a ≤ b` on the dial is exactly `rank a ≤ rank b` (the lift is definitional). -/
theorem le_iff_rank {a b : Dial} : a ≤ b ↔ a.rank ≤ b.rank := Iff.rfl

/-- **The dial is bounded** — `acceptanceOnly` is the floor (`⊥`), `fullDisclosure` the
ceiling (`⊤`), PROVED. The zero-knowledge bottom is the genuine least element: you cannot
disclose *less* than the single acceptance bit. -/
instance : BoundedOrder Dial where
  top := fullDisclosure
  bot := acceptanceOnly
  le_top a := by show a.rank ≤ rank fullDisclosure; cases a <;> simp [rank]
  bot_le a := by show rank acceptanceOnly ≤ a.rank; cases a <;> simp [rank]

@[simp] theorem bot_eq : (⊥ : Dial) = acceptanceOnly := rfl
@[simp] theorem top_eq : (⊤ : Dial) = fullDisclosure := rfl

/-- `acceptanceOnly` is *strictly* below `selective` (the chain is non-degenerate). -/
theorem acceptanceOnly_lt_selective : acceptanceOnly < selective := by
  rw [lt_iff_le_and_ne, le_iff_rank]; exact ⟨by simp [rank], by simp⟩

/-- `selective` is *strictly* below `fullDisclosure` (the chain is non-degenerate). -/
theorem selective_lt_fullDisclosure : selective < fullDisclosure := by
  rw [lt_iff_le_and_ne, le_iff_rank]; exact ⟨by simp [rank], by simp⟩

end Dial

#assert_axioms Dial.rank_injective
#assert_axioms Dial.acceptanceOnly_lt_selective
#assert_axioms Dial.selective_lt_fullDisclosure

/-! # §2. `DiscloseAt` and the monotone-information law

A *verification event* is anything that, at a given dial position, exposes some quantum of
information to the verifier. We model the information leaked at a position abstractly as a
monotone map `leaked : Dial → Info` into an order of "information sets" (`I`, an abstract
order where `≤` is "leaks no more than"). The dial's defining law is then two-fold:

  (a) **monotone information**: a lower dial position leaks `≤` information; and
  (b) **acceptance invariant**: WHETHER it verifies is *independent* of the position —
      turning the dial down changes only what *else* is learned.

Crucially, (b) is NOT made true by fiat (a bare `Prop` field cannot depend on `d`, which
would make the invariant `Iff.rfl`-vacuous). We give `accepts : Dial → Prop` a *genuine
position index* — a verifier is, a priori, free to accept differently at different
disclosure levels — and pin its position-independence to the underlying verify seam:
acceptance at every notch is exactly `Discharged p w` (the position-independent golden
oracle of `Dregg2.Laws`). The invariant theorem then has real content: it discharges the
position-indexed `accepts d₁ ↔ accepts d₂` *through* the verifier seam, not by reflexivity.
This is the faithful "proves the same while revealing less": the SAME witness discharges
the SAME predicate regardless of how much else the verifier is shown. -/

/-- **A disclosure schedule on the dial.** Parameterised by an abstract order of
information `I` (`a ≤ b` = "`a` leaks no more than `b`") and the verify seam `Verifiable P W`.

* `leaked d` — the information a verifier learns at dial position `d` (`mono`: descending
  the dial never *increases* what is leaked);
* `accepts d` — whether the statement verifies *as seen at position `d`*. A priori this is
  a genuine function of `d` (a verifier could, in a broken model, accept differently when
  shown more); we do NOT assume it constant.
* `pred`/`wit` — the predicate and witness underlying the verification;
* `accepts_eq` — the **position-independence law as a hypothesis on the verifier**:
  acceptance at every notch is exactly `Discharged pred wit`. This is the honest content —
  the verifier consults the witness, never the disclosure level — from which the
  acceptance-invariant is *derived* (not assumed). -/
structure DiscloseAt (I : Type u) (P W : Type u) [Preorder I] [Verifiable P W] where
  /-- What the verifier learns at each dial position (more disclosure ⇒ ≥ information). -/
  leaked : Dial → I
  /-- Descending the dial leaks no more: `d₁ ≤ d₂ → leaked d₁ ≤ leaked d₂`. -/
  mono : Monotone leaked
  /-- The predicate under verification. -/
  pred : P
  /-- The witness offered for it. -/
  wit : W
  /-- WHETHER the statement verifies, *as a function of the dial position* — a priori free
  to vary; pinned to the verify seam by `accepts_eq`. -/
  accepts : Dial → Prop
  /-- **The verifier ignores the dial**: at every position, acceptance is exactly the
  position-independent golden-oracle check `Discharged pred wit`. The honest carrier of the
  acceptance-invariant — the verifier consults the witness, never the disclosure level. -/
  accepts_eq : ∀ d, accepts d ↔ Discharged pred wit

namespace DiscloseAt

variable {I P W : Type u} [Preorder I] [Verifiable P W]

/-- **Monotone-information law — PROVED, kernel-clean.** Turning the dial *down*
(`d₁ ≤ d₂`) leaks no more information (`leaked d₁ ≤ leaked d₂`). This is the dial's whole
point as an information channel: a lower resolution is a *coarsening*. -/
theorem leak_mono (S : DiscloseAt I P W) {d₁ d₂ : Dial} (h : d₁ ≤ d₂) :
    S.leaked d₁ ≤ S.leaked d₂ :=
  S.mono h

/-- **The floor leaks least — PROVED, kernel-clean.** At the zero-knowledge bottom the
verifier learns the minimum: `leaked ⊥ ≤ leaked d` for every position `d`. -/
theorem leak_bot_le (S : DiscloseAt I P W) (d : Dial) :
    S.leaked ⊥ ≤ S.leaked d :=
  S.mono bot_le

/-- **The acceptance invariant — `accepts_invariant_under_dial`, PROVED, kernel-clean.**
WHETHER the statement verifies is the *same* fact at any two positions: `accepts d₁ ↔
accepts d₂`. This is NOT reflexivity — `accepts` is a genuine function of the dial — it is
*derived* by routing both sides through the position-independent verify seam: each notch's
acceptance equals `Discharged pred wit`, so all notches agree. Turning the dial does not
change acceptance, only what else is learned, BECAUSE the verifier consults the witness and
never the disclosure level. -/
theorem accepts_invariant_under_dial (S : DiscloseAt I P W) (d₁ d₂ : Dial) :
    S.accepts d₁ ↔ S.accepts d₂ :=
  (S.accepts_eq d₁).trans (S.accepts_eq d₂).symm

/-- **Acceptance is preserved exactly as one descends — PROVED, kernel-clean.** If it
accepts at `d₂` it accepts at every lower `d₁ ≤ d₂`, and conversely — the operational
"proves the same while reveals less." A direct corollary of the invariant (here the
ordering hypothesis is genuinely irrelevant: acceptance is position-independent in *both*
directions, which is exactly the strength of the claim). -/
theorem accepts_preserved_down (S : DiscloseAt I P W) {d₁ d₂ : Dial} (_h : d₁ ≤ d₂) :
    S.accepts d₁ ↔ S.accepts d₂ :=
  accepts_invariant_under_dial S d₁ d₂

/-- **The acceptance bit is exactly the golden-oracle check — PROVED, kernel-clean.** At
the zero-knowledge floor the single bit the verifier learns IS `Discharged pred wit`: the
floor accepts iff the witness discharges the predicate, with nothing else disclosed. This
is the bridge that makes the dial's bottom the realizability `Holds` check of
`ConstructiveKnowledge` (§6). -/
theorem accepts_bot_iff_discharged (S : DiscloseAt I P W) :
    S.accepts ⊥ ↔ Discharged S.pred S.wit :=
  S.accepts_eq ⊥

end DiscloseAt

#assert_axioms DiscloseAt.leak_mono
#assert_axioms DiscloseAt.leak_bot_le
#assert_axioms DiscloseAt.accepts_invariant_under_dial
#assert_axioms DiscloseAt.accepts_preserved_down
#assert_axioms DiscloseAt.accepts_bot_iff_discharged

/-! # §3. The two mode systems — svenvs (2-point) and dregg2 (3-point)

The unification keystone needs the two *named* mode systems as honest carriers. svenvs's
testimony channel has two points; dregg2 has three. We give each a `LinearOrder` (its own
native order of "how much is disclosed") so that "monotone order-embedding into the dial"
is a statement about genuine ordered structures, not a renaming. -/

/-- **svenvs's two-point testimony channel** — the lone judge either is told the witness
(`disclose`) or it is not (`nonDisclose`, *"the small thing may speak for itself, never be
seized"*). Ordered: `nonDisclose < disclose`. -/
inductive Svenvs where
  /-- The witness is withheld; the judge learns only that testimony was accepted. -/
  | nonDisclose
  /-- The witness is disclosed in the clear to the judge. -/
  | disclose
  deriving DecidableEq, Repr

namespace Svenvs
def rank : Svenvs → Nat | nonDisclose => 0 | disclose => 1
theorem rank_injective : Function.Injective rank := by
  intro a b h; cases a <;> cases b <;> simp_all [rank]
instance : LinearOrder Svenvs := LinearOrder.lift' rank rank_injective
theorem le_iff_rank {a b : Svenvs} : a ≤ b ↔ a.rank ≤ b.rank := Iff.rfl
theorem nonDisclose_lt_disclose : nonDisclose < disclose := by
  rw [lt_iff_le_and_ne, le_iff_rank]; exact ⟨by simp [rank], by simp⟩
end Svenvs

/-- **dregg2's three privacy modes** — `fullyPrivate` (one acceptance bit), `selective`
(chosen facts + conclusion), `trusted` (full cleartext + trace). Ordered by disclosure:
`fullyPrivate < selective < trusted`. -/
inductive Dregg2Mode where
  /-- Fully-Private: the verifier learns one bit — it verifies. -/
  | fullyPrivate
  /-- Selective: chosen facts and the conclusion are disclosed. -/
  | selective
  /-- Trusted: the full cleartext and execution trace are disclosed. -/
  | trusted
  deriving DecidableEq, Repr

namespace Dregg2Mode
def rank : Dregg2Mode → Nat | fullyPrivate => 0 | selective => 1 | trusted => 2
theorem rank_injective : Function.Injective rank := by
  intro a b h; cases a <;> cases b <;> simp_all [rank]
instance : LinearOrder Dregg2Mode := LinearOrder.lift' rank rank_injective
theorem le_iff_rank {a b : Dregg2Mode} : a ≤ b ↔ a.rank ≤ b.rank := Iff.rfl
end Dregg2Mode

/-! # §4. The unification keystone — both mode systems embed into the one dial

`dial_unifies_single_and_multi_party`: svenvs's `{nonDisclose, disclose}` AND dregg2's
`{fullyPrivate, selective, trusted}` are **both monotone order-embeddings into `Dial`**,
each preserving the acceptance-invariant. The same dial at two resolutions: svenvs reads
the two extreme notches; dregg2 reads all three. -/

/-- svenvs ↪ dial: `nonDisclose ↦ acceptanceOnly` (the ZK floor), `disclose ↦
fullDisclosure` (cleartext). The two-point channel reads the dial's two *extremes*. -/
def svenvsToDial : Svenvs → Dial
  | Svenvs.nonDisclose => Dial.acceptanceOnly
  | Svenvs.disclose    => Dial.fullDisclosure

/-- dregg2 ↪ dial: mode-for-position, the identity-of-meaning between the three modes and
the three notches. dregg2 reads the *whole* dial. -/
def dregg2ToDial : Dregg2Mode → Dial
  | Dregg2Mode.fullyPrivate => Dial.acceptanceOnly
  | Dregg2Mode.selective    => Dial.selective
  | Dregg2Mode.trusted      => Dial.fullDisclosure

/-- **svenvs's embedding is a strictly-monotone order-embedding — PROVED, kernel-clean.**
`a ≤ b ↔ svenvsToDial a ≤ svenvsToDial b`: the lone judge's two-point order is faithfully
the dial restricted to its two extremes. -/
theorem svenvsToDial_orderEmbedding (a b : Svenvs) :
    a ≤ b ↔ svenvsToDial a ≤ svenvsToDial b := by
  cases a <;> cases b <;>
    simp only [svenvsToDial, Svenvs.le_iff_rank, Dial.le_iff_rank, Svenvs.rank, Dial.rank] <;>
    decide

/-- **svenvs's embedding, packaged as a Mathlib `OrderEmbedding`** (the structured form). -/
def svenvsEmb : Svenvs ↪o Dial where
  toFun := svenvsToDial
  inj' := by intro a b h; cases a <;> cases b <;> simp_all [svenvsToDial]
  map_rel_iff' := by intro a b; exact (svenvsToDial_orderEmbedding a b).symm

/-- **dregg2's embedding is a strictly-monotone order-embedding — PROVED, kernel-clean.**
`a ≤ b ↔ dregg2ToDial a ≤ dregg2ToDial b`: the three privacy modes ARE the three dial
notches, order and all. -/
theorem dregg2ToDial_orderEmbedding (a b : Dregg2Mode) :
    a ≤ b ↔ dregg2ToDial a ≤ dregg2ToDial b := by
  cases a <;> cases b <;>
    simp [dregg2ToDial, Dregg2Mode.le_iff_rank, Dial.le_iff_rank, Dregg2Mode.rank,
          Dial.rank]

/-- **dregg2's embedding, packaged as a Mathlib `OrderEmbedding`.** -/
def dregg2Emb : Dregg2Mode ↪o Dial where
  toFun := dregg2ToDial
  inj' := by intro a b h; cases a <;> cases b <;> simp_all [dregg2ToDial]
  map_rel_iff' := by intro a b; exact (dregg2ToDial_orderEmbedding a b).symm

/-- The acceptance-invariant transported across an embedding `f : M → Dial`: for any
disclosure schedule on the dial, WHETHER it verifies is identical whether we read it at the
dial notch of `m₁` or of `m₂`. This is genuine content — `accepts` is a real function of the
dial position — discharged through the verify seam (§2), NOT by reflexivity. Both mode
systems preserve it because the dial does. -/
def PreservesAcceptance {M : Type v} {I P W : Type u} [Preorder I] [Verifiable P W]
    (f : M → Dial) (S : DiscloseAt I P W) : Prop :=
  ∀ m₁ m₂ : M, S.accepts (f m₁) ↔ S.accepts (f m₂)

/-- Any embedding into the dial preserves acceptance — because acceptance on the dial is
position-independent (§2). The honest derivation, shared by both mode embeddings. -/
theorem preservesAcceptance_of_embed {M : Type v} {I P W : Type u}
    [Preorder I] [Verifiable P W] (f : M → Dial) (S : DiscloseAt I P W) :
    PreservesAcceptance f S :=
  fun m₁ m₂ => DiscloseAt.accepts_invariant_under_dial S (f m₁) (f m₂)

/-- **`dial_unifies_single_and_multi_party` — THE unification keystone, PROVED,
kernel-clean.**

svenvs's single-party two-point `{nonDisclose, disclose}` AND dregg2's multi-party
three-point `{fullyPrivate, selective, trusted}` are **both monotone order-embeddings into
the one `Dial`**, and BOTH preserve the acceptance-invariant of any disclosure schedule.
This is "the same dial at different resolutions": the single-party vertical disclosure and
the multi-party horizontal disclosure are facets of *one* ordered structure.

The four conjuncts: (1) svenvs embeds order-faithfully; (2) dregg2 embeds order-faithfully;
(3) svenvs preserves acceptance; (4) dregg2 preserves acceptance — (3),(4) discharged
through the verify seam, not reflexivity. -/
theorem dial_unifies_single_and_multi_party
    {I P W : Type u} [Preorder I] [Verifiable P W] (S : DiscloseAt I P W) :
    (∀ a b : Svenvs, a ≤ b ↔ svenvsToDial a ≤ svenvsToDial b) ∧
    (∀ a b : Dregg2Mode, a ≤ b ↔ dregg2ToDial a ≤ dregg2ToDial b) ∧
    PreservesAcceptance svenvsToDial S ∧
    PreservesAcceptance dregg2ToDial S :=
  ⟨svenvsToDial_orderEmbedding, dregg2ToDial_orderEmbedding,
   preservesAcceptance_of_embed svenvsToDial S,
   preservesAcceptance_of_embed dregg2ToDial S⟩

/-- **The two embeddings AGREE at the shared extremes — PROVED, kernel-clean.** Where the
coarse (svenvs) and fine (dregg2) dials name the same physical notch, they map to the same
dial position: both floors land on `acceptanceOnly`, both ceilings on `fullDisclosure`.
This is what makes "the same dial at two resolutions" literal rather than analogical. -/
theorem embeddings_agree_at_extremes :
    svenvsToDial Svenvs.nonDisclose = dregg2ToDial Dregg2Mode.fullyPrivate ∧
    svenvsToDial Svenvs.disclose = dregg2ToDial Dregg2Mode.trusted :=
  ⟨rfl, rfl⟩

#assert_axioms svenvsToDial_orderEmbedding
#assert_axioms dregg2ToDial_orderEmbedding
#assert_axioms dial_unifies_single_and_multi_party
#assert_axioms embeddings_agree_at_extremes

/-! # §5. Single ⊕ multi-party as one — party-count agnosticism

The dial law is parameterised by a *verifier set* `ι` (a `Fintype`): `Fin 1` is svenvs's
lone judge, an arbitrary `Fintype ι` is dregg2's many knowers. The law holds UNIFORMLY in
`ι` because each verifier learns only its OWN dial position, independent of how many
verifiers there are. Single-party and multi-party are *one* theorem. -/

/-- **A multi-party disclosure schedule.** Each verifier `i : ι` sits at its own dial
position `pos i` and learns `leaked (pos i)` from a *shared* disclosure schedule `S`. The
key independence is structural: verifier `i`'s leaked information is a function of `pos i`
ALONE — not of `ι`, not of the other verifiers' positions. -/
structure PartySchedule (ι : Type v) (I P W : Type u) [Preorder I] [Verifiable P W] where
  /-- The disclosure schedule on the dial (shared across all verifiers). -/
  S : DiscloseAt I P W
  /-- Each verifier's dial position. -/
  pos : ι → Dial

namespace PartySchedule

variable {ι : Type v} {I P W : Type u} [Preorder I] [Verifiable P W]

/-- What verifier `i` learns: `leaked` at *its own* position. -/
def learnedBy (PS : PartySchedule ι I P W) (i : ι) : I := PS.S.leaked (PS.pos i)

/-- **`dial_is_party_count_agnostic` — single ⊕ multi-party as ONE law, PROVED,
kernel-clean.** For ANY finite verifier set `ι` and any schedule:

  (1) each verifier learns *only* its own position's disclosure (`learnedBy i = leaked
      (pos i)`) — independent of `ι` and of the other verifiers' positions;
  (2) the monotone-information law holds per-verifier: if `i`'s notch is `≤` `j`'s, then `i`
      learns `≤` what `j` learns;
  (3) acceptance is the *same fact* for every pair of verifiers regardless of their notches
      (routed through the verify seam, §2) — every party agrees on WHETHER it verifies even
      while disagreeing on how much else they see.

The cardinality of `ι` never appears — `Fin 1` (svenvs's lone judge) and any `Fintype ι`
(dregg2's many knowers) obey the identical law. This is single ⊕ multi-party as one. -/
theorem dial_is_party_count_agnostic [Fintype ι] (PS : PartySchedule ι I P W) :
    (∀ i : ι, PS.learnedBy i = PS.S.leaked (PS.pos i)) ∧
    (∀ i j : ι, PS.pos i ≤ PS.pos j → PS.learnedBy i ≤ PS.learnedBy j) ∧
    (∀ i j : ι, PS.S.accepts (PS.pos i) ↔ PS.S.accepts (PS.pos j)) :=
  ⟨fun _ => rfl, fun _ _ hij => PS.S.mono hij,
   fun i j => DiscloseAt.accepts_invariant_under_dial PS.S (PS.pos i) (PS.pos j)⟩

/-- **Each verifier learns only its OWN position — PROVED, kernel-clean.** Verifier `i`'s
leaked information is determined by `pos i` and nothing else: two schedules that agree on
`i`'s position (even over different verifier sets) give `i` the same information. This is
the precise sense in which the multi-party channel is "many independent single-party
channels," collapsing single and multi into one. -/
theorem each_learns_only_own_position
    {ι' : Type w} (PS : PartySchedule ι I P W) (PS' : PartySchedule ι' I P W)
    (i : ι) (i' : ι') (hpos : PS.pos i = PS'.pos i') (hS : PS.S = PS'.S) :
    PS.learnedBy i = PS'.learnedBy i' := by
  unfold learnedBy; rw [hpos, hS]

/-- **The single-party instance is svenvs's lone judge — PROVED, kernel-clean.** With
`ι := Fin 1` there is exactly one verifier; the party-agnostic law specialises to it with
no change, recovering svenvs's vertical single-party disclosure as the `Fintype.card = 1`
case of the uniform law. -/
theorem single_party_is_fin_one (PS : PartySchedule (Fin 1) I P W) :
    Fintype.card (Fin 1) = 1 ∧
    (∀ i : Fin 1, PS.learnedBy i = PS.S.leaked (PS.pos i)) :=
  ⟨Fintype.card_fin 1, fun _ => rfl⟩

end PartySchedule

#assert_axioms PartySchedule.dial_is_party_count_agnostic
#assert_axioms PartySchedule.each_learns_only_own_position
#assert_axioms PartySchedule.single_party_is_fin_one

/-! # §6. Bottom = ZK — the dial floor IS `verifier_learns_only_acceptance`

`zk_is_dial_bottom`: the dial's `acceptanceOnly` floor is the *same position* as the
zero-knowledge `acceptancePos` of `ConstructiveKnowledge`. Any `Disclosure` whose
`acceptancePos`/`contentPos` are placed on the dial — acceptance at the floor, content
above it — has its verifier provably confined below content, which is exactly
`verifier_learns_only_acceptance`. -/

/-- A `Disclosure` (from `ConstructiveKnowledge`) *carried on the dial*: its acceptance
position is the dial's bottom `acceptanceOnly`, and content sits strictly above. The
`Disclosure` order is `Dial`; its separation hypotheses (`accept_le_content`,
`accept_ne_content`) become facts about the dial chain. -/
def dialDisclosure : Disclosure Dial where
  acceptancePos := Dial.acceptanceOnly
  contentPos := Dial.fullDisclosure
  accept_le_content := by rw [Dial.le_iff_rank]; simp [Dial.rank]
  accept_ne_content := by simp

/-- **`zk_is_dial_bottom` — the ZK position IS the dial floor, PROVED, kernel-clean.** The
`acceptanceOnly` bottom of the dial is *definitionally* the `acceptancePos` of the
dial-carried `Disclosure`, and a verifier there learns only acceptance — strictly below
content — which is exactly `ConstructiveKnowledge.verifier_learns_only_acceptance` applied
to the dial. The zero-knowledge floor of the unified dial and the standalone ZK
epistemic-boundary law are the same fact. -/
theorem zk_is_dial_bottom :
    dialDisclosure.acceptancePos = (⊥ : Dial) ∧
    dialDisclosure.acceptancePos < dialDisclosure.contentPos :=
  ⟨rfl, verifier_learns_only_acceptance dialDisclosure⟩

/-- **Content is unreachable from the dial floor — PROVED, kernel-clean.** The
complementary half: a verifier pinned at `acceptanceOnly` cannot climb to content
(`¬ contentPos ≤ acceptancePos`), i.e. it learns NOT the witness content. This is
`content_not_reached_from_acceptance` read on the dial — the zero-knowledge guarantee at
the bottom notch. -/
theorem dial_bottom_reaches_not_content :
    ¬ dialDisclosure.contentPos ≤ dialDisclosure.acceptancePos :=
  content_not_reached_from_acceptance dialDisclosure

#assert_axioms zk_is_dial_bottom
#assert_axioms dial_bottom_reaches_not_content

/-
OPEN (the crypto-indistinguishability grounding the dial order). Every law above pins the
*epistemic order* faithfully — the dial is a genuine bounded chain, both mode systems embed
into it monotonically, acceptance is position-independent, and the floor is the ZK
acceptance position. The single remaining, genuinely-cryptographic obligation is that this
ORDER REFLECTS AN ACTUAL INDISTINGUISHABILITY: that a verifier confined to a lower dial
position cannot *computationally* distinguish/extract the information notionally available
only above it (simulator existence, computational indistinguishability of real vs.
simulated transcripts at each notch). That is a circuit/cryptographic obligation, NEVER
merged into this Lean order-law (cf. `ConstructiveKnowledge` §2 / `Dregg2.Boundary` §8: the
`Verify` oracle's crypto-soundness is a separate circuit obligation). It enters here only
through the `Disclosure` separation *parameter* that `dialDisclosure` instantiates — the
metatheory says "*if* the notches separate the disclosure order thus, *then* the verifier
is epistemically confined," and the crypto layer discharges the antecedent. This is the
legitimate ZK-indistinguishability residue; it is NOT discharged by any `axiom`/`sorry`
here — it lives, faithfully, as the hypothesis structure of `Disclosure`. -/

end Metatheory
