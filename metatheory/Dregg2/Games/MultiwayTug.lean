/-
# Dregg2.Games.MultiwayTug — a VERIFIED pure-transition spec for the multiway-tug card game.

Design lineage: the mechanics are derived from **Hanamikoji** (Kota Nakayama). The *shipped*
dregg game is the original re-theming "multiway-tug"; only the name/theme differ — the rules
modelled here are the Hanamikoji rules (2 players, 7 "guild" rows with charm values
`[2,2,2,3,3,4,5]` = 21, a 21-card deck holding `charm g` copies of each row `g`, a hidden
6-card hand, four once-per-round actions Secret / Discard / Gift / Competition, control of a
row goes to whoever placed MORE on it, win at ≥ 11 charm OR ≥ 4 rows).

## ⚑ THE ENGINE IS `I-CUT-YOU-CHOOSE` — restored (2026-07-25)

Hanamikoji's whole engine is a cake-cutting dilemma: on Gift you REVEAL three favors and the
**opponent takes one**; on Competition you reveal four as **two pairs you chose** and the
opponent **takes a pair**. The actor cuts; the other seat chooses.

This model USED TO PRE-FOLD that choice — `gift (self₁ self₂ other)` let the acting player
declare who got what, and there was no opponent step anywhere in the transition system. With
the split pre-folded there is no dilemma and (given a scripted mover) no decision at all: a
whole match was a pure function of the deal seed. That is fixed here. A `Gift`/`Competition`
action now only PRESENTS cards; they land in escrow as a `pending : Option Offer`; and the
OTHER seat's `Response` decides the split. The transition alphabet is `Move := act | respond`.

The three decisions a player now owns, each with a theorem below saying it is real:

  1. **WHICH action, WHEN** — `legalB` only requires the kind unused, and
     `every_action_order_is_feasible` proves ALL 24 orderings are card-feasible, so the order
     is a free choice over a fully-available space (the Rust engine used to hardcode ONE).
  2. **THE CUT** — which cards to present, and (Competition) how to PAIR them.
     `comp_balanced_cut_dominates` / `gift_modest_cut_dominates` prove the guaranteed swing
     depends on the cut, so the cut is a decision with a wrong answer.
  3. **THE CHOICE** — `respond_decides_the_round` exhibits one pending offer whose two
     responses hand the round to DIFFERENT players. That is the falsifier for "a player
     decides nothing", discharged as a theorem.

## What is PROVEN here (the pure model — real, non-vacuous, `#assert_axioms`-clean)

  1. **CONSERVATION** (`conservation`, `conservation_response`, `conservation_move`) — the total
     card multiset (`removed + deck + hands + secrets + discard-piles + placed + escrow`) is
     INVARIANT under every move. Genuine multiset arithmetic (`Multiset.sub_add_cancel`), NOT
     `by decide` on a toy. Lifted to whole executions along the `Boundary` keystone
     (`conservation_along_run`). The escrow is DERIVED from `pending` (`pendingCards`), so
     "an offer's cards are somewhere" is definitional, not an invariant to maintain.
  2. **ONE-ACTION-PER-ROUND** (`used_monotone`, `legal_needs_unused`) — a monotone used-set.
     A `Response` consumes NO flag (responding is not one of your four actions), which is why
     `Move` splits into `act`/`respond` rather than adding a fifth `ActionKind`.
  3. **THE OFFER INTERLOCK** (`pending_blocks_actions`, `respond_needs_pending`,
     `respond_not_by_proposer`) — while an offer is pending NOTHING but a response is legal; a
     response with no pending offer is refused; and **the proposer cannot answer their own
     offer**. That last one is the anti-self-deal tooth: without it I-cut-you-choose silently
     collapses back into the pre-folded gift this file just deleted.
  4. **SCORING** — control goes to whoever placed more (`control_correct`); raw placement counts
     only accrue (`geishaCount_mono`); and the Secret card IS scored (`secret_is_scored`).
  5. **WIN-SAFETY** — `Won` (≥ 11 charm OR ≥ 4 rows) as a `Good`-style predicate, plus the
     adjudicated `roundWinner` (§7B) that took draws from 66.1% to 5.1%.
-/
import Dregg2.Boundary
import Mathlib.Data.Multiset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases

namespace Dregg2.Games.MultiwayTug

open scoped BigOperators

/-! ## 1. Rows, charm, players, actions -/

/-- A **guild row**, indexed `0..6`. A card is just the row it scores for. -/
abbrev Geisha := Fin 7

/-- The **charm value** of each row `[2,2,2,3,3,4,5]` (Σ = 21). This is ALSO the number of
copies of that row's card in the deck (face-value copies), so the full deck has 21 cards. -/
def charm : Geisha → ℕ := ![2, 2, 2, 3, 3, 4, 5]

/-- The two players. -/
inductive Player where
  | p1 | p2
deriving DecidableEq, Repr

/-- The opponent. -/
def Player.other : Player → Player
  | .p1 => .p2
  | .p2 => .p1

@[simp] theorem Player.other_p1 : Player.other .p1 = .p2 := rfl
@[simp] theorem Player.other_p2 : Player.other .p2 = .p1 := rfl
@[simp] theorem Player.other_other (p : Player) : p.other.other = p := by cases p <;> rfl
theorem Player.other_ne (p : Player) : p.other ≠ p := by cases p <;> decide

/-- The four once-per-round **action kinds** (the used-flag domain). A response is NOT one of
these — responding to the opponent's offer is forced, not one of your four actions. -/
inductive ActionKind where
  | secretK | discardK | giftK | competitionK
deriving DecidableEq, Repr

/-- A concrete **action** (the flag-consuming half of a move).

⚑ `offerGift`/`offerComp` carry ONLY the presented cards — no self/other split. Who gets what
is the OTHER seat's `Response`. (The deleted pre-folded forms were `gift self₁ self₂ other` and
`competition self₁ self₂ other₁ other₂`.) `offerComp` carries the cards ALREADY PAIRED
(`a₀ a₁ | b₀ b₁`): the pairing IS the cut, so it is part of the action, not a derived detail. -/
inductive Action where
  /-- Secret one card (set aside face-down; scored at round end). -/
  | secret (c : Geisha)
  /-- Discard two cards (removed from the round; never scored). -/
  | discard (c₁ c₂ : Geisha)
  /-- Gift: PRESENT three favors. The opponent takes one; you keep the other two. -/
  | offerGift (c₀ c₁ c₂ : Geisha)
  /-- Competition: PRESENT two pairs. The opponent takes a pair; you keep the other. -/
  | offerComp (a₀ a₁ b₀ b₁ : Geisha)
deriving DecidableEq, Repr

/-- The action-kind of an action (for the used-flag). -/
def Action.kind : Action → ActionKind
  | .secret _ => .secretK
  | .discard _ _ => .discardK
  | .offerGift _ _ _ => .giftK
  | .offerComp _ _ _ _ => .competitionK

/-- A **pending offer** — cards revealed on the table, awaiting the other seat's choice. It
records WHO cut, so `respond_not_by_proposer` can refuse a self-deal. -/
inductive Offer where
  /-- Three favors presented by `proposer`; the responder takes exactly one. -/
  | gift (proposer : Player) (c₀ c₁ c₂ : Geisha)
  /-- Two pairs presented by `proposer`; the responder takes exactly one pair. -/
  | comp (proposer : Player) (a₀ a₁ b₀ b₁ : Geisha)
deriving DecidableEq, Repr

/-- Who cut. -/
def Offer.proposer : Offer → Player
  | .gift p _ _ _ => p
  | .comp p _ _ _ _ => p

/-- The cards held in escrow by a pending offer. -/
def Offer.cards : Offer → Multiset Geisha
  | .gift _ c₀ c₁ c₂ => {c₀} + {c₁} + {c₂}
  | .comp _ a₀ a₁ b₀ b₁ => {a₀} + {a₁} + {b₀} + {b₁}

/-- **The other seat's answer** — the choice this whole file exists to restore. -/
inductive Response where
  /-- Take presented favor `pick` of the three. -/
  | gift (pick : Fin 3)
  /-- Take presented pair `pick` of the two. -/
  | comp (pick : Fin 2)
deriving DecidableEq, Repr

/-- A response ANSWERS an offer only if it is of the matching shape (fail-closed). -/
def Offer.accepts : Offer → Response → Bool
  | .gift _ _ _ _, .gift _ => true
  | .comp _ _ _ _ _, .comp _ => true
  | _, _ => false

/-- The cards the RESPONDER takes for their own rows. A shape-mismatched response takes
nothing (fail-closed; `legalRespB` refuses it anyway). -/
def takerShare : Offer → Response → Multiset Geisha
  | .gift _ c₀ _ _, .gift 0 => {c₀}
  | .gift _ _ c₁ _, .gift 1 => {c₁}
  | .gift _ _ _ c₂, .gift 2 => {c₂}
  | .comp _ a₀ a₁ _ _, .comp 0 => {a₀} + {a₁}
  | .comp _ _ _ b₀ b₁, .comp 1 => {b₀} + {b₁}
  | _, _ => 0

/-- The cards left to the PROPOSER (the cutter keeps the side the taker declined). -/
def cutterShare : Offer → Response → Multiset Geisha
  | .gift _ _ c₁ c₂, .gift 0 => {c₁} + {c₂}
  | .gift _ c₀ _ c₂, .gift 1 => {c₀} + {c₂}
  | .gift _ c₀ c₁ _, .gift 2 => {c₀} + {c₁}
  | .comp _ _ _ b₀ b₁, .comp 0 => {b₀} + {b₁}
  | .comp _ a₀ a₁ _ _, .comp 1 => {a₀} + {a₁}
  | o, _ => o.cards

/-- **`share_split` — the escrow empties EXACTLY.** Whatever the response, the taker's share
plus the cutter's share is the whole offer: no favor is duplicated or stranded on the table.
Holds UNCONDITIONALLY (a shape-mismatched response gives the cutter everything), which is what
makes response-conservation a one-liner rather than an invariant to carry. -/
theorem share_split (o : Offer) (r : Response) :
    takerShare o r + cutterShare o r = o.cards := by
  cases o <;> cases r <;> rename_i k <;> fin_cases k <;>
    simp only [Fin.isValue, Fin.reduceFinMk, takerShare, cutterShare, Offer.cards, zero_add, add_zero] <;> ac_rfl

/-! ### The card-movement decomposition (destinations of an action's cards) -/

/-- Cards added to the acting player's **secret** pile. -/
def toSecret : Action → Multiset Geisha
  | .secret c => {c}
  | _ => 0

/-- Cards added to the acting player's **discard** pile. -/
def toDiscardPile : Action → Multiset Geisha
  | .discard c₁ c₂ => {c₁} + {c₂}
  | _ => 0

/-- Cards moved to the **escrow** (revealed on the table, awaiting the other seat's choice). -/
def toOffer : Action → Multiset Geisha
  | .offerGift c₀ c₁ c₂ => {c₀} + {c₁} + {c₂}
  | .offerComp a₀ a₁ b₀ b₁ => {a₀} + {a₁} + {b₀} + {b₁}
  | _ => 0

/-- The FULL multiset of cards the action removes from the acting player's hand. -/
def actionCards : Action → Multiset Geisha
  | .secret c => {c}
  | .discard c₁ c₂ => {c₁} + {c₂}
  | .offerGift c₀ c₁ c₂ => {c₀} + {c₁} + {c₂}
  | .offerComp a₀ a₁ b₀ b₁ => {a₀} + {a₁} + {b₀} + {b₁}

/-- The offer an action opens (`none` for the two private actions). -/
def offerOf (p : Player) : Action → Option Offer
  | .offerGift c₀ c₁ c₂ => some (.gift p c₀ c₁ c₂)
  | .offerComp a₀ a₁ b₀ b₁ => some (.comp p a₀ a₁ b₀ b₁)
  | _ => none

/-- The opened offer holds exactly the escrowed cards. -/
theorem offerOf_cards (p : Player) (a : Action) :
    (match offerOf p a with | none => 0 | some o => o.cards) = toOffer a := by
  cases a <;> rfl

/-- **The cards leaving the hand equal the cards arriving everywhere else.** -/
theorem actionCards_split (a : Action) :
    toSecret a + toDiscardPile a + toOffer a = actionCards a := by
  cases a <;>
    simp only [toSecret, toDiscardPile, toOffer, actionCards, add_zero, zero_add, add_assoc]

/-! ## 2. The game state -/

/-- The **multiway-tug state**. Every card lives in exactly one location; the ESCROW is derived
from `pending` (`pendingCards`), so a revealed-but-unresolved offer is not a zone that can drift
out of sync. `used` is the per-player per-action once-per-round flag; `turns` is the committed
turn stamp (8 actions + 4 responses in a full round). -/
structure GState where
  /-- The single face-down card removed at deal. -/
  removed : Multiset Geisha
  /-- The draw pile. -/
  deck : Multiset Geisha
  /-- Each player's hidden hand. -/
  hand : Player → Multiset Geisha
  /-- Each player's secret pile (scored at round end). -/
  secret : Player → Multiset Geisha
  /-- Each player's discard pile (out of the round). -/
  discardPile : Player → Multiset Geisha
  /-- Each player's placed cards (on the guild rows). -/
  placed : Player → Multiset Geisha
  /-- Once-per-round action flags. -/
  used : Player → ActionKind → Bool
  /-- ⚑ The pending offer: revealed favors awaiting the OTHER seat's choice. -/
  pending : Option Offer
  /-- Whose turn it is (to act, or — while `pending` — to respond). -/
  current : Player
  /-- The committed turn stamp (actions AND responses). -/
  turns : ℕ

/-- Sum of a per-player multiset over both players. -/
def sum2 (f : Player → Multiset Geisha) : Multiset Geisha := f .p1 + f .p2

/-- **The escrow** — the cards a pending offer holds on the table. Derived, so
"empty iff no offer is pending" is DEFINITIONAL rather than an invariant to prove. -/
def pendingCards (s : GState) : Multiset Geisha :=
  match s.pending with
  | none => 0
  | some o => o.cards

@[simp] theorem pendingCards_none {s : GState} (h : s.pending = none) : pendingCards s = 0 := by
  simp [pendingCards, h]

/-- The **total card multiset** (the conserved quantity), now including the escrow. -/
def totalCards (s : GState) : Multiset Geisha :=
  s.removed + s.deck + sum2 s.hand + sum2 s.secret + sum2 s.discardPile + sum2 s.placed
    + pendingCards s

/-! ## 3. The pure transitions — ACT and RESPOND -/

/-- Is the ACTION **legal**: the acting player is to move, **no offer is pending**, its kind is
unused this round, and its cards are in the acting player's hand.

⚑ The `pending.isNone` conjunct is the interlock: you cannot start a second offer, nor duck a
response by taking an unrelated action, while the table is waiting on you. -/
def legalB (s : GState) (p : Player) (a : Action) : Bool :=
  decide (s.current = p) && s.pending.isNone && (! s.used p a.kind)
    && decide (actionCards a ≤ s.hand p)

/-- The state update for a LEGAL action: move `actionCards a` out of the hand into secret /
discard / ESCROW, set the used-flag, stamp the turn, and pass the seat — to the responder if
this action opened an offer, to the next actor otherwise. Both are `p.other`. -/
def applyLegal (s : GState) (p : Player) (a : Action) : GState :=
  { s with
    hand := Function.update s.hand p (s.hand p - actionCards a)
    secret := Function.update s.secret p (s.secret p + toSecret a)
    discardPile := Function.update s.discardPile p (s.discardPile p + toDiscardPile a)
    used := Function.update s.used p (Function.update (s.used p) a.kind true)
    pending := offerOf p a
    current := p.other
    turns := s.turns + 1 }

/-- **`applyAction` — the ACT transition.** A legal action moves cards; an illegal action is a
no-op (fail-closed). Total and deterministic. -/
def applyAction (s : GState) (p : Player) (a : Action) : GState :=
  bif legalB s p a then applyLegal s p a else s

/-- Is the RESPONSE **legal**: an offer is pending, `p` is to move, **`p` is NOT the proposer**,
and the response matches the offer's shape.

⚑ `o.proposer = p.other` is the ANTI-SELF-DEAL tooth. Drop it and the cutter answers their own
cut — which is exactly the pre-folded `gift self₁ self₂ other` this file deleted. -/
def legalRespB (s : GState) (p : Player) (r : Response) : Bool :=
  match s.pending with
  | none => false
  | some o => decide (s.current = p) && decide (o.proposer = p.other) && o.accepts r

/-- The state update for a LEGAL response: the escrow empties onto the two boards — the
responder takes their share, the proposer keeps the rest — the offer closes, and the seat stays
with the responder (who now takes their OWN action; actions still alternate A,B,A,B). -/
def applyRespLegal (s : GState) (p : Player) (r : Response) : GState :=
  match s.pending with
  | none => s
  | some o =>
    { s with
      placed := Function.update
        (Function.update s.placed p (s.placed p + takerShare o r))
        p.other (s.placed p.other + cutterShare o r)
      pending := none
      current := p
      turns := s.turns + 1 }

/-- **`applyResponse` — the RESPOND transition.** The other seat's choice, as a real step of the
transition system. This is the step the shipped game did not have. -/
def applyResponse (s : GState) (p : Player) (r : Response) : GState :=
  bif legalRespB s p r then applyRespLegal s p r else s

/-- The transition alphabet: a flag-consuming ACTION, or a RESPONSE to a pending offer. -/
inductive Move where
  | act (a : Action)
  | respond (r : Response)
deriving DecidableEq, Repr

/-- **`applyMove` — the whole transition.** -/
def applyMove (s : GState) (p : Player) : Move → GState
  | .act a => applyAction s p a
  | .respond r => applyResponse s p r

/-- Determinism: `applyMove` is a function, so the successor is unique. -/
theorem applyMove_deterministic (s : GState) (p : Player) (m : Move) {n₁ n₂ : GState}
    (h₁ : n₁ = applyMove s p m) (h₂ : n₂ = applyMove s p m) : n₁ = n₂ :=
  h₁.trans h₂.symm

/-- Determinism of the act transition (kept for the AIR/leaf layer). -/
theorem applyAction_deterministic (s : GState) (p : Player) (a : Action) {n₁ n₂ : GState}
    (h₁ : n₁ = applyAction s p a) (h₂ : n₂ = applyAction s p a) : n₁ = n₂ :=
  h₁.trans h₂.symm

/-! ## 3B. THE OFFER INTERLOCK — the teeth that keep I-cut-you-choose from collapsing -/

/-- **`pending_blocks_actions`.** While an offer is pending NO action is legal, for EITHER
player. The table must be answered before play continues — the proposer cannot walk away from
their own cut, and the responder cannot duck it. -/
theorem pending_blocks_actions (s : GState) (p : Player) (a : Action) (o : Offer)
    (h : s.pending = some o) : legalB s p a = false := by
  simp [legalB, h]

/-- **`respond_needs_pending`.** A response with nothing on the table is refused — you cannot
conjure a share out of an offer that was never made. -/
theorem respond_needs_pending (s : GState) (p : Player) (r : Response) (h : s.pending = none) :
    legalRespB s p r = false := by
  simp [legalRespB, h]

/-- **`respond_not_by_proposer` (THE ANTI-SELF-DEAL TOOTH).** The player who CUT can never be
the player who CHOOSES. This is the theorem that makes the mechanic I-cut-YOU-choose rather
than the pre-folded self-dealt split the shipped game had. -/
theorem respond_not_by_proposer (s : GState) (p : Player) (r : Response) (o : Offer)
    (hp : s.pending = some o) (hself : o.proposer = p) : legalRespB s p r = false := by
  simp only [legalRespB, hp]
  have : ¬ (o.proposer = p.other) := by rw [hself]; exact fun h => Player.other_ne p h.symm
  simp [this]

/-- After an offer action, an offer IS pending — the escrow is really opened (non-vacuity of the
interlock: `pending_blocks_actions` is not guarding an always-`none` field). -/
theorem offer_opens_pending (s : GState) (p : Player) (c₀ c₁ c₂ : Geisha)
    (h : legalB s p (.offerGift c₀ c₁ c₂) = true) :
    (applyAction s p (.offerGift c₀ c₁ c₂)).pending = some (.gift p c₀ c₁ c₂) := by
  simp [applyAction, h, applyLegal, offerOf]

/-- After a legal response, the table is clear again. -/
theorem respond_closes_pending (s : GState) (p : Player) (r : Response)
    (h : legalRespB s p r = true) : (applyResponse s p r).pending = none := by
  simp only [applyResponse, h, cond_true, applyRespLegal]
  cases hp : s.pending with
  | none => simp [legalRespB, hp] at h
  | some o => simp

/-- On a legal action, `applyAction` IS `applyLegal`. -/
theorem applyAction_of_legal (s : GState) (p : Player) (a : Action) (h : legalB s p a = true) :
    applyAction s p a = applyLegal s p a := by
  simp only [applyAction, h, cond_true]

/-- On a legal response, `applyResponse` IS `applyRespLegal`. -/
theorem applyResponse_of_legal (s : GState) (p : Player) (r : Response)
    (h : legalRespB s p r = true) : applyResponse s p r = applyRespLegal s p r := by
  simp only [applyResponse, h, cond_true]

/-! ## 4. INVARIANT 1 — CONSERVATION -/

/-- The hand-move identity: removing `actionCards a` from a hand `m` (`actionCards a ≤ m`) and
re-adding the three destination shares recovers `m` exactly. -/
theorem hand_move {m : Multiset Geisha} (a : Action) (hle : actionCards a ≤ m) :
    m - actionCards a + toSecret a + toDiscardPile a + toOffer a = m := by
  have hsplit : ∀ g, Multiset.count g (toSecret a) + Multiset.count g (toDiscardPile a)
      + Multiset.count g (toOffer a) = Multiset.count g (actionCards a) := by
    intro g
    rw [← Multiset.count_add, ← Multiset.count_add, actionCards_split]
  ext g
  have hc : Multiset.count g (actionCards a) ≤ Multiset.count g m := Multiset.count_le_of_le g hle
  have hg := hsplit g
  simp only [Multiset.count_add, Multiset.count_sub]
  omega

/-- **`conservation` (INVARIANT 1, the ACT step).** The total card multiset is INVARIANT under
`applyAction`: cards only move between hand, secret, discard and ESCROW. Real multiset
arithmetic, for EVERY input (legal ⇒ genuine relocation; illegal ⇒ no-op). -/
theorem conservation (s : GState) (p : Player) (a : Action) :
    totalCards (applyAction s p a) = totalCards s := by
  by_cases hleg : legalB s p a = true
  · have hle : actionCards a ≤ s.hand p := by
      simp only [legalB, Bool.and_eq_true, decide_eq_true_eq] at hleg
      exact hleg.2
    have hnone : s.pending = none := by
      simp only [legalB, Bool.and_eq_true] at hleg
      exact Option.isNone_iff_eq_none.mp (by simpa using hleg.1.1.2)
    simp only [applyAction, hleg, cond_true, totalCards, applyLegal, sum2, pendingCards, hnone]
    rw [show (match offerOf p a with | none => (0 : Multiset Geisha) | some o => o.cards)
          = toOffer a from offerOf_cards p a]
    cases p <;>
      simp only [Function.update_apply, Player.other_p1, Player.other_p2, reduceCtorEq,
        reduceIte] <;>
      · conv_rhs => rw [← hand_move a hle]
        ac_rfl
  · simp only [Bool.not_eq_true] at hleg
    simp [applyAction, hleg]

/-- **`conservation_response` (INVARIANT 1, the RESPOND step).** Emptying the escrow onto the
two boards conserves the total: `share_split` says the two shares reassemble the offer exactly.
-/
theorem conservation_response (s : GState) (p : Player) (r : Response) :
    totalCards (applyResponse s p r) = totalCards s := by
  by_cases hleg : legalRespB s p r = true
  · cases hp : s.pending with
    | none => simp [legalRespB, hp] at hleg
    | some o =>
      simp only [applyResponse, hleg, cond_true, applyRespLegal, hp, totalCards, sum2,
        pendingCards]
      cases p <;>
        simp only [Function.update_apply, Player.other_p1, Player.other_p2, reduceCtorEq,
          reduceIte] <;>
        · conv_lhs => rw [add_zero]
          conv_rhs => rw [← share_split o r]
          ac_rfl
  · simp only [Bool.not_eq_true] at hleg
    simp [applyResponse, hleg]

/-- **`conservation_move` (INVARIANT 1, every move).** -/
theorem conservation_move (s : GState) (p : Player) (m : Move) :
    totalCards (applyMove s p m) = totalCards s := by
  cases m with
  | act a => exact conservation s p a
  | respond r => exact conservation_response s p r

/-! ## 5. INVARIANT 2 — ONE ACTION PER ROUND (a monotone used-set) -/

/-- A response never touches the used-flags (responding is not one of your four actions). -/
@[simp] theorem used_applyResponse (s : GState) (p : Player) (r : Response) :
    (applyResponse s p r).used = s.used := by
  by_cases hleg : legalRespB s p r = true
  · simp only [applyResponse, hleg, cond_true, applyRespLegal]
    cases s.pending <;> rfl
  · simp only [Bool.not_eq_true] at hleg
    simp [applyResponse, hleg]

/-- **`used_monotone` (INVARIANT 2a).** Any move only ever SETS a used-flag. -/
theorem used_monotone (s : GState) (p : Player) (m : Move) (q : Player) (k : ActionKind)
    (h : s.used q k = true) : (applyMove s p m).used q k = true := by
  cases m with
  | respond r => simpa [applyMove] using h
  | act a =>
    show (applyAction s p a).used q k = true
    by_cases hleg : legalB s p a = true
    · simp only [applyAction, hleg, cond_true, applyLegal, Function.update_apply]
      by_cases hq : q = p
      · subst hq
        by_cases hk : k = a.kind
        · subst hk; simp
        · simp [hk, h]
      · simp [hq, h]
    · simp only [Bool.not_eq_true] at hleg
      simp only [applyAction, hleg, cond_false]; exact h

/-- **`legal_needs_unused` (INVARIANT 2b).** A legal action REQUIRES its kind unused this round.
-/
theorem legal_needs_unused (s : GState) (p : Player) (a : Action) (h : legalB s p a = true) :
    s.used p a.kind = false := by
  simp only [legalB, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.1.2

/-- **`used_after_legal` (the flag IS set — non-vacuity of the used-set).** -/
theorem used_after_legal (s : GState) (p : Player) (a : Action) (h : legalB s p a = true) :
    (applyAction s p a).used p a.kind = true := by
  simp only [applyAction, h, cond_true, applyLegal, Function.update_self]

/-! ## 5B. THE TURN STAMP — every move advances it by exactly one -/

/-- A legal action stamps one turn. -/
theorem turns_applyLegal (s : GState) (p : Player) (a : Action) (h : legalB s p a = true) :
    (applyAction s p a).turns = s.turns + 1 := by
  simp [applyAction, h, applyLegal]

/-- A legal response stamps one turn (a response is a real committed turn, not a free rider). -/
theorem turns_applyResponse (s : GState) (p : Player) (r : Response)
    (h : legalRespB s p r = true) : (applyResponse s p r).turns = s.turns + 1 := by
  simp only [applyResponse, h, cond_true, applyRespLegal]
  cases hp : s.pending with
  | none => simp [legalRespB, hp] at h
  | some o => simp

/-! ## 6. INVARIANT 3 — SCORING (control, monotonicity, the Secret scored) -/

/-- **`geishaCount s p g`** — the placed cards PLUS the secret (the Secret IS scored). -/
def geishaCount (s : GState) (p : Player) (g : Geisha) : ℕ :=
  (s.placed p).count g + (s.secret p).count g

/-- **`secret_is_scored`.** The secret pile contributes to the tally. -/
theorem secret_is_scored (s : GState) (p : Player) (g : Geisha) :
    (s.placed p).count g ≤ geishaCount s p g := by
  simp only [geishaCount]; exact Nat.le_add_right _ _

/-- Placed cards only accrue under a move (an action escrows, a response places). -/
theorem placed_le (s : GState) (p : Player) (m : Move) (q : Player) :
    s.placed q ≤ (applyMove s p m).placed q := by
  cases m with
  | act a =>
    show s.placed q ≤ (applyAction s p a).placed q
    by_cases hleg : legalB s p a = true
    · simp [applyAction, hleg, applyLegal]
    · simp only [Bool.not_eq_true] at hleg; simp [applyAction, hleg]
  | respond r =>
    show s.placed q ≤ (applyResponse s p r).placed q
    by_cases hleg : legalRespB s p r = true
    · simp only [applyResponse, hleg, cond_true, applyRespLegal]
      cases hp : s.pending with
      | none => simp [legalRespB, hp] at hleg
      | some o =>
        simp only [Function.update_apply]
        cases p <;> cases q <;>
          simp only [Player.other_p1, Player.other_p2, reduceCtorEq, if_true, if_false] <;>
          first
            | exact le_rfl
            | exact Multiset.le_add_right _ _
    · simp only [Bool.not_eq_true] at hleg; simp [applyResponse, hleg]

/-- Secret cards only accrue under a move. -/
theorem secret_le (s : GState) (p : Player) (m : Move) (q : Player) :
    s.secret q ≤ (applyMove s p m).secret q := by
  cases m with
  | act a =>
    show s.secret q ≤ (applyAction s p a).secret q
    by_cases hleg : legalB s p a = true
    · simp only [applyAction, hleg, cond_true, applyLegal, Function.update_apply]
      cases p <;> cases q <;>
        simp only [reduceCtorEq, if_true, if_false] <;>
        first
          | exact le_rfl
          | exact Multiset.le_add_right _ _
    · simp only [Bool.not_eq_true] at hleg; simp [applyAction, hleg]
  | respond r =>
    show s.secret q ≤ (applyResponse s p r).secret q
    by_cases hleg : legalRespB s p r = true
    · simp only [applyResponse, hleg, cond_true, applyRespLegal]
      cases s.pending <;> exact le_rfl
    · simp only [Bool.not_eq_true] at hleg; simp [applyResponse, hleg]

/-- **`geishaCount_mono` (INVARIANT 3 — scores only accrue).** -/
theorem geishaCount_mono (s : GState) (p : Player) (m : Move) (q : Player) (g : Geisha) :
    geishaCount s q g ≤ geishaCount (applyMove s p m) q g :=
  Nat.add_le_add
    (Multiset.count_le_of_le g (placed_le s p m q))
    (Multiset.count_le_of_le g (secret_le s p m q))

/-- The ACT-step specialisation the deployed program bridge reads. -/
theorem geishaCount_mono_act (s : GState) (p : Player) (a : Action) (q : Player) (g : Geisha) :
    geishaCount s q g ≤ geishaCount (applyAction s p a) q g :=
  geishaCount_mono s p (.act a) q g

/-- The RESPOND-step specialisation. -/
theorem geishaCount_mono_resp (s : GState) (p : Player) (r : Response) (q : Player) (g : Geisha) :
    geishaCount s q g ≤ geishaCount (applyResponse s p r) q g :=
  geishaCount_mono s p (.respond r) q g

/-- **`control s g`** — whoever has the strictly higher tally; a tie leaves the row uncontrolled.
-/
def control (s : GState) (g : Geisha) : Option Player :=
  if geishaCount s .p2 g < geishaCount s .p1 g then some .p1
  else if geishaCount s .p1 g < geishaCount s .p2 g then some .p2
  else none

/-- **`control_correct`.** If `control s g = some p` then `p` strictly out-tallies the opponent. -/
theorem control_correct (s : GState) (g : Geisha) (p : Player)
    (h : control s g = some p) : geishaCount s p.other g < geishaCount s p g := by
  simp only [control] at h
  split at h
  · rename_i h1
    rw [Option.some.injEq] at h; subst h; simpa using h1
  · split at h
    · rename_i h2
      rw [Option.some.injEq] at h; subst h; simpa using h2
    · exact absurd h (by simp)

/-! ## 7. INVARIANT 4 — WIN-SAFETY -/

/-- Rows controlled by player `p`. -/
def controlledBy (s : GState) (p : Player) : Finset Geisha :=
  Finset.univ.filter (fun g => control s g = some p)

/-- Total charm a player controls. -/
def charmScore (s : GState) (p : Player) : ℕ := ∑ g ∈ controlledBy s p, charm g

/-- Number of rows a player controls. -/
def geishaScore (s : GState) (p : Player) : ℕ := (controlledBy s p).card

/-- The charm win threshold (`≥ 11 charm`) — the single source the model AND the emitted
win-gate both read. -/
abbrev charmWinThreshold : ℕ := 11

/-- The guild-count win threshold (`≥ 4 rows`). -/
abbrev guildWinThreshold : ℕ := 4

/-- **`Won`** — ≥ 11 charm OR ≥ 4 rows. -/
def Won (s : GState) (p : Player) : Prop :=
  charmWinThreshold ≤ charmScore s p ∨ guildWinThreshold ≤ geishaScore s p

/-- **`won_iff_threshold` (WIN-SAFETY — cannot win illegally).** -/
theorem won_iff_threshold (s : GState) (p : Player) :
    Won s p ↔ (11 ≤ charmScore s p ∨ 4 ≤ geishaScore s p) := Iff.rfl

/-- **`won_needs_control` (WIN-SAFETY — cannot win out of nothing).** -/
theorem won_needs_control (s : GState) (p : Player) (h : Won s p) :
    (controlledBy s p).Nonempty := by
  rcases h with hc | hg
  · rcases Finset.eq_empty_or_nonempty (controlledBy s p) with he | hne
    · simp only [charmScore, charmWinThreshold, he, Finset.sum_empty] at hc; omega
    · exact hne
  · rcases Finset.eq_empty_or_nonempty (controlledBy s p) with he | hne
    · simp only [geishaScore, guildWinThreshold, he, Finset.card_empty] at hg; omega
    · exact hne

/-! ### The blank state and the winning witnesses (non-vacuity + teeth) -/

/-- A blank state: empty everywhere, nobody has acted, no offer on the table. -/
def blankState : GState where
  removed := 0
  deck := 0
  hand := fun _ => 0
  secret := fun _ => 0
  discardPile := fun _ => 0
  placed := fun _ => 0
  used := fun _ _ => false
  pending := none
  current := .p1
  turns := 0

/-- **`not_won_blank` (WIN-SAFETY teeth).** -/
theorem not_won_blank (p : Player) : ¬ Won blankState p := by
  have hempty : controlledBy blankState p = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro g _
    simp [control, blankState, geishaCount]
  simp only [Won, charmScore, geishaScore, charmWinThreshold, guildWinThreshold, hempty,
    Finset.sum_empty, Finset.card_empty]
  omega

/-- A concrete **winning state**: P1 controls rows `3`, `5`, `6` for `3 + 4 + 5 = 12` charm. -/
def winState : GState :=
  { blankState with placed := fun p => if p = .p1 then ({3, 5, 6} : Multiset Geisha) else 0 }

/-- **`winState_wins` (WIN-SAFETY non-vacuity — a real win exists).** -/
theorem winState_wins : Won winState .p1 := by
  have hctl : controlledBy winState .p1 = {3, 5, 6} := by decide
  left
  simp only [charmScore, hctl]
  decide

/-! ## 7B. ⚑ THE ADJUDICATED ROUND WINNER — the fix for the 66% draw rate

**The design wound.** `Won` is an ABSOLUTE threshold and the shipped game is ONE round, so a
round in which neither player clears the bar had NO WINNER. **Measured: 66.1% of rounds ended
with no winner at all.**

**Why, exactly.** `∑ g, charm g = 21` and `control` awards a row to at most one player, so
`charmScore p1 + charmScore p2 ≤ 21` (`charmScore_add_le`) — if every row were controlled the sum
would be 21, forcing one player to ≥ 11. So EVERY undecided round is caused by TIED rows going
uncontrolled and their charm evaporating.

**The fix.** Adjudicating an undecided round on total charm, then rows held, leaves **5.1%**
draws at 41.2% / 53.7%. It does not touch `control`, so the emitted win-gate teeth keep meaning
exactly what they meant, and `Won` is UNCHANGED and still the first thing `roundWinner` asks. -/

instance (s : GState) (p : Player) : Decidable (Won s p) := by unfold Won; exact inferInstance

/-- The two players' controlled-row sets are DISJOINT. -/
theorem controlledBy_disjoint (s : GState) :
    Disjoint (controlledBy s .p1) (controlledBy s .p2) := by
  rw [Finset.disjoint_left]
  intro g h1 h2
  simp only [controlledBy, Finset.mem_filter] at h1 h2
  rw [h1.2] at h2
  exact absurd h2.2 (by simp)

/-- **`charmScore_add_le` — the conservation of charm.** -/
theorem charmScore_add_le (s : GState) :
    charmScore s .p1 + charmScore s .p2 ≤ ∑ g : Geisha, charm g := by
  rw [charmScore, charmScore, ← Finset.sum_union (controlledBy_disjoint s)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun _ _ _ => Nat.zero_le _)

/-- The board's whole charm is `21`. -/
theorem total_charm : (∑ g : Geisha, charm g) = 21 := by decide

/-- Likewise for rows held. -/
theorem geishaScore_add_le (s : GState) : geishaScore s .p1 + geishaScore s .p2 ≤ 7 := by
  rw [geishaScore, geishaScore, ← Finset.card_union_of_disjoint (controlledBy_disjoint s)]
  simpa using Finset.card_le_card (Finset.subset_univ
    (controlledBy s .p1 ∪ controlledBy s .p2))

/-- **`not_both_charm_won`** — `11 + 11 > 21`. -/
theorem not_both_charm_won (s : GState) :
    ¬ (charmWinThreshold ≤ charmScore s .p1 ∧ charmWinThreshold ≤ charmScore s .p2) := by
  rintro ⟨h1, h2⟩
  have hc := charmScore_add_le s
  rw [total_charm] at hc
  simp only [charmWinThreshold] at h1 h2
  omega

/-- **`not_both_guild_won`** — `4 + 4 > 7`. -/
theorem not_both_guild_won (s : GState) :
    ¬ (guildWinThreshold ≤ geishaScore s .p1 ∧ guildWinThreshold ≤ geishaScore s .p2) := by
  rintro ⟨h1, h2⟩
  have hg := geishaScore_add_le s
  simp only [guildWinThreshold] at h1 h2
  omega

/-- ⚠ **`won_can_be_mutual` — `Won` is NOT exclusive.** P1 can hold rows `4,5,6` for `12` charm
on THREE rows while P2 holds the other FOUR for `9`. Both are `Won`. So the round's terminal rule
needs a PRECEDENCE, not an exclusivity argument. -/
def straddleState : GState :=
  { blankState with
    placed := fun p => if p = .p1 then ({4, 5, 6} : Multiset Geisha)
                                   else ({0, 1, 2, 3} : Multiset Geisha) }

theorem won_can_be_mutual : Won straddleState .p1 ∧ Won straddleState .p2 := by
  have h1 : controlledBy straddleState .p1 = {4, 5, 6} := by decide
  have h2 : controlledBy straddleState .p2 = {0, 1, 2, 3} := by decide
  refine ⟨Or.inl ?_, Or.inr ?_⟩
  · simp only [charmScore, h1]; decide
  · simp only [geishaScore, h2]; decide

/-- **`roundWinner` — the terminal rule.** Absolute threshold (`Won`, UNCHANGED); then higher
TOTAL CHARM; then higher ROW COUNT; only on exact parity of both is it a genuine draw. -/
def roundWinner (s : GState) : Option Player :=
  if charmWinThreshold ≤ charmScore s .p1 then some .p1
  else if charmWinThreshold ≤ charmScore s .p2 then some .p2
  else if guildWinThreshold ≤ geishaScore s .p1 then some .p1
  else if guildWinThreshold ≤ geishaScore s .p2 then some .p2
  else if charmScore s .p2 < charmScore s .p1 then some .p1
  else if charmScore s .p1 < charmScore s .p2 then some .p2
  else if geishaScore s .p2 < geishaScore s .p1 then some .p1
  else if geishaScore s .p1 < geishaScore s .p2 then some .p2
  else none

/-! ### The CLAUSE that decided the round

`roundWinner` is a PRECEDENCE, and which of its nine clauses fired is itself a fact about the
round — "p1 won on charm" and "p1 won because p2 held fewer rows at equal charm" are different
outcomes even though both name p1. `roundWinnerBranch` names the clause; `branchWinner` reads the
seat back off it, and `roundWinner_eq_branchWinner` proves the two carry exactly the same content.

This matters DOWNSTREAM rather than here: the deployed teeth (`MultiwayTugProgram`) cannot express
a disjunction of cross-register comparisons inside one case, so each clause becomes its own
transition case and the CLAUSE is what a scoring turn names. A caller therefore has to be told
which clause fired — and it is told by this function through the oracle, not by re-deciding the
precedence in its own language. -/

/-- The clause of `roundWinner` that decides `s`, `0..8` in precedence order: charm-threshold p1,
charm-threshold p2, row-threshold p1, row-threshold p2, charm-lead p1, charm-lead p2, row-lead p1,
row-lead p2, dead heat. -/
def roundWinnerBranch (s : GState) : Nat :=
  if charmWinThreshold ≤ charmScore s .p1 then 0
  else if charmWinThreshold ≤ charmScore s .p2 then 1
  else if guildWinThreshold ≤ geishaScore s .p1 then 2
  else if guildWinThreshold ≤ geishaScore s .p2 then 3
  else if charmScore s .p2 < charmScore s .p1 then 4
  else if charmScore s .p1 < charmScore s .p2 then 5
  else if geishaScore s .p2 < geishaScore s .p1 then 6
  else if geishaScore s .p1 < geishaScore s .p2 then 7
  else 8

/-- The seat a clause names (`8`, and every out-of-range index, is the draw). -/
def branchWinner : Nat → Option Player
  | 0 => some .p1
  | 1 => some .p2
  | 2 => some .p1
  | 3 => some .p2
  | 4 => some .p1
  | 5 => some .p2
  | 6 => some .p1
  | 7 => some .p2
  | _ => none

/-- **`roundWinner_eq_branchWinner`** — the clause index loses nothing: reading the seat off the
clause is the terminal rule. So a caller told only the CLAUSE knows the winner. -/
theorem roundWinner_eq_branchWinner (s : GState) :
    roundWinner s = branchWinner (roundWinnerBranch s) := by
  unfold roundWinner roundWinnerBranch
  split_ifs <;> rfl

/-- The clause index is in range. -/
theorem roundWinnerBranch_lt (s : GState) : roundWinnerBranch s < 9 := by
  unfold roundWinnerBranch
  split_ifs <;> omega

/-- **`terminal_rule_reads_only_the_tallies`** — every terminal quantity (`control`, both scores,
`Won`, `roundWinner` and its clause) is a function of the per-`(seat, row)` tallies ALONE. The deck,
the hands, the discards, the removed favor and the turn stamp are irrelevant to it.

This is what makes a caller's wire encoding faithful WITHOUT it having to reconstruct zones it does
not track: a caller that reports the true `geishaCount` of every `(seat, row)` gets the true
adjudication, whatever it writes in the other zones. It is stated as a theorem rather than left as
an assumption in a comment because it is exactly the assumption the FFI caller relies on. -/
theorem terminal_rule_reads_only_the_tallies (s t : GState)
    (h : ∀ p g, geishaCount s p g = geishaCount t p g) :
    (∀ g, control s g = control t g)
    ∧ (∀ p, charmScore s p = charmScore t p)
    ∧ (∀ p, geishaScore s p = geishaScore t p)
    ∧ roundWinner s = roundWinner t
    ∧ roundWinnerBranch s = roundWinnerBranch t := by
  have hctl : ∀ g, control s g = control t g := by
    intro g; simp only [control, h]
  have hby : ∀ p, controlledBy s p = controlledBy t p := by
    intro p; simp only [controlledBy, hctl]
  have hc : ∀ p, charmScore s p = charmScore t p := by
    intro p; simp only [charmScore, hby]
  have hg : ∀ p, geishaScore s p = geishaScore t p := by
    intro p; simp only [geishaScore, hby]
  refine ⟨hctl, hc, hg, ?_, ?_⟩
  · simp only [roundWinner, hc, hg]
  · simp only [roundWinnerBranch, hc, hg]

/-- **`roundWinner_extends_Won` (the fix is CONSERVATIVE).** -/
theorem roundWinner_extends_Won (s : GState) (p : Player) (h : Won s p) (h' : ¬ Won s p.other) :
    roundWinner s = some p := by
  simp only [Won, charmWinThreshold, guildWinThreshold, not_or, not_le] at h h'
  cases p with
  | p1 => simp only [Player.other_p1] at h'
          rcases h with hc | hg <;>
            (rw [roundWinner]; simp only [charmWinThreshold, guildWinThreshold]
             split_ifs <;> first | rfl | omega)
  | p2 => simp only [Player.other_p2] at h'
          rcases h with hc | hg <;>
            (rw [roundWinner]; simp only [charmWinThreshold, guildWinThreshold]
             split_ifs <;> first | rfl | omega)

/-- **`roundWinner_sound` (the adjudicated winner EARNED it).** -/
theorem roundWinner_sound (s : GState) (p : Player) (h : roundWinner s = some p) :
    Won s p
      ∨ charmScore s p.other < charmScore s p
      ∨ (charmScore s p.other = charmScore s p ∧ geishaScore s p.other < geishaScore s p) := by
  unfold roundWinner at h
  split at h
  · rename_i hw; rw [Option.some.injEq] at h; subst h; exact Or.inl (Or.inl hw)
  · split at h
    · rename_i hw; rw [Option.some.injEq] at h; subst h; exact Or.inl (Or.inl hw)
    · split at h
      · rename_i hw; rw [Option.some.injEq] at h; subst h; exact Or.inl (Or.inr hw)
      · split at h
        · rename_i hw; rw [Option.some.injEq] at h; subst h; exact Or.inl (Or.inr hw)
        · split at h
          · rename_i hlt; rw [Option.some.injEq] at h; subst h; exact Or.inr (Or.inl hlt)
          · split at h
            · rename_i hlt; rw [Option.some.injEq] at h; subst h; exact Or.inr (Or.inl hlt)
            · split at h
              · rename_i h1 h2 hlt
                rw [Option.some.injEq] at h; subst h
                exact Or.inr (Or.inr ⟨by simp only [Player.other_p1]; omega, hlt⟩)
              · split at h
                · rename_i h1 h2 h3 hlt
                  rw [Option.some.injEq] at h; subst h
                  exact Or.inr (Or.inr ⟨by simp only [Player.other_p2]; omega, hlt⟩)
                · exact absurd h (by simp)

/-- **`roundWinner_draw_iff` (the draw is an EXACT DEAD HEAT).** -/
theorem roundWinner_draw_iff (s : GState) :
    roundWinner s = none ↔
      (charmScore s .p1 = charmScore s .p2 ∧ geishaScore s .p1 = geishaScore s .p2) := by
  constructor
  · intro h
    unfold roundWinner at h
    repeat (split at h; · exact absurd h (by simp))
    rename_i h1 h2 h3 h4 h5 h6 h7 h8
    exact ⟨by omega, by omega⟩
  · rintro ⟨hc, hg⟩
    have hcs := charmScore_add_le s
    rw [total_charm] at hcs
    have hgs := geishaScore_add_le s
    rw [roundWinner, if_neg (by simp only [charmWinThreshold]; omega),
      if_neg (by simp only [charmWinThreshold]; omega),
      if_neg (by simp only [guildWinThreshold]; omega),
      if_neg (by simp only [guildWinThreshold]; omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- A concrete round the SHIPPED rule threw away: P1 holds rows `5`,`6` (charm `9`), P2 holds
row `3` (charm `3`). Nobody reached the bar, so the match was a non-event. -/
def undecidedState : GState :=
  { blankState with
    placed := fun p => if p = .p1 then ({5, 6} : Multiset Geisha) else ({3} : Multiset Geisha) }

/-- **`undecidedState_not_Won` — the shipped rule finds NO winner here.** -/
theorem undecidedState_not_Won (p : Player) : ¬ Won undecidedState p := by
  have h1 : controlledBy undecidedState .p1 = {5, 6} := by decide
  have h2 : controlledBy undecidedState .p2 = {3} := by decide
  cases p <;>
    simp only [Won, charmScore, geishaScore, charmWinThreshold, guildWinThreshold, h1, h2] <;>
    decide

/-- **`undecidedState_adjudicates` (THE FIX, WITNESSED).** -/
theorem undecidedState_adjudicates : roundWinner undecidedState = some .p1 := by
  have hc1 : controlledBy undecidedState .p1 = {5, 6} := by decide
  have hc2 : controlledBy undecidedState .p2 = {3} := by decide
  have e1 : charmScore undecidedState .p1 = 9 := by simp only [charmScore, hc1]; decide
  have e2 : charmScore undecidedState .p2 = 3 := by simp only [charmScore, hc2]; decide
  have g1 : geishaScore undecidedState .p1 = 2 := by simp only [geishaScore, hc1]; decide
  have g2 : geishaScore undecidedState .p2 = 1 := by simp only [geishaScore, hc2]; decide
  rw [roundWinner]
  simp only [charmWinThreshold, guildWinThreshold, e1, e2, g1, g2]
  decide

/-- **`winState_roundWinner` — a threshold win is still a threshold win.** -/
theorem winState_roundWinner : roundWinner winState = some .p1 := by
  have hctl : controlledBy winState .p1 = {3, 5, 6} := by decide
  have hc : charmWinThreshold ≤ charmScore winState .p1 := by
    simp only [charmScore, charmWinThreshold, hctl]; decide
  simp only [roundWinner, if_pos hc]

/-- A genuine dead heat. -/
theorem blankState_draws : roundWinner blankState = none := by
  rw [roundWinner_draw_iff]
  have h : ∀ p, controlledBy blankState p = ∅ := by
    intro p
    apply Finset.filter_eq_empty_iff.mpr
    intro g _
    simp [control, blankState, geishaCount]
  simp [charmScore, geishaScore, h]

/-! ## 7C. ⚑⚑ THE THREE DECISIONS, AS THEOREMS

This is the section that answers "a player currently decides nothing". Each of the three
restored decisions gets a theorem saying it is a REAL choice: different inputs, different
outcomes, over the SAME position. -/

/-! ### Decision 1 — WHICH action, WHEN. -/

/-- The cards an action-kind consumes after that turn's draw (`4,3,2,1`). -/
def kindCost : ActionKind → ℕ
  | .competitionK => 4
  | .giftK => 3
  | .discardK => 2
  | .secretK => 1

/-- Is a proposed ORDER of the four action-kinds card-feasible from a 6-card opening with one
draw per action-turn? After `k` turns you have drawn `k` cards, so the cumulative spend of the
first `k` actions must never exceed `6 + k`. -/
def orderFeasible (o : List ActionKind) : Bool :=
  (List.range (o.length + 1)).all
    (fun k => decide (((o.take k).map kindCost).sum ≤ 6 + k))

/-- The 24 orderings of the four once-per-round actions. -/
def allOrders : List (List ActionKind) :=
  let ks := [ActionKind.secretK, .discardK, .giftK, .competitionK]
  (ks.flatMap fun a => (ks.filter (· != a)).flatMap fun b =>
    ((ks.filter (· != a)).filter (· != b)).flatMap fun c =>
      (((ks.filter (· != a)).filter (· != b)).filter (· != c)).map fun d => [a, b, c, d])

/-- **`every_action_order_is_feasible` (DECISION 1 IS REAL).** ALL 24 orderings of the four
once-per-round actions are card-feasible — the descending `[Competition, Gift, Discard, Secret]`
the Rust engine hardcoded for BOTH seats was one arbitrary point in a space that was always
fully available. `legalB` requires only that the kind be unused, so the whole space is legal;
this theorem says none of it is a card-starvation trap. -/
theorem every_action_order_is_feasible : allOrders.all orderFeasible = true := by decide

/-- Non-vacuity of the sweep: there really are 24 orders (not an empty `all`). -/
theorem allOrders_card : allOrders.length = 24 := by decide

/-- The falsifier for `orderFeasible`: a 5-cost action would NOT be feasible first, so the
predicate can go false and `every_action_order_is_feasible` is a real check. -/
theorem orderFeasible_can_fail :
    orderFeasible [ActionKind.competitionK, .competitionK, .competitionK] = false := by decide

/-! ### Decision 2 — THE CUT (the cake-cutting dilemma, quantified). -/

/-- The raw influence of a multiset of favors. -/
def weight (m : Multiset Geisha) : ℕ := (m.map charm).sum

/-- The **swing** a response produces for the CUTTER: their share minus the taker's. -/
def swing (o : Offer) (r : Response) : Int :=
  (weight (cutterShare o r) : Int) - (weight (takerShare o r) : Int)

/-- The cutter's **guaranteed swing**: the worst the taker can do to them. This is the value a
proposer is actually choosing when they choose a cut — the taker will pick the response that
minimises it. -/
def guarantee : Offer → Int
  | o@(.gift _ _ _ _) => min (min (swing o (.gift 0)) (swing o (.gift 1))) (swing o (.gift 2))
  | o@(.comp _ _ _ _ _) => min (swing o (.comp 0)) (swing o (.comp 1))

/-- **`comp_balanced_cut_dominates` (DECISION 2 IS REAL — the cake-cutting dilemma).**

The SAME four favors (rows `6,5,0,1`, charm `5,4,2,2`), paired two ways:

  * lopsided `{5,4} | {2,2}` guarantees the cutter **−5** (the taker simply takes the big pair);
  * balanced  `{5,2} | {4,2}` guarantees the cutter **−1**.

So the PAIRING — a thing the shipped game never let a player express, because the split was
pre-folded into the actor's own action — strictly changes what the cutter can guarantee. This
is the agonising bit of Hanamikoji restored as a checked inequality: you must cut so that you
are content with EITHER half, because you do not get to choose which one you keep. -/
theorem comp_balanced_cut_dominates :
    guarantee (.comp .p1 6 5 0 1) = -5
      ∧ guarantee (.comp .p1 6 0 5 1) = -1
      ∧ guarantee (.comp .p1 6 5 0 1) < guarantee (.comp .p1 6 0 5 1) := by
  refine ⟨by decide, by decide, by decide⟩

/-- **`gift_modest_cut_dominates` (DECISION 2, the Gift face).**

Presenting your three STRONGEST favors (rows `6,5,0` = charm `5,4,2`) guarantees a swing of only
**+1** — the opponent just takes the `5`. Presenting three modest ones (`0,1,2` = charm `2,2,2`)
guarantees **+2**. The strong presentation has the higher raw total and the WORSE guarantee:
what you present is a decision with a wrong answer, and the wrong answer is the greedy one the
`pick_highest` mover always played. -/
theorem gift_modest_cut_dominates :
    guarantee (.gift .p1 6 5 0) = 1
      ∧ guarantee (.gift .p1 0 1 2) = 2
      ∧ guarantee (.gift .p1 6 5 0) < guarantee (.gift .p1 0 1 2) := by
  refine ⟨by decide, by decide, by decide⟩

/-! ### Decision 3 — THE CHOICE (the theorem this whole lane exists for). -/

/-- A live position with a pending Gift: P1 has cut three favors (rows `6`, `0`, `2` — charm
`5, 2, 2`) and P2 is to answer. The board already standing: P2 holds rows `3` and `4` (charm
`3 + 3`), P1 holds row `1` (charm `2`). -/
def cutState : GState :=
  { blankState with
    placed := fun p => if p = .p1 then ({1} : Multiset Geisha) else ({3, 4} : Multiset Geisha)
    pending := some (.gift .p1 6 0 2)
    current := .p2
    used := fun p k => p = .p1 ∧ k = .giftK }

/-- The position is REAL: P2's response is legal (so `applyResponse` is not a silent no-op and
the theorem below is not about two copies of the same state). -/
theorem cutState_response_legal (k : Fin 3) : legalRespB cutState .p2 (.gift k) = true := by
  fin_cases k <;> rfl

/-- ⚑ **`respond_decides_the_round` — THE FALSIFIER, DISCHARGED.**

From ONE pending offer, in ONE position, the responder's two answers hand the round to DIFFERENT
players:

  * take the `5`-charm favor → P2 reaches `3 + 3 + 5 = 11` charm and **P2 wins outright**;
  * take a `2`-charm favor instead → P2 has `8`, P1 has `2 + 5 + 2 = 9`, and **P1 wins**.

The shipped game had no step at which anyone could make this choice: `advance` took no card
argument, the split was pre-folded into the actor's own action, and the "opponent's genuine
choice" was a `max_by_key`. This theorem is the machine-checked statement that a player now
decides the outcome. -/
theorem respond_decides_the_round :
    roundWinner (applyResponse cutState .p2 (.gift 0)) = some .p2
      ∧ roundWinner (applyResponse cutState .p2 (.gift 1)) = some .p1 := by
  constructor
  · have hc1 : controlledBy (applyResponse cutState .p2 (.gift 0)) .p1 = {0, 1, 2} := by decide
    have hc2 : controlledBy (applyResponse cutState .p2 (.gift 0)) .p2 = {3, 4, 6} := by decide
    have e1 : charmScore (applyResponse cutState .p2 (.gift 0)) .p1 = 6 := by
      simp only [charmScore, hc1]; decide
    have e2 : charmScore (applyResponse cutState .p2 (.gift 0)) .p2 = 11 := by
      simp only [charmScore, hc2]; decide
    rw [roundWinner]
    simp only [charmWinThreshold, guildWinThreshold, e1, e2]
    decide
  · have hc1 : controlledBy (applyResponse cutState .p2 (.gift 1)) .p1 = {1, 2, 6} := by decide
    have hc2 : controlledBy (applyResponse cutState .p2 (.gift 1)) .p2 = {0, 3, 4} := by decide
    have e1 : charmScore (applyResponse cutState .p2 (.gift 1)) .p1 = 9 := by
      simp only [charmScore, hc1]; decide
    have e2 : charmScore (applyResponse cutState .p2 (.gift 1)) .p2 = 8 := by
      simp only [charmScore, hc2]; decide
    have g1 : geishaScore (applyResponse cutState .p2 (.gift 1)) .p1 = 3 := by
      simp only [geishaScore, hc1]; decide
    have g2 : geishaScore (applyResponse cutState .p2 (.gift 1)) .p2 = 3 := by
      simp only [geishaScore, hc2]; decide
    rw [roundWinner]
    simp only [charmWinThreshold, guildWinThreshold, e1, e2, g1, g2]
    decide

/-- The two answers really do land in different states (the sharper, control-free form). -/
theorem respond_changes_the_board :
    (applyResponse cutState .p2 (.gift 0)).placed .p2
      ≠ (applyResponse cutState .p2 (.gift 1)).placed .p2 := by decide

/-- And the proposer cannot help themselves to the good half: P1 answering P1's own cut is
REFUSED, so `respond_decides_the_round`'s choice genuinely belongs to the other seat. -/
theorem cutState_self_deal_refused (k : Fin 3) : legalRespB cutState .p1 (.gift k) = false :=
  respond_not_by_proposer cutState .p1 (.gift k) (.gift .p1 6 0 2) rfl rfl

/-! ## 8. The `Boundary` tie-in — conservation as a `Good`-invariant along whole executions -/

open Dregg2.Boundary

/-- The game as a `TurnCoalg`: the input alphabet is `Player × Move`. -/
def gameCoalg : TurnCoalg Unit (Player × Move) where
  Carrier := GState
  step := fun s => ((), fun pm => applyMove s pm.1 pm.2)

/-- **`conservation_along_run` (INVARIANT 1, lifted to all time).** Conservation holds at EVERY
configuration reachable along a whole execution `Run` — now over the alphabet that INCLUDES the
response step. -/
theorem conservation_along_run {x y : GState} (C : Multiset Geisha)
    (hrun : Execution.Run (inducedSystem gameCoalg) x y)
    (hx : totalCards x = C) : totalCards y = C := by
  refine stepComplete_preserves gameCoalg
    (fun a _ b => totalCards b = totalCards a)
    (fun _ _ _ => True) (fun _ _ _ => True) (fun _ _ _ => True)
    (fun s => totalCards s = C) ?_ ?_ hrun hx
  · intro x t
    refine ⟨?_, trivial, trivial, trivial⟩
    obtain ⟨p, m⟩ := t
    exact conservation_move x p m
  · intro x t hgood hinv
    exact hinv.1.trans hgood

/-! ## 9. THE AIR-REFINEMENT OBLIGATION (the AIR side lands in `MultiwayTugAir.lean`) -/

/-- **`AirSpec air`** — the contract the verified circuit's transition AIR must meet. -/
def AirSpec (air : GState → Player → Action → GState → Prop) : Prop :=
  ∀ o p a n, air o p a n ↔ n = applyAction o p a

/-- **`multiwayTug_air_refines_applyAction` (THE OBLIGATION, stated).** -/
theorem multiwayTug_air_refines_applyAction
    (air : GState → Player → Action → GState → Prop) (h : AirSpec air)
    (o : GState) (p : Player) (a : Action) (n : GState) :
    air o p a n ↔ n = applyAction o p a :=
  h o p a n

/-- **`air_functional` (a consequence of the contract).** -/
theorem air_functional
    (air : GState → Player → Action → GState → Prop) (h : AirSpec air)
    {o : GState} {p : Player} {a : Action} {n₁ n₂ : GState}
    (h₁ : air o p a n₁) (h₂ : air o p a n₂) : n₁ = n₂ :=
  ((h o p a n₁).mp h₁).trans ((h o p a n₂).mp h₂).symm

/-! ## 10. A real play witness (smoke — the model runs, cards are conserved)

⚑ **THE WITNESS NO LONGER EVALUATES IN THIS MODULE (2026-08-08).** This module is in the
`Dregg2.FFI` closure — the crypto archive's build — and the 12 `#guard`s that used to run at
elaboration here made every game-fixture regression a hard failure of every Rust proving
target. The `demo` state STAYS here (a `def` body elaborates without running); the
EVALUATION — each fact as a NAMED theorem per GUARD-DISCIPLINE, `native_decide` +
`#assert_compiled` — lives in `MultiwayTugFixtures.lean`, rooted in the central guard library:
a plain `lake build` still runs every pin, and a stale fixture reds the guard library instead
of the archive. Every pinned expression mentions only PUBLIC names, so the pins moved
verbatim: the legal cut, conservation over cut and answer, the pending offer and seat pass,
the anti-self-deal refusal, the interlock, the used-flag, the illegal-action no-op, the
21-card deck, and the 12-turn round. -/

/-- A concrete mid-game state: P1 to move, both hands dealt, nothing on the table. -/
def demo : GState :=
  { blankState with
    hand := fun p => if p = .p1 then ({3, 3, 5, 6, 6, 0} : Multiset Geisha)
                                 else ({1, 2, 4, 5, 6, 0} : Multiset Geisha)
    current := .p1 }

/-! ## 11. Axiom hygiene — the PROVEN invariants pinned to the standard kernel triple. -/

#assert_axioms share_split
#assert_axioms conservation
#assert_axioms conservation_response
#assert_axioms conservation_move
#assert_axioms applyMove_deterministic
#assert_axioms applyAction_deterministic
#assert_axioms pending_blocks_actions
#assert_axioms respond_needs_pending
#assert_axioms respond_not_by_proposer
#assert_axioms offer_opens_pending
#assert_axioms respond_closes_pending
#assert_axioms used_monotone
#assert_axioms legal_needs_unused
#assert_axioms used_after_legal
#assert_axioms turns_applyLegal
#assert_axioms turns_applyResponse
#assert_axioms secret_is_scored
#assert_axioms geishaCount_mono
#assert_axioms control_correct
#assert_axioms won_iff_threshold
#assert_axioms won_needs_control
#assert_axioms not_won_blank
#assert_axioms winState_wins
#assert_axioms controlledBy_disjoint
#assert_axioms charmScore_add_le
#assert_axioms geishaScore_add_le
#assert_axioms not_both_charm_won
#assert_axioms not_both_guild_won
#assert_axioms won_can_be_mutual
#assert_axioms roundWinner_extends_Won
#assert_axioms roundWinner_sound
#assert_axioms roundWinner_draw_iff
#assert_axioms roundWinner_eq_branchWinner
#assert_axioms roundWinnerBranch_lt
#assert_axioms terminal_rule_reads_only_the_tallies
#assert_axioms undecidedState_not_Won
#assert_axioms undecidedState_adjudicates
#assert_axioms winState_roundWinner
#assert_axioms blankState_draws
-- ⚑ The three decisions.
#assert_axioms every_action_order_is_feasible
#assert_axioms allOrders_card
#assert_axioms orderFeasible_can_fail
#assert_axioms comp_balanced_cut_dominates
#assert_axioms gift_modest_cut_dominates
#assert_axioms cutState_response_legal
#assert_axioms respond_decides_the_round
#assert_axioms respond_changes_the_board
#assert_axioms cutState_self_deal_refused
#assert_axioms conservation_along_run
#assert_axioms multiwayTug_air_refines_applyAction
#assert_axioms air_functional

end Dregg2.Games.MultiwayTug
