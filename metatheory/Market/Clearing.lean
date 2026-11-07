/-
# Market.Clearing — DrEX rung 1: EXECUTION SOUNDNESS (the multilateral clearing theorem).

**DrEX — the Dragon's Egg Exchange** — is a Lean-first proof-carrying exchange: the exchange's
RULES are proven sound in Lean (this tower), and each execution INSTANCE will carry a proof it
obeyed them (the circuit layer). This module is rung 1 of that ladder: the matching/execution
core — a multilateral clearing that provably CONSERVES and is provably FAIR.

**The gap this fills, named by Dregg2 itself:** `Dregg2.Intent.Kernel.crossBid_needs_market`
proves a cross-asset bid (offer 5 gold, want 1 art) has NO bilateral fill — `¬ Converts offered
wanted` — "the fill is a *market* fact, not a resource fact." This module IS that market layer:
a **book** of intents cleared *multilaterally* — an allocation, one outcome per intent, that is
per-participant FAIR (every intent's own `predicate` accepts its outcome) and pool-CONSERVING
(the ⊗-pool of everything offered converts to the ⊗-pool of everything allocated, in the SAME
`Converts` relation the bilateral kernel uses — conservation is NOT redefined here).

## The DrEX ladder (Lean spec + refinement → execution theorems → private ZKP → settlement)

  * **Rung 1 (proved) — EXECUTION SOUNDNESS.** Three composed faces, two of which were ALREADY
    proved in `Dregg2/Intent/Ring.lean` and are REUSED, not re-proved: **conservation +
    atomicity** (`settleRing_conserves`: per-asset supply preserved across the whole ring;
    `settleRing_atomic`: any failing leg rolls back everything — backed by the real matcher,
    `intent/src/solver.rs`'s Johnson's-cycles + Shapley–Scarf TTC). THIS FILE adds the
    book-allocation face: `MarketClearing book` over `Intent R B reg stmtOf` books, with
    `clearing_conserves_per_asset` (the cleared book's per-asset Σ in = Σ out, composed through
    `KernelBridge.toBal` — the REAL per-asset ledger measure, not a new one), `clearing_fair`
    (every participant's own predicate accepts its outcome), `exact_clears_iff` (for exact
    books, a clearing exists IFF the offered pool equals the wanted pool — Σ-balance is exactly
    clearability), `ringClearing` (the 3-party ring containing the very `crossBid` the kernel
    proved bilaterally stuck CLEARS), and refusal teeth both ways (`mint_refused`: Σin ≠ Σout
    admits no clearing; `unfair_refused`: a pool-balanced but misrouted allocation admits no
    clearing). And `Market/Fairness.lean` adds the FAIRNESS half conservation cannot express —
    `clearing_respects_limits`: every participant of a solver-admitted cycle stays within its
    declaration on BOTH sides (debited only its offered asset, ≤ its offered amount — new;
    credited its wanted asset, ≥ its declared minimum — composed from Ring.lean's
    `cycle_individuallyRational`). This is DrEX's matching engine, as theorems.
  * **Rung 2 (NEXT, named not claimed) — ORDER-BOOK AGGREGATION SOUNDNESS.** The aggregated
    `Book` FAITHFULLY represents the submitted orders: no order dropped, none inserted, none
    reordered, and priority respected (price-time, or batch-uniform-price for a frequent-batch
    DrEX). This composes with Dregg2's existing ChainBound no-drop/no-insert/no-reorder
    light-client discipline (the grain-R3 stream shape) — reuse that shape over order streams,
    do not reinvent it. Also at rung 2: ledger realization — a cleared exact book induces a
    `RingBalanced` settlement whose `settleRing` commit conserves `recTotalAsset` (connect
    `MarketClearing` to `Intent/Ring.lean`'s solver-output keystones).
  * **Rung 3 (NORTH STAR, named) — SHIELDED CLEARING + the PRIVATE-MATCHING ZKP.** Two welds:
    (a) weave the shielded pool (`circuit-prove/src/shielded/pool.rs` — the standing
    "shielded pool not woven into effect_vm" seam) INTO the ring, so clearing happens over
    SHIELDED notes rather than cleartext balances; (b) the load-bearing custom-circuit surface:
    a ZKP that "this cleared allocation is the correct aggregation + execution of these
    COMMITTED (hidden) orders under the book rules" — without revealing the orders. Division of
    labor: the Lean tower (rungs 1–2) proves the RULES sound; the circuit proves an execution
    INSTANCE obeyed them privately, composing onto dregg's existing AIR/recursion layer
    (`chain/`, `circuit-prove/`): WHO traded is the nullifier layer's job; WHAT cleared
    correctly is this tower reflected in-circuit.
  * **Rung 4 (horizon) — cross-chain proof-settlement**: the cleared+proven batch settles
    through the existing light-client/settlement carriers.

  * **Floor (existing, composed with — NOT duplicated)** — `Dregg2.Intent`: `Converts`/⊗/`res`
    (`Resource.lean`), the four-faced `Intent`/`FillReceipt`/`fulfill` (`Core.lean`), the coend
    solver `Match`/`match_of_converts` (`Match.lean`), `settleIntent`/`settleReceipt`/`crossBid`
    (`Kernel.lean`), the ledger refinement `toBal`/`converts_refines_toBal`
    (`KernelBridge.lean`), and beneath those `Intent/Ring.lean`'s `settleRing_conserves` /
    `Exec/RecordKernel.lean`'s `recKExecAsset_conserves_per_asset` (the executable per-asset
    conservation this layer's Σ statement shadows through `toBal`). A singleton book's clearing
    is exactly a bilateral fill (`MarketClearing.ofFill` lifts `settleReceipt`; n = 1 recovers
    `settle_conserves`).

Also in the rung-2+ property catalog: no-arbitrage (no sub-book of a cleared book re-clears to
strictly enlarge any participant's allocation at others' expense), pooled-AMM solvency (a
standing pool as a family of clearings whose invariant is a `MarketClearing`-preserved measure),
and price existence for exact books.

Pure.
-/
import Dregg2.Intent.KernelBridge
import Dregg2.Intent.Match
import Dregg2.Tactics

universe v u

namespace Market

open CategoryTheory MonoidalCategory
open Dregg2.Intent
open Dregg2.Exec (AssetId)
open Dregg2.Time.Deadline (Deadline)
open Dregg2.Authority.Blocklace (Lace)
open Dregg2.Authority.Predicate (Registry)
open Dregg2.Time.Frame (FrameStatement)

/-! ## 1. Books and pools. -/

variable {R : Type u} {Stmt Wit : Type} {B : Lace} {reg : Registry Stmt Wit}
  {stmtOf : FrameStatement → Stmt}

/-- **A book** — the multilateral input: a list of intents over the SAME resource theory and
time-world (the standing orders the market clears together). Reuses `Dregg2.Intent.Intent`
verbatim — a book entry is exactly a kernel intent, four faces and all. -/
abbrev Book (R : Type u) {Stmt Wit : Type} (B : Lace) (reg : Registry Stmt Wit)
    (stmtOf : FrameStatement → Stmt) : Type u :=
  List (Intent R B reg stmtOf)

section Pool

variable [Category.{v} R] [MonoidalCategory R]

/-- **The pool** of a list of resources: their side-by-side ⊗-composite (`𝟙_` for the empty
list). This is the market's escrow-in-aggregate: what the book's participants put on the table,
as ONE resource object. Conservation of a clearing is stated as `Converts` between pools — the
SAME thin convertibility relation the bilateral kernel uses, lifted along `⊗` (which `Converts`
respects: `Converts.tensor`). -/
def pool (rs : List R) : R := rs.foldr (· ⊗ ·) (𝟙_ R)

@[simp] theorem pool_nil : pool ([] : List R) = 𝟙_ R := rfl

@[simp] theorem pool_cons (x : R) (xs : List R) : pool (x :: xs) = x ⊗ pool xs := rfl

end Pool

/-- Everything the book's intents OFFER, in book order. -/
def offersOf (book : Book R B reg stmtOf) : List R := book.map (·.offered)

/-- Everything the book's intents WANT, in book order. -/
def wantsOf (book : Book R B reg stmtOf) : List R := book.map (·.wanted)

@[simp] theorem offersOf_length (book : Book R B reg stmtOf) :
    (offersOf book).length = book.length := List.length_map ..

@[simp] theorem wantsOf_length (book : Book R B reg stmtOf) :
    (wantsOf book).length = book.length := List.length_map ..

/-! ## 2. `MarketClearing` — the multilateral matched allocation. -/

section Clearing

variable [Category.{v} R] [MonoidalCategory R]

/-- **A market clearing of a book** — the multilateral fill `crossBid_needs_market` demands:

  * `alloc` — ONE outcome resource per intent (positional: `alloc[i]` settles `book[i]`);
  * `fair` — EVERY participant's own `predicate` (face 2 of its intent) accepts its outcome:
    nobody is settled into an outcome they did not declare acceptable;
  * `balanced` — the offered pool converts to the allocated pool: `Converts (⊗ offered)
    (⊗ alloc)`. This is the bilateral kernel's OWN conservation relation
    (`Intent/Resource.lean`), applied at the pool grain — value moves BETWEEN participants but
    the market as a whole neither mints nor burns. (On the discrete demo theory this forces the
    pools' bundles EQUAL — the per-asset Σ theorem below.)

Deliberately NOT fields: per-intent `Converts offered[i] alloc[i]` — that is exactly the
bilateral fill the market exists to transcend (`ringBook_bilateral_stuck` below exhibits a
clearing whose every entry REFUSES it). -/
structure MarketClearing (book : Book R B reg stmtOf) where
  /-- The matched allocation: `alloc[i]` is what participant `i` receives. -/
  alloc : List R
  /-- One outcome per intent. -/
  len_eq : alloc.length = book.length
  /-- **Fairness** — each cleared intent's predicate is satisfied at its allocated outcome. -/
  fair : ∀ (i : ℕ) (hi : i < book.length),
    (book[i]'hi).predicate (alloc[i]'(by rw [len_eq]; exact hi))
  /-- **Conservation** — the offered pool converts to the allocated pool (the kernel's
  `Converts`, not a new relation). -/
  balanced : Converts (pool (offersOf book)) (pool alloc)

/-- **Fairness, as the named market law** — every cleared intent's predicate is satisfied by
what it receives ("each participant gets an outcome they accepted"). This is `MarketClearing`'s
validity condition surfaced as the API theorem; its TEETH — a pool-balanced but predicate-
violating allocation is NOT a clearing — is `unfair_refused` below. -/
theorem clearing_fair {book : Book R B reg stmtOf} (C : MarketClearing book)
    (i : ℕ) (hi : i < book.length) :
    (book[i]'hi).predicate (C.alloc[i]'(by rw [C.len_eq]; exact hi)) :=
  C.fair i hi

/-- **n = 1 recovers the bilateral kernel** — a fulfilled intent's receipt (`Intent/Core.lean`'s
`FillReceipt`, e.g. the auction's `settleReceipt`) IS a clearing of the singleton book: the
receipt's `satisfied` is the fairness face, and its `conversion` (whiskered by the empty pool,
`Converts.tensorRight`) is the balance face. The market layer conservatively extends `fulfill`;
it does not fork it. -/
def MarketClearing.ofFill (i : Intent R B reg stmtOf) (rcpt : FillReceipt i) :
    MarketClearing ([i] : Book R B reg stmtOf) where
  alloc := [rcpt.outcome]
  len_eq := rfl
  fair := fun k hk =>
    match k, hk with
    | 0, _ => rcpt.satisfied
    | n + 1, hk => absurd hk (by simp)
  balanced := Converts.tensorRight ⟨rcpt.conversion⟩ (𝟙_ R)

end Clearing

/-- **A clearing is a route in the SOLVER** — the coend `Match` (`Intent/Match.lean`, the
multi-hop router `∫^B (A⟶B)×(B⟶C)`) is populated at the pool boundary by any clearing's balance
witness (`match_of_converts`). The market layer plugs into the existing solver; it does not
re-invent routing. -/
theorem MarketClearing.route {R : Type u} [SmallCategory R] [MonoidalCategory R]
    {book : Book R B reg stmtOf} (C : MarketClearing book) :
    Nonempty (Match (pool (offersOf book)) (pool C.alloc)) :=
  match_of_converts C.balanced

/-! ## 3. The per-asset Σ conservation theorem (composing `KernelBridge.toBal`).

On the demo resource theory the pool balance refines to the REAL per-asset measure: the total
of each asset offered into the market equals the total allocated out, asset by asset. The Σ is
stated in `toBal` — `Intent/KernelBridge.lean`'s abstraction map onto the executable ledger's
`bal : CellId → AssetId → ℤ` columns — so this is the ledger's own conservation reading, not a
market-local invention. -/

/-- `toBal` is ADDITIVE over bundle union: the per-asset reading of `b * b'` (⊗ of bundles) is
the sum of the readings. This is what lets the pool's single `Converts` witness distribute into
a per-participant Σ. -/
theorem toBal_mul (b b' : Bundle) (a : AssetId) :
    toBal (b * b') a = toBal b a + toBal b' a := by
  unfold toBal
  rcases Decidable.em (a = 0) with h0 | h0
  · simp [h0]
  · rcases Decidable.em (a = 1) with h1 | h1
    · simp [h1]
    · simp [h0, h1]

/-- `toBal` of the empty bundle (`𝟙_`'s underlying `1`) reads `0` on every asset. -/
theorem toBal_unit (a : AssetId) : toBal (1 : Bundle) a = 0 := by
  unfold toBal
  rcases Decidable.em (a = 0) with h0 | h0
  · simp [h0]
  · rcases Decidable.em (a = 1) with h1 | h1
    · simp [h1]
    · simp [h0, h1]

/-- **The pool's per-asset reading is the Σ of its members'** — `toBal (⊗ rs) a = Σᵢ toBal rsᵢ a`.
The bridge from the one pool object to the per-participant sum. -/
theorem pool_toBal (rs : List DemoRes) (a : AssetId) :
    toBal (pool rs).as a = (rs.map (fun r => toBal r.as a)).sum := by
  induction rs with
  | nil => simpa using toBal_unit a
  | cons x xs ih =>
    have hx : (pool (x :: xs)).as = x.as * (pool xs).as := rfl
    rw [hx, toBal_mul, ih, List.map_cons, List.sum_cons]

/-- **THE CONSERVATION KEYSTONE — a market clearing conserves per asset: Σ in = Σ out.** For any
book over the demo resource theory and any clearing of it, and for EVERY asset `a`: the sum over
participants of what they OFFERED (read in the ledger measure `toBal`) equals the sum over
participants of what they were ALLOCATED. This lifts the bilateral `settle_conserves`
(`Converts offered outcome`, one intent) to the cleared SET, composing three existing pieces —
the clearing's pool witness (`balanced`), `KernelBridge.converts_refines_toBal` (the discrete
`Converts` forces the pools' per-asset readings equal), and `pool_toBal` (the pool reading
distributes into the Σ). FALSIFIER: a book whose only fair allocation inflates an asset (e.g.
`mintBook` below, wanting 8 gold against 7 offered) — for it, no `MarketClearing` exists at all
(`mint_refused`), which is exactly this theorem refusing to be satisfiable. -/
theorem clearing_conserves_per_asset {book : Book DemoRes B reg stmtOf}
    (C : MarketClearing book) (a : AssetId) :
    (book.map (fun i => toBal i.offered.as a)).sum
      = (C.alloc.map (fun r => toBal r.as a)).sum := by
  have h := converts_refines_toBal C.balanced
  have ha := congrFun h a
  rw [pool_toBal, pool_toBal] at ha
  simpa [offersOf, List.map_map, Function.comp_def] using ha

/-! ## 4. Exact books — clearability IS Σ-balance (the characterization). -/

/-- **An exact book**: every intent's predicate accepts EXACTLY its `wanted` (the grain of the
kernel demos — `settleIntent`, `crossBid` — and of a limit-order book: you get precisely what
you asked or nothing). -/
def ExactBook (book : Book DemoRes B reg stmtOf) : Prop :=
  ∀ (i : ℕ) (hi : i < book.length) (r : DemoRes),
    (book[i]'hi).predicate r ↔ r = (book[i]'hi).wanted

/-- In an exact book, fairness pins the WHOLE allocation: any clearing allocates each
participant exactly its `wanted`. (This is what makes `unfair_refused` bite: there is no room to
misroute a balanced pool.) -/
theorem exact_alloc_eq {book : Book DemoRes B reg stmtOf} (hex : ExactBook book)
    (C : MarketClearing book) : C.alloc = wantsOf book := by
  apply List.ext_getElem (by rw [C.len_eq]; simp [wantsOf])
  intro i h1 h2
  have hib : i < book.length := by rw [← C.len_eq]; exact h1
  have hf := (hex i hib _).mp (C.fair i hib)
  rw [hf]
  simp [wantsOf]

/-- **THE CHARACTERIZATION — an exact book clears IFF its pools balance** (`⊗ offered` and
`⊗ wanted` carry the same bundle, i.e. Σ in = Σ out on every asset simultaneously). Forward:
fairness pins the allocation to the wanteds (`exact_alloc_eq`) and the discrete `Converts`
forces pool equality. Backward: allocate everyone exactly their wanted; the pool equality IS the
conversion (`Discrete.eqToHom`). So for exact books, *clearability is exactly conservation* —
the market can clear anything that balances and NOTHING that doesn't. Both refusal teeth below
are corollaries. -/
theorem exact_clears_iff (book : Book DemoRes B reg stmtOf) (hex : ExactBook book) :
    Nonempty (MarketClearing book)
      ↔ (pool (offersOf book)).as = (pool (wantsOf book)).as := by
  constructor
  · rintro ⟨C⟩
    obtain ⟨f⟩ := C.balanced
    have h := Discrete.eq_of_hom f
    rwa [exact_alloc_eq hex C] at h
  · intro h
    exact ⟨{ alloc := wantsOf book
             len_eq := by simp [wantsOf]
             fair := fun i hi => by
               rw [hex i hi]
               simp [wantsOf]
             balanced := ⟨Discrete.eqToHom h⟩ }⟩

/-- An exact book whose pools do NOT balance admits no clearing — the refusal form of
`exact_clears_iff`, used by both teeth below. -/
theorem exact_refuses {book : Book DemoRes B reg stmtOf} (hex : ExactBook book)
    (h : (pool (offersOf book)).as ≠ (pool (wantsOf book)).as) :
    IsEmpty (MarketClearing book) :=
  ⟨fun C => h ((exact_clears_iff book hex).mp ⟨C⟩)⟩

/-! ## 5. NON-VACUITY, positive polarity — the 3-party ring CLEARS.

The book contains the kernel's own `crossBid` (offer 5 gold, want 1 art — the intent
`crossBid_needs_market` proves has NO bilateral fill), an art seller (offer 1 art, want 2 gold),
and a dealer capturing the 3-gold spread (offer 2 gold, want 5 gold). Offered pool = wanted pool
= (7 gold, 1 art). EVERY entry is bilaterally stuck and EVERY proper sub-book fails to balance —
the clearing is genuinely 3-multilateral. -/

/-- The art seller: offers 1 art, wants 2 gold (a cross-asset ask — bilaterally unfillable). -/
def artSeller : KernelIntent Dregg2.Authority.Blocklace.demoLace demoReg demoStmtOf where
  offered := res 0 1
  wanted := res 2 0
  predicate := fun r => r = res 2 0
  resource := EscrowWitness.fund (res 0 1)
  validity := Deadline.causalAfter Dregg2.Authority.Blocklace.g0

/-- The dealer: offers 2 gold, wants 5 gold — the market maker whose 3-gold margin is exactly
the bid-ask spread between `crossBid` (pays 5 gold for the art) and `artSeller` (asks 2). Same-
asset and unequal, so ALSO bilaterally unfillable; only the ring pays it. -/
def dealer : KernelIntent Dregg2.Authority.Blocklace.demoLace demoReg demoStmtOf where
  offered := res 2 0
  wanted := res 5 0
  predicate := fun r => r = res 5 0
  resource := EscrowWitness.fund (res 2 0)
  validity := Deadline.causalAfter Dregg2.Authority.Blocklace.g0

/-- **The ring book**: the kernel's bilaterally-stuck `crossBid`, plus the two counterparties
that close it. -/
def ringBook : Book DemoRes Dregg2.Authority.Blocklace.demoLace demoReg demoStmtOf :=
  [crossBid, artSeller, dealer]

/-- The ring book is exact (all three predicates are `= wanted`). -/
theorem ringBook_exact : ExactBook ringBook := fun i hi _r =>
  match i, hi with
  | 0, _ => Iff.rfl
  | 1, _ => Iff.rfl
  | 2, _ => Iff.rfl

/-- **EVERY entry of the ring book is bilaterally STUCK** — no `Converts offered wanted` for any
of the three (entry 0 is literally the kernel's `crossBid_needs_market`). This is the
before-picture: the bilateral kernel refuses all three fills individually. -/
theorem ringBook_bilateral_stuck :
    ∀ (i : ℕ) (hi : i < ringBook.length),
      ¬ Converts (ringBook[i]'hi).offered (ringBook[i]'hi).wanted := fun i hi =>
  match i, hi with
  | 0, _ => crossBid_needs_market
  | 1, _ => res_no_convert (by decide)
  | 2, _ => res_no_convert (by decide)

/-- **THE MARKET CLEARS THE RING** — the allocation `[1 art → crossBid, 2 gold → artSeller,
5 gold → dealer]`. Fair (each gets exactly what its predicate demands) and balanced (both pools
carry the bundle (7 gold, 1 art)). The multilateral fill that `crossBid_needs_market` said only
a market can provide, provided. -/
def ringClearing : MarketClearing ringBook where
  alloc := [res 0 1, res 2 0, res 5 0]
  len_eq := rfl
  fair := fun i hi =>
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
  balanced := ⟨Discrete.eqToHom (by decide)⟩

/-- The ring clearing's conservation, instantiated: for every asset, Σ offered = Σ allocated
across the three participants (7 gold in/out, 1 art in/out) — `clearing_conserves_per_asset` on
a real multilateral example. -/
theorem ringClearing_conserves (a : AssetId) :
    (ringBook.map (fun i => toBal i.offered.as a)).sum
      = (ringClearing.alloc.map (fun r => toBal r.as a)).sum :=
  clearing_conserves_per_asset ringClearing a

/-- The ring clearing is a route in the coend solver: `Match (⊗ offered) (⊗ alloc)` is
inhabited. The market's output is solver-shaped. -/
theorem ringClearing_route :
    Nonempty (Match (pool (offersOf ringBook)) (pool ringClearing.alloc)) :=
  ringClearing.route

/-- **The ring is GENUINELY 3-multilateral** — every 2-party sub-book of it fails to clear
(pools don't balance pairwise), so all three participants are needed. Together with
`ringBook_bilateral_stuck` (1-party fails) and `ringClearing` (3-party succeeds), the market
layer is doing something the bilateral kernel provably cannot. -/
theorem ring_pairs_refused :
    IsEmpty (MarketClearing ([crossBid, artSeller] :
        Book DemoRes Dregg2.Authority.Blocklace.demoLace demoReg demoStmtOf))
      ∧ IsEmpty (MarketClearing ([crossBid, dealer] :
        Book DemoRes Dregg2.Authority.Blocklace.demoLace demoReg demoStmtOf))
      ∧ IsEmpty (MarketClearing ([artSeller, dealer] :
        Book DemoRes Dregg2.Authority.Blocklace.demoLace demoReg demoStmtOf)) := by
  refine ⟨exact_refuses ?_ (by decide), exact_refuses ?_ (by decide),
    exact_refuses ?_ (by decide)⟩ <;>
    exact fun i hi _r =>
      match i, hi with
      | 0, _ => Iff.rfl
      | 1, _ => Iff.rfl

/-! ## 6. NON-VACUITY, negative polarity — the teeth. -/

/-- **TOOTH (bilateral echo):** the singleton book `[crossBid]` has NO market clearing — the
market layer does not conjure counterparties; without them the cross-bid stays stuck, exactly as
`crossBid_needs_market` says. -/
theorem crossBid_alone_refused :
    IsEmpty (MarketClearing ([crossBid] :
      Book DemoRes Dregg2.Authority.Blocklace.demoLace demoReg demoStmtOf)) :=
  exact_refuses
    (fun i hi _r => match i, hi with | 0, _ => Iff.rfl)
    (by decide)

/-- The greedy dealer: offers 2 gold but demands 6 — one more gold than the ring's pool holds.
Its book would MINT a gold if "cleared". -/
def greedyDealer : KernelIntent Dregg2.Authority.Blocklace.demoLace demoReg demoStmtOf where
  offered := res 2 0
  wanted := res 6 0
  predicate := fun r => r = res 6 0
  resource := EscrowWitness.fund (res 2 0)
  validity := Deadline.causalAfter Dregg2.Authority.Blocklace.g0

/-- The mint book: the ring with the dealer replaced by its greedy twin — offered pool
(7 gold, 1 art), wanted pool (8 gold, 1 art). Σ in ≠ Σ out. -/
def mintBook : Book DemoRes Dregg2.Authority.Blocklace.demoLace demoReg demoStmtOf :=
  [crossBid, artSeller, greedyDealer]

/-- **TOOTH (conservation): a non-conserving "clearing" is REFUSED.** The mint book — whose only
fair allocation would create a gold out of nothing (Σ in = 7 < Σ out = 8 on asset 0) — admits NO
`MarketClearing` at all. The market cannot be talked into minting: `balanced` is the kernel's
`Converts`, and the discrete resource theory has no conversion between unequal pools. -/
theorem mint_refused : IsEmpty (MarketClearing mintBook) :=
  exact_refuses
    (fun i hi _r =>
      match i, hi with
      | 0, _ => Iff.rfl
      | 1, _ => Iff.rfl
      | 2, _ => Iff.rfl)
    (by decide)

/-- **TOOTH (fairness): a pool-BALANCED but MISROUTED allocation is refused.** The candidate
`[2 gold → crossBid, 1 art → artSeller, 5 gold → dealer]` carries the SAME pool (7 gold, 1 art)
as the honest clearing — conservation alone would wave it through (see the `#guard` below) — but
it hands `crossBid` gold when its predicate demands the art. NO clearing of the ring book
allocates this way: fairness pins every exact book's allocation to the wanteds
(`exact_alloc_eq`). Conservation and fairness are independent teeth. -/
theorem unfair_refused (C : MarketClearing ringBook) :
    C.alloc ≠ [res 2 0, res 0 1, res 5 0] := by
  rw [exact_alloc_eq ringBook_exact C]
  intro h
  have h0 := congrArg (fun l => l.map (fun r : DemoRes => r.as.toAdd)) h
  exact absurd h0 (by decide)

/-! ### `#eval`/`#guard` smoke — the cleared allocation is computed, not asserted. -/

-- the ring's pools both carry (7 gold, 1 art):
#guard (pool (offersOf ringBook)).as.toAdd == (7, 1)
#guard (pool (wantsOf ringBook)).as.toAdd == (7, 1)
#guard (pool ringClearing.alloc).as.toAdd == (7, 1)
-- the concrete cleared allocation, per participant:
#guard (ringClearing.alloc.map (fun r => r.as.toAdd)) == [(0, 1), (2, 0), (5, 0)]
-- per-asset Σ, computed both ways (asset 0 = gold: 7; asset 1 = art: 1):
#guard (ringBook.map (fun i => toBal i.offered.as 0)).sum == 7
#guard (ringClearing.alloc.map (fun r => toBal r.as 0)).sum == 7
#guard (ringBook.map (fun i => toBal i.offered.as 1)).sum == 1
#guard (ringClearing.alloc.map (fun r => toBal r.as 1)).sum == 1
-- the mint book's pools DISAGREE (8 gold demanded of 7 offered):
#guard (pool (offersOf mintBook)).as.toAdd == (7, 1)
#guard (pool (wantsOf mintBook)).as.toAdd == (8, 1)
-- the unfair candidate is pool-balanced — only FAIRNESS refuses it:
#guard (pool [res 2 0, res 0 1, res 5 0]).as.toAdd == (7, 1)

/-! ### The n = 1 embedding, concretely: the auction's settle is a singleton clearing. -/

/-- The kernel's `settleIntent`/`settleReceipt` (the auction's winning allocation), lifted to a
singleton-book clearing — the market layer contains the bilateral kernel as its n = 1 case. -/
def settleClearing : MarketClearing ([settleIntent] :
    Book DemoRes Dregg2.Authority.Blocklace.demoLace demoReg demoStmtOf) :=
  .ofFill settleIntent settleReceipt

#guard (settleClearing.alloc.map (fun r => r.as.toAdd)) == [(0, 3)]

/-! ### Axiom hygiene — pin the market keystones to the three kernel axioms. -/

#assert_all_clean [Market.clearing_fair, Market.clearing_conserves_per_asset,
  Market.pool_toBal, Market.exact_alloc_eq, Market.exact_clears_iff, Market.exact_refuses,
  Market.ringBook_exact, Market.ringBook_bilateral_stuck, Market.ringClearing_conserves,
  Market.ringClearing_route, Market.ring_pairs_refused, Market.crossBid_alone_refused,
  Market.mint_refused, Market.unfair_refused]

end Market
