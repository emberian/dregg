/-
# Market.DarkBazaarPrivateDescriptor

The first fixed-shape Dark Bazaar proof family whose order values are private
witness columns rather than public Cert-F coefficients.

Family: exactly four committed slots (zero-quantity padding is canonical at the
Rust boundary), four price buckets, quantities in `[0,15]`, and a fixed rule id.
Public inputs are only `(session, rule, orderRoot[0..8), pStar, vStar)`.  Each private
order is an eight-way one-hot `(bid/ask × limit 0..3)` plus a four-bit quantity.
The four seven-bit order codes are injectively packed into one 28-bit felt.  A
single domain-separated full-arity Poseidon2 permutation absorbs
`(session,rule,packedBook)`, eight canonical blind felts, and four explicit zero
framing lanes, exposing all eight output lanes (~248 bits, ~124-bit collision
work).  There is no narrow intermediate carrier.

The AIR recomputes all four demand/supply buckets, each `min(D,S)`, the maximum
volume, and the LOWEST maximizing price.  No order value occurs in descriptor
constants or public inputs.  Rust only fills this Lean-authored layout and proves
the emitted descriptor.
-/
import Market.FhEggClearing
import Market.PackedBookFamily
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Tactics

namespace Market.DarkBazaarPrivateDescriptor

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.CaveatBignum (bignumVal Ranged)
open Dregg2.Bignum.DigitInjective (bignumVal_injective)
open Market.PackedBookFamily (bignumVal_ofFn)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 TableId TraceFamily VmTrace Satisfied2
    ChipTableSoundN chipLookupTupleN chip_lookup_sound_N envAt emitVmJson2)

set_option autoImplicit false

/-! ## 1. Exact semantic certificate checker. -/

def ORDER_COUNT : Nat := 4
def PRICE_COUNT : Nat := 4
def QTY_BITS : Nat := 4
def DIFF_BITS : Nat := 6

def DIGEST_WIDTH : Nat := 8

/-- Poseidon input domain separator for this exact commitment encoding. -/
def ROOT_DOMAIN_TAG : Int := 1145194322

def BABYBEAR_MODULUS : Int := 2013265921

/-- Stable public rule/domain separator for `N=4,K=4,qty<16,lowest-price-tie`. -/
def RULE_ID : Int := 1430520836

/-- Private order code: `kind<4` is a bid at `kind`; `kind>=4` is an ask at `kind-4`. -/
structure PrivateOrder where
  kind : Fin 8
  qty : Fin 16
  deriving DecidableEq, Repr

structure PrivateWitness where
  orders : Fin 4 → PrivateOrder
  blinding : Fin 8 → Int

structure PublicStatement where
  session : Int
  rule : Int
  orderRoot : Fin 8 → Int
  pStar : Nat
  vStar : Int
  deriving DecidableEq, Repr

def PrivateOrder.toLimitOrder (o : PrivateOrder) : LimitOrder where
  side := if o.kind.val < 4 then .bid else .ask
  qty := o.qty.val
  limit := o.kind.val % 4

def privateBook (w : PrivateWitness) : OrderBook :=
  List.ofFn (fun i : Fin 4 => (w.orders i).toLimitOrder)

/-- Host integers for blind limbs are canonical field representatives.  This
rules out the trivial `b` versus `b + p` alias before the cryptographic binding
assumption is even discussed. -/
def CanonicalBlinding (w : PrivateWitness) : Prop :=
  ∀ i, 0 ≤ w.blinding i ∧ w.blinding i < BABYBEAR_MODULUS

def canonicalBlindingCheck (w : PrivateWitness) : Bool :=
  (List.ofFn w.blinding).all fun z => decide (0 ≤ z ∧ z < BABYBEAR_MODULUS)

theorem canonicalBlindingCheck_iff (w : PrivateWitness) :
    canonicalBlindingCheck w = true ↔ CanonicalBlinding w := by
  simp [canonicalBlindingCheck, CanonicalBlinding]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ i
    fin_cases i <;> assumption
  · intro h
    exact ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6, h 7⟩

/-- Seven-bit injective order code: `kind + 8*qty ∈ [0,127]`. -/
def orderCode (o : PrivateOrder) : Int := o.kind.val + 8 * o.qty.val

theorem orderCode_injective : Function.Injective orderCode := by
  intro left right h
  have hkind : left.kind.val = right.kind.val := by
    simp only [orderCode] at h
    have hl := left.kind.isLt
    have hr := right.kind.isLt
    omega
  have hqty : left.qty.val = right.qty.val := by
    simp only [orderCode] at h
    omega
  cases left with
  | mk lk lq =>
    cases right with
    | mk rk rq =>
      cases Fin.ext hkind
      cases Fin.ext hqty
      rfl

/-- Four base-128 digits, hence `< 128^4 = 2^28 < BabyBear`. -/
def packedBook (w : PrivateWitness) : Int :=
  (List.ofFn (fun i : Fin 4 => (128 : Int) ^ i.val * orderCode (w.orders i))).sum

/-- The book's digit list — one base-128 limb per committed slot. -/
def bookLimbs (w : PrivateWitness) : List Int :=
  List.ofFn (fun i : Fin 4 => orderCode (w.orders i))

/-- **The pack IS a bignum.**  The positional sum the AIR emits (`Σ 128ⁱ · ORDER_PACKᵢ`) and the
base-128 limb denotation `bignumVal` are the same object — by `bignumVal_ofFn`, which is proved
by induction on the limb count, so this bridge does not know `4` either. -/
theorem packedBook_eq_bignumVal (w : PrivateWitness) :
    packedBook w = bignumVal 128 (bookLimbs w) := by
  rw [bookLimbs, bignumVal_ofFn]
  rfl

/-- Every committed slot is a legal base-128 digit — the per-limb range side condition the
injectivity keystone consumes.  Stated over an arbitrary slot index, not four of them. -/
theorem bookLimbs_ranged (w : PrivateWitness) : Ranged 128 (bookLimbs w) := by
  intro z hz
  simp only [bookLimbs, List.mem_ofFn] at hz
  obtain ⟨i, hi⟩ := hz
  subst hi
  simp only [orderCode]
  have hk := (w.orders i).kind.isLt
  have hq := (w.orders i).qty.isLt
  omega

/-- The committed 28-bit pack loses no fixed-slot order information.

This is a MULTI-LIMB argument, not an enumeration: `bignumVal_injective` inducts over the limb
list once, at every width, and the per-slot inversion is `orderCode_injective`.  The previous
proof wrote the four-digit sum out literally and handed eight bound hypotheses to `omega`, which
is why the family could not be resized — that proof cost grows with the square of the slot count
and says nothing about any other `N`.  See `Market.PackedBookFamily` for the parametric form and
for the multi-FELT pack a game-sized family needs. -/
theorem packedBook_injective_on_orders {left right : PrivateWitness}
    (hpack : packedBook left = packedBook right) : left.orders = right.orders := by
  rw [packedBook_eq_bignumVal, packedBook_eq_bignumVal] at hpack
  have hlists : bookLimbs left = bookLimbs right :=
    bignumVal_injective (by norm_num) (bookLimbs left) (bookLimbs right)
      (by simp [bookLimbs]) (bookLimbs_ranged left) (bookLimbs_ranged right) hpack
  have hfun : (fun i : Fin 4 => orderCode (left.orders i)) =
      fun i : Fin 4 => orderCode (right.orders i) :=
    List.ofFn_inj.mp hlists
  funext i
  exact orderCode_injective (congrFun hfun i)

/-- Canonical source commitment input.  Twelve meaningful inputs plus four
explicit zero framing lanes use the chip's full arity-16 seed mode, so every
blind limb is absorbed and no scalar intermediate can launder the width. -/
def rootPreimage (session : Int) (w : PrivateWitness) : List Int :=
  [ROOT_DOMAIN_TAG, session, RULE_ID, packedBook w] ++ List.ofFn w.blinding ++ [0, 0, 0, 0]

/-- Canonical eight-felt source commitment. -/
def orderRoot (hash8 : List Int → Fin 8 → Int) (session : Int) (w : PrivateWitness) : Fin 8 → Int :=
  hash8 (rootPreimage session w)

/-- The exact bad event behind the external commitment-binding claim: two distinct
packed source openings for one session produce the same root.  We deliberately do
NOT assert that a field-valued Poseidon map is injective (it cannot be globally
injective at finite cardinality).  Protocol binding is the computational
assumption that no feasible adversary finds a value of this predicate. -/
def RootCollision (hash8 : List Int → Fin 8 → Int) (session : Int)
    (left right : PrivateWitness) : Prop :=
  (packedBook left ≠ packedBook right ∨ left.blinding ≠ right.blinding) ∧
  orderRoot hash8 session left = orderRoot hash8 session right

/-- The exact private-order statement checked by the family. -/
def Accepts (hash8 : List Int → Fin 8 → Int) (pub : PublicStatement) (w : PrivateWitness) : Prop :=
  CanonicalBlinding w ∧
  pub.rule = RULE_ID ∧
  pub.orderRoot = orderRoot hash8 pub.session w ∧
  pub.pStar = crossing (privateBook w) PRICE_COUNT ∧
  pub.vStar = clearedVolume (privateBook w) PRICE_COUNT

/-- Executable, exact certificate checker authored in Lean. -/
def check (hash8 : List Int → Fin 8 → Int) (pub : PublicStatement) (w : PrivateWitness) : Bool :=
  canonicalBlindingCheck w &&
  (pub.rule == RULE_ID) &&
  (pub.orderRoot == orderRoot hash8 pub.session w) &&
  (pub.pStar == crossing (privateBook w) PRICE_COUNT) &&
  (pub.vStar == clearedVolume (privateBook w) PRICE_COUNT)

theorem check_iff (hash8 : List Int → Fin 8 → Int) (pub : PublicStatement) (w : PrivateWitness) :
    check hash8 pub w = true ↔ Accepts hash8 pub w := by
  simp [check, Accepts, canonicalBlindingCheck_iff, and_assoc]

/-- Earlier buckets are strictly below `argmaxUpto`: this is the formal
lowest-price tie tooth missing from the older output-only join. -/
theorem argmaxUpto_strict_before (bk : OrderBook) :
    ∀ n q, q < argmaxUpto bk n → execVol bk q < execVol bk (argmaxUpto bk n) := by
  intro n
  induction n with
  | zero =>
      intro q hq
      simp [argmaxUpto] at hq
  | succ n ih =>
      intro q hq
      by_cases h : execVol bk (argmaxUpto bk n) < execVol bk (n + 1)
      · have harg : argmaxUpto bk (n + 1) = n + 1 := by
          simp [argmaxUpto, h]
        rw [harg] at hq ⊢
        exact lt_of_le_of_lt (argmaxUpto_max bk n q (by omega)) h
      · have harg : argmaxUpto bk (n + 1) = argmaxUpto bk n := by
          simp [argmaxUpto, h]
        rw [harg] at hq ⊢
        exact ih q hq

theorem crossing_strict_before (bk : OrderBook) {q : Nat}
    (hq : q < crossing bk PRICE_COUNT) :
    execVol bk q < clearedVolume bk PRICE_COUNT := by
  exact argmaxUpto_strict_before bk (PRICE_COUNT - 1) q hq

/-- **Checker soundness.** Acceptance binds the opened private orders to the
public root and makes `(pStar,vStar)` the exact deterministic volume argmax,
including strict dominance over every earlier bucket. -/
theorem check_sound {hash8 : List Int → Fin 8 → Int} {pub : PublicStatement} {w : PrivateWitness}
    (h : check hash8 pub w = true) :
    CanonicalBlinding w ∧
    pub.rule = RULE_ID ∧
    pub.orderRoot = orderRoot hash8 pub.session w ∧
    pub.pStar = crossing (privateBook w) PRICE_COUNT ∧
    pub.vStar = clearedVolume (privateBook w) PRICE_COUNT ∧
    (∀ q < PRICE_COUNT, execVol (privateBook w) q ≤ pub.vStar) ∧
    (∀ q < pub.pStar, execVol (privateBook w) q < pub.vStar) := by
  have ha : Accepts hash8 pub w := (check_iff hash8 pub w).mp h
  rcases ha with ⟨hcanon, hrule, hroot, hp, hV⟩
  refine ⟨hcanon, hrule, hroot, hp, hV, ?_, ?_⟩
  · intro q hq
    rw [hV]
    exact clearedVolume_optimal (privateBook w) PRICE_COUNT hq
  · intro q hq
    rw [hp] at hq
    rw [hV]
    exact crossing_strict_before (privateBook w) hq

/-- Two accepted, distinct source openings for the same public statement reduce
directly to a commitment collision.  This is the formal boundary: exact checker
soundness is unconditional; uniqueness of the opening is computational Poseidon
binding and is never smuggled in as a false field-level injectivity theorem. -/
theorem two_distinct_openings_yield_root_collision
    {hash8 : List Int → Fin 8 → Int} {pub : PublicStatement} {left right : PrivateWitness}
    (hl : check hash8 pub left = true) (hr : check hash8 pub right = true)
    (hdiff : packedBook left ≠ packedBook right ∨ left.blinding ≠ right.blinding) :
    RootCollision hash8 pub.session left right := by
  have al := (check_iff hash8 pub left).mp hl
  have ar := (check_iff hash8 pub right).mp hr
  exact ⟨hdiff, al.2.2.1.symm.trans ar.2.2.1⟩

/-! A non-vacuous executable workbook and tamper teeth. -/

def fixtureOrder (i : Fin 4) : PrivateOrder :=
  match i.val with
  | 0 => ⟨⟨2, by omega⟩, ⟨10, by omega⟩⟩ -- bid 10 @ 2
  | 1 => ⟨⟨1, by omega⟩, ⟨6, by omega⟩⟩  -- bid 6 @ 1
  | 2 => ⟨⟨4, by omega⟩, ⟨5, by omega⟩⟩  -- ask 5 @ 0
  | _ => ⟨⟨5, by omega⟩, ⟨8, by omega⟩⟩  -- ask 8 @ 1

def fixtureWitness : PrivateWitness := ⟨fixtureOrder, fun i => 777 + i.val⟩
def toyHash8 (xs : List Int) (lane : Fin 8) : Int := xs.sum + 17 + lane.val
def fixturePublic : PublicStatement where
  session := 99
  rule := RULE_ID
  orderRoot := orderRoot toyHash8 99 fixtureWitness
  pStar := 1
  vStar := 13

def tamperedOrderWitness : PrivateWitness where
  orders := fun i => if i = 0 then ⟨⟨2, by omega⟩, ⟨11, by omega⟩⟩ else fixtureOrder i
  blinding := fixtureWitness.blinding

def noncanonicalBlindWitness : PrivateWitness where
  orders := fixtureWitness.orders
  blinding := fun i => if i = 0 then BABYBEAR_MODULUS else fixtureWitness.blinding i

#guard check toyHash8 fixturePublic fixtureWitness
#guard !check toyHash8 { fixturePublic with orderRoot := fun i => fixturePublic.orderRoot i + 1 }
  fixtureWitness
#guard !check toyHash8 { fixturePublic with pStar := 2 } fixtureWitness
#guard !check toyHash8 { fixturePublic with vStar := 12 } fixtureWitness
#guard !check toyHash8 fixturePublic tamperedOrderWitness
#guard !check toyHash8 fixturePublic noncanonicalBlindWitness

/-! ## 2. Lean-authored fixed AIR descriptor. -/

/- Column layout.  Public: session/rule 0..1, root8 2..9, p*/V* 10..11.
Private blind8: 12..19. Private order rows: 21..76. -/
def SESSION : Nat := 0
def RULE : Nat := 1
def ROOT_BASE : Nat := 2
def PSTAR : Nat := 10
def VSTAR : Nat := 11
def BLINDING_BASE : Nat := 12
def PACKED_BOOK : Nat := 20

def ROOT (lane : Nat) : Nat := ROOT_BASE + lane
def BLINDING (lane : Nat) : Nat := BLINDING_BASE + lane

def ORDER_BASE : Nat := 21
def ORDER_STRIDE : Nat := 14
def KIND (i t : Nat) : Nat := ORDER_BASE + ORDER_STRIDE * i + t
def QTY (i : Nat) : Nat := ORDER_BASE + ORDER_STRIDE * i + 8
def QTY_BIT (i b : Nat) : Nat := ORDER_BASE + ORDER_STRIDE * i + 9 + b
def ORDER_PACK (i : Nat) : Nat := ORDER_BASE + ORDER_STRIDE * i + 13

def DEMAND_BASE : Nat := 77
def SUPPLY_BASE : Nat := 81
def VOLUME_BASE : Nat := 85
def MIN_CHOOSE_BASE : Nat := 89
def MIN_DIFF_BASE : Nat := 93
def MIN_DIFF_BITS_BASE : Nat := 97
def SELECT_BASE : Nat := 121
def MAX_DIFF_BASE : Nat := 125
def MAX_DIFF_BITS_BASE : Nat := 129
def LOW_SLACK_BASE : Nat := 153
def LOW_SLACK_BITS_BASE : Nat := 157
def TRACE_WIDTH : Nat := 181

def DEMAND (p : Nat) : Nat := DEMAND_BASE + p
def SUPPLY (p : Nat) : Nat := SUPPLY_BASE + p
def VOLUME (p : Nat) : Nat := VOLUME_BASE + p
def MIN_CHOOSE (p : Nat) : Nat := MIN_CHOOSE_BASE + p
def MIN_DIFF (p : Nat) : Nat := MIN_DIFF_BASE + p
def MIN_DIFF_BIT (p b : Nat) : Nat := MIN_DIFF_BITS_BASE + DIFF_BITS * p + b
def SELECT (p : Nat) : Nat := SELECT_BASE + p
def MAX_DIFF (p : Nat) : Nat := MAX_DIFF_BASE + p
def MAX_DIFF_BIT (p b : Nat) : Nat := MAX_DIFF_BITS_BASE + DIFF_BITS * p + b
def LOW_SLACK (p : Nat) : Nat := LOW_SLACK_BASE + p
def LOW_SLACK_BIT (p b : Nat) : Nat := LOW_SLACK_BITS_BASE + DIFF_BITS * p + b

def v (col : Nat) : EmittedExpr := .var col
def c (z : Int) : EmittedExpr := .const z
def add (x y : EmittedExpr) : EmittedExpr := .add x y
def mul (x y : EmittedExpr) : EmittedExpr := .mul x y
def neg (x : EmittedExpr) : EmittedExpr := mul (c (-1)) x
def sub (x y : EmittedExpr) : EmittedExpr := add x (neg y)
def sumE (xs : List EmittedExpr) : EmittedExpr := xs.foldr add (c 0)
def weighted (k : Int) (x : EmittedExpr) : EmittedExpr := mul (c k) x

def binaryBody (col : Nat) : EmittedExpr := mul (v col) (sub (v col) (c 1))

def recompose (col : Nat) (bit : Nat → Nat) (bits : Nat) : EmittedExpr :=
  sub (sumE ((List.range bits).map (fun b => weighted ((2 : Int) ^ b) (v (bit b))))) (v col)

def kindValue (i : Nat) : EmittedExpr :=
  sumE ((List.range 8).map (fun (t : Nat) => weighted (t : Int) (v (KIND i t))))

def bidActive (i p : Nat) : EmittedExpr :=
  sumE ((List.range (4 - p)).map (fun j => v (KIND i (p + j))))

def askActive (i p : Nat) : EmittedExpr :=
  sumE ((List.range (p + 1)).map (fun j => v (KIND i (4 + j))))

def demandExpr (p : Nat) : EmittedExpr :=
  sumE ((List.range 4).map (fun i => mul (v (QTY i)) (bidActive i p)))

def supplyExpr (p : Nat) : EmittedExpr :=
  sumE ((List.range 4).map (fun i => mul (v (QTY i)) (askActive i p)))

def laterSelected (p : Nat) : EmittedExpr :=
  sumE ((List.range (3 - p)).map (fun j => v (SELECT (p + 1 + j))))

def orderBodies (i : Nat) : List EmittedExpr :=
  ((List.range 8).map (fun t => binaryBody (KIND i t))) ++
  [ sub (sumE ((List.range 8).map (fun t => v (KIND i t)))) (c 1)
  , recompose (QTY i) (QTY_BIT i) QTY_BITS ] ++
  ((List.range QTY_BITS).map (fun b => binaryBody (QTY_BIT i b))) ++
  [sub (v (ORDER_PACK i)) (add (kindValue i) (weighted 8 (v (QTY i))))]

def priceBodies (p : Nat) : List EmittedExpr :=
  [ sub (v (DEMAND p)) (demandExpr p)
  , sub (v (SUPPLY p)) (supplyExpr p)
  , binaryBody (MIN_CHOOSE p)
  , sub (v (VOLUME p))
      (add (mul (v (MIN_CHOOSE p)) (v (DEMAND p)))
        (mul (sub (c 1) (v (MIN_CHOOSE p))) (v (SUPPLY p))))
  , sub (v (MIN_DIFF p))
      (add (mul (v (MIN_CHOOSE p)) (sub (v (SUPPLY p)) (v (DEMAND p))))
        (mul (sub (c 1) (v (MIN_CHOOSE p))) (sub (v (DEMAND p)) (v (SUPPLY p)))))
  , recompose (MIN_DIFF p) (MIN_DIFF_BIT p) DIFF_BITS ] ++
  ((List.range DIFF_BITS).map (fun b => binaryBody (MIN_DIFF_BIT p b))) ++
  [ binaryBody (SELECT p)
  , sub (v (MAX_DIFF p)) (sub (v VSTAR) (v (VOLUME p)))
  , recompose (MAX_DIFF p) (MAX_DIFF_BIT p) DIFF_BITS ] ++
  ((List.range DIFF_BITS).map (fun b => binaryBody (MAX_DIFF_BIT p b))) ++
  [ sub (v (LOW_SLACK p)) (sub (v (MAX_DIFF p)) (laterSelected p))
  , recompose (LOW_SLACK p) (LOW_SLACK_BIT p) DIFF_BITS ] ++
  ((List.range DIFF_BITS).map (fun b => binaryBody (LOW_SLACK_BIT p b)))

def semanticBodies : List EmittedExpr :=
  [ sub (v RULE) (c RULE_ID)
  , sub (v PACKED_BOOK)
      (sumE ((List.range 4).map (fun i => weighted ((128 : Int) ^ i) (v (ORDER_PACK i))))) ] ++
  ((List.range 4).flatMap orderBodies) ++
  ((List.range 4).flatMap priceBodies) ++
  [ sub (sumE ((List.range 4).map (fun p => v (SELECT p)))) (c 1)
  , sub (v PSTAR)
      (sumE ((List.range 4).map (fun (p : Nat) => weighted (p : Int) (v (SELECT p)))))
  , sub (v VSTAR)
      (sumE ((List.range 4).map (fun p => mul (v (SELECT p)) (v (VOLUME p))))) ]

def rootInputExprs : List EmittedExpr :=
  [c ROOT_DOMAIN_TAG, v SESSION, v RULE, v PACKED_BOOK] ++
    (List.range DIGEST_WIDTH).map (fun i => v (BLINDING i)) ++ [c 0, c 0, c 0, c 0]

def rootDigestCols : List Nat := (List.range DIGEST_WIDTH).map ROOT

def rootLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2, chipLookupTupleN rootInputExprs rootDigestCols⟩

def hashLookups : List VmConstraint2 := [rootLookup]

def publicPins : List VmConstraint2 :=
  [ .base (.piBinding .first SESSION 0)
  , .base (.piBinding .first RULE 1) ] ++
  (List.range DIGEST_WIDTH).map (fun i => .base (.piBinding .first (ROOT i) (2 + i))) ++
  [ .base (.piBinding .first PSTAR 10)
  , .base (.piBinding .first VSTAR 11) ]

/-- Gates are transition-domain plus an exact last-row copy, avoiding the
height-one/last-row semantic drop that older descriptors suffered. -/
def darkBazaarPrivateN4K4Descriptor : EffectVmDescriptor2 :=
  { name := "dark-bazaar-private-n4k4::wide-poseidon2-v2"
  , traceWidth := TRACE_WIDTH
  , piCount := 12
  , tables := []
  , constraints := hashLookups ++
      semanticBodies.map (fun body => .base (.gate body)) ++ publicPins ++
      semanticBodies.map (fun body => .base (.boundary .last body))
  , hashSites := []
  , ranges := [] }

#guard darkBazaarPrivateN4K4Descriptor.traceWidth == 181
#guard darkBazaarPrivateN4K4Descriptor.piCount == 12
#guard hashLookups.length == 1
#guard darkBazaarPrivateN4K4Descriptor.constraints.length == 1 + 2 * semanticBodies.length + 12
#guard !(emitVmJson2 darkBazaarPrivateN4K4Descriptor).contains "1430520837"

/- The deployed gate and constraint counts as LITERALS, and the tie from this artifact to the
size-generic cost model in `Market.PackedBookFamily`.  Those three `#guard`s are what make the
model's game-sized numbers a computation over a VALIDATED formula rather than an estimate: change
the layout here and they go red, so the model cannot drift away from the emitted descriptor. -/
#guard semanticBodies.length == 181
#guard darkBazaarPrivateN4K4Descriptor.constraints.length == 375
#guard TRACE_WIDTH == Market.PackedBookFamily.traceWidthOf 4 4 8 4 6 1
#guard semanticBodies.length == Market.PackedBookFamily.semanticBodyCount 4 4 8 4 6 1
#guard darkBazaarPrivateN4K4Descriptor.constraints.length ==
  Market.PackedBookFamily.constraintCount 4 4 8 4 6 1 1

/-! ## 3. Honest emitted-AIR extraction boundary.

This section begins the `Satisfied2` bridge: every semantic gate vanishes modulo
BabyBear, every public pin is enforced, and the wide lookup binds all eight root
columns to the genuine full-arity permutation output under `ChipTableSoundN`.
Sections 4–6 perform the bounded integer decode and close the final
`darkBazaarPrivateN4K4_descriptor_to_accepts` theorem. -/

def dbM0 : Int → Int := fun _ => 0
def dbF0 : Int → Int × Nat := fun _ => (0, 0)

def publicCols : List Nat :=
  [SESSION, RULE] ++ rootDigestCols ++ [PSTAR, VSTAR]

def constTrace (a pis : Assignment) (tf : TraceFamily) : VmTrace where
  rows := List.replicate 4 a
  pub := pis
  tf := tf

@[simp] theorem constTrace_rows_length (a pis : Assignment) (tf : TraceFamily) :
    (constTrace a pis tf).rows.length = 4 := by
  simp [constTrace]

@[simp] theorem constTrace_loc0 (a pis : Assignment) (tf : TraceFamily) :
    (envAt (constTrace a pis tf) 0).loc = a := by
  funext col
  simp [envAt, constTrace]

@[simp] theorem constTrace_pub0 (a pis : Assignment) (tf : TraceFamily) :
    (envAt (constTrace a pis tf) 0).pub = pis := rfl

@[simp] theorem constTrace_tf (a pis : Assignment) (tf : TraceFamily) :
    (constTrace a pis tf).tf = tf := rfl

def CanonicalAssignment (a : Assignment) : Prop :=
  ∀ col, 0 ≤ a col ∧ a col < BABYBEAR_MODULUS

theorem semantic_gate_mem {body : EmittedExpr} (hbody : body ∈ semanticBodies) :
    VmConstraint2.base (.gate body) ∈ darkBazaarPrivateN4K4Descriptor.constraints := by
  simp [darkBazaarPrivateN4K4Descriptor, hbody]

theorem public_pin_mem {pin : VmConstraint2} (hpin : pin ∈ publicPins) :
    pin ∈ darkBazaarPrivateN4K4Descriptor.constraints := by
  simp [darkBazaarPrivateN4K4Descriptor, hpin]

theorem root_lookup_mem :
    rootLookup ∈ darkBazaarPrivateN4K4Descriptor.constraints := by
  simp [darkBazaarPrivateN4K4Descriptor, hashLookups]

/-- A satisfying constant trace forces every Lean-authored semantic gate modulo
the deployed BabyBear modulus. -/
theorem semantic_gate_vanishes {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf))
    {body : EmittedExpr} (hbody : body ∈ semanticBodies) :
    body.eval a ≡ 0 [ZMOD BABYBEAR_MODULUS] := by
  have h := hsat.rowConstraints 0 (by simp) _ (semantic_gate_mem hbody)
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, BABYBEAR_MODULUS] using h

/-- Every declared PI binding is real at row zero. -/
theorem public_pin_sound {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf))
    {col pi : Nat}
    (hpin : VmConstraint2.base (.piBinding .first col pi) ∈ publicPins) :
    a col ≡ pis pi [ZMOD BABYBEAR_MODULUS] := by
  have h := hsat.rowConstraints 0 (by simp) _ (public_pin_mem hpin)
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, BABYBEAR_MODULUS] using h

/-- Under the genuine wide Poseidon chip-table hypothesis, the descriptor binds
ALL eight public root lanes to the one-permutation output over the exact
domain-separated 12-felt source plus four zero framing lanes. -/
theorem wide_root_lookup_sound {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (permOut : List Int → List Int)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) :
    rootDigestCols.map a = permOut (rootInputExprs.map (·.eval a)) := by
  have hrow := hsat.rowConstraints 0 (by simp) rootLookup root_lookup_mem
  have hlookup :
      (chipLookupTupleN rootInputExprs rootDigestCols).map (·.eval a) ∈ tf TableId.poseidon2 := by
    simpa [rootLookup, VmConstraint2.holdsAt,
      Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt] using hrow
  exact chip_lookup_sound_N permOut (tf TableId.poseidon2) hChip a
    rootInputExprs rootDigestCols (by decide) hlookup

structure EmittedAirFacts (permOut : List Int → List Int)
    (a pis : Assignment) (tf : TraceFamily) : Prop where
  canonicalCells : CanonicalAssignment a
  semanticGates : ∀ body ∈ semanticBodies, body.eval a ≡ 0 [ZMOD BABYBEAR_MODULUS]
  wideRoot : rootDigestCols.map a = permOut (rootInputExprs.map (·.eval a))
  publicPins : ∀ col pi,
    VmConstraint2.base (.piBinding .first col pi) ∈ publicPins →
    a col ≡ pis pi [ZMOD BABYBEAR_MODULUS]

/-- Load-bearing first rung of the emitted-AIR bridge: it starts from the actual
`Satisfied2` denotation and extracts every gate, every PI, and the full wide
commitment lookup.  The closing theorem below consumes these facts through the
complete integer decode and market identification. -/
theorem darkBazaarPrivateN4K4_emitted_air_sound
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (permOut : List Int → List Int)
    (hcanon : CanonicalAssignment a)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) :
    EmittedAirFacts permOut a pis tf :=
  ⟨hcanon,
   fun _ hbody => semantic_gate_vanishes hsat hbody,
   wide_root_lookup_sound permOut hChip hsat,
   fun _ _ hpin => public_pin_sound hsat hpin⟩

/-- Binary gates really pin a bit; the range decompositions rely on this tooth. -/
theorem binaryBody_zero_iff (a : Assignment) (col : Nat) :
    (binaryBody col).eval a = 0 ↔ a col = 0 ∨ a col = 1 := by
  simp [binaryBody, sub, neg, mul, add, v, c, EmittedExpr.eval]
  omega

/-! ## 4. Exact integer decoding of the emitted private witness. -/

open Dregg2.Circuit.Emit.EffectVmEmitTransfer (pPrimeInt)

/-- BabyBear primality and canonical representatives turn a modular boolean
gate into honest integer bithood. -/
theorem binary_of_modular_gate {a : Assignment} {col : Nat}
    (hcanon : CanonicalAssignment a)
    (hmod : (binaryBody col).eval a ≡ 0 [ZMOD BABYBEAR_MODULUS]) :
    a col = 0 ∨ a col = 1 := by
  have hev : (binaryBody col).eval a = a col * (a col - 1) := by
    simp only [binaryBody, sub, neg, mul, add, v, c, EmittedExpr.eval]
    ring
  rw [hev] at hmod
  have hd : (2013265921 : Int) ∣ a col * (a col - 1) := by
    simpa [BABYBEAR_MODULUS] using Int.modEq_zero_iff_dvd.mp hmod
  rcases pPrimeInt.dvd_mul.mp hd with hx | hx
  · obtain ⟨k, hk⟩ := hx
    have hc := hcanon col
    simp only [BABYBEAR_MODULUS] at hc
    left
    omega
  · obtain ⟨k, hk⟩ := hx
    have hc := hcanon col
    simp only [BABYBEAR_MODULUS] at hc
    right
    omega

/-- Two canonical representatives of one BabyBear residue are the same integer. -/
theorem eq_of_modEq_of_canonical {x y : Int}
    (hmod : x ≡ y [ZMOD BABYBEAR_MODULUS])
    (hx : 0 ≤ x ∧ x < BABYBEAR_MODULUS)
    (hy : 0 ≤ y ∧ y < BABYBEAR_MODULUS) : x = y := by
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hmod
  simp only [BABYBEAR_MODULUS] at hk hx hy
  omega

theorem kind_bit_body_mem (order : Fin 4) (kind : Fin 8) :
    binaryBody (KIND order.val kind.val) ∈ semanticBodies := by
  fin_cases order <;> fin_cases kind <;> decide

theorem qty_bit_body_mem (order : Fin 4) (bit : Fin 4) :
    binaryBody (QTY_BIT order.val bit.val) ∈ semanticBodies := by
  fin_cases order <;> fin_cases bit <;> decide

theorem min_choose_body_mem (price : Fin 4) :
    binaryBody (MIN_CHOOSE price.val) ∈ semanticBodies := by
  fin_cases price <;> decide

theorem min_diff_bit_body_mem (price : Fin 4) (bit : Fin 6) :
    binaryBody (MIN_DIFF_BIT price.val bit.val) ∈ semanticBodies := by
  fin_cases price <;> fin_cases bit <;> decide

theorem select_body_mem (price : Fin 4) :
    binaryBody (SELECT price.val) ∈ semanticBodies := by
  fin_cases price <;> decide

theorem max_diff_bit_body_mem (price : Fin 4) (bit : Fin 6) :
    binaryBody (MAX_DIFF_BIT price.val bit.val) ∈ semanticBodies := by
  fin_cases price <;> fin_cases bit <;> decide

theorem low_slack_bit_body_mem (price : Fin 4) (bit : Fin 6) :
    binaryBody (LOW_SLACK_BIT price.val bit.val) ∈ semanticBodies := by
  fin_cases price <;> fin_cases bit <;> decide

structure DecodedPrivateBits (a : Assignment) : Prop where
  kind : ∀ order : Fin 4, ∀ kind : Fin 8,
    a (KIND order.val kind.val) = 0 ∨ a (KIND order.val kind.val) = 1
  qty : ∀ order bit : Fin 4,
    a (QTY_BIT order.val bit.val) = 0 ∨ a (QTY_BIT order.val bit.val) = 1
  minChoose : ∀ price : Fin 4,
    a (MIN_CHOOSE price.val) = 0 ∨ a (MIN_CHOOSE price.val) = 1
  minDiff : ∀ price : Fin 4, ∀ bit : Fin 6,
    a (MIN_DIFF_BIT price.val bit.val) = 0 ∨ a (MIN_DIFF_BIT price.val bit.val) = 1
  select : ∀ price : Fin 4,
    a (SELECT price.val) = 0 ∨ a (SELECT price.val) = 1
  maxDiff : ∀ price : Fin 4, ∀ bit : Fin 6,
    a (MAX_DIFF_BIT price.val bit.val) = 0 ∨ a (MAX_DIFF_BIT price.val bit.val) = 1
  lowSlack : ∀ price : Fin 4, ∀ bit : Fin 6,
    a (LOW_SLACK_BIT price.val bit.val) = 0 ∨ a (LOW_SLACK_BIT price.val bit.val) = 1

/-- Every private selector and range-decomposition limb is an actual bit in any
canonical satisfying trace. -/
theorem darkBazaarPrivateN4K4_private_bits_decoded
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) :
    DecodedPrivateBits a := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro order kind
    exact binary_of_modular_gate hcanon
      (semantic_gate_vanishes hsat (kind_bit_body_mem order kind))
  · intro order bit
    exact binary_of_modular_gate hcanon
      (semantic_gate_vanishes hsat (qty_bit_body_mem order bit))
  · intro price
    exact binary_of_modular_gate hcanon
      (semantic_gate_vanishes hsat (min_choose_body_mem price))
  · intro price bit
    exact binary_of_modular_gate hcanon
      (semantic_gate_vanishes hsat (min_diff_bit_body_mem price bit))
  · intro price
    exact binary_of_modular_gate hcanon
      (semantic_gate_vanishes hsat (select_body_mem price))
  · intro price bit
    exact binary_of_modular_gate hcanon
      (semantic_gate_vanishes hsat (max_diff_bit_body_mem price bit))
  · intro price bit
    exact binary_of_modular_gate hcanon
      (semantic_gate_vanishes hsat (low_slack_bit_body_mem price bit))

theorem qty_recompose_body_mem (order : Fin 4) :
    recompose (QTY order.val) (QTY_BIT order.val) QTY_BITS ∈ semanticBodies := by
  fin_cases order <;> decide

theorem min_diff_recompose_body_mem (price : Fin 4) :
    recompose (MIN_DIFF price.val) (MIN_DIFF_BIT price.val) DIFF_BITS ∈ semanticBodies := by
  fin_cases price <;> decide

theorem max_diff_recompose_body_mem (price : Fin 4) :
    recompose (MAX_DIFF price.val) (MAX_DIFF_BIT price.val) DIFF_BITS ∈ semanticBodies := by
  fin_cases price <;> decide

theorem low_slack_recompose_body_mem (price : Fin 4) :
    recompose (LOW_SLACK price.val) (LOW_SLACK_BIT price.val) DIFF_BITS ∈ semanticBodies := by
  fin_cases price <;> decide

/-- Exact four-bit recomposition for private quantities. -/
theorem qty_recompose_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf))
    (order : Fin 4) :
    a (QTY order.val) =
      a (QTY_BIT order.val 0) + 2 * a (QTY_BIT order.val 1) +
      4 * a (QTY_BIT order.val 2) + 8 * a (QTY_BIT order.val 3) := by
  have hbits := darkBazaarPrivateN4K4_private_bits_decoded hcanon hsat
  have hb0 := hbits.qty order 0; have hb1 := hbits.qty order 1
  have hb2 := hbits.qty order 2; have hb3 := hbits.qty order 3
  have hgate := semantic_gate_vanishes hsat (qty_recompose_body_mem order)
  have hres :
      (a (QTY_BIT order.val 0) + 2 * a (QTY_BIT order.val 1) +
        4 * a (QTY_BIT order.val 2) + 8 * a (QTY_BIT order.val 3)) -
        a (QTY order.val) ≡ 0 [ZMOD BABYBEAR_MODULUS] := by
    norm_num [recompose, sumE, weighted, sub, neg, mul, add, v, c, QTY_BITS,
      EmittedExpr.eval, List.range_succ, Function.comp_apply] at hgate
    simpa [sub_eq_add_neg, add_assoc] using hgate
  have hcong :
      a (QTY_BIT order.val 0) + 2 * a (QTY_BIT order.val 1) +
        4 * a (QTY_BIT order.val 2) + 8 * a (QTY_BIT order.val 3) ≡
      a (QTY order.val) [ZMOD BABYBEAR_MODULUS] := by
    simpa using hres.add_right (a (QTY order.val))
  have hsmall :
      0 ≤ a (QTY_BIT order.val 0) + 2 * a (QTY_BIT order.val 1) +
        4 * a (QTY_BIT order.val 2) + 8 * a (QTY_BIT order.val 3) ∧
      a (QTY_BIT order.val 0) + 2 * a (QTY_BIT order.val 1) +
        4 * a (QTY_BIT order.val 2) + 8 * a (QTY_BIT order.val 3) < BABYBEAR_MODULUS := by
    rcases hb0 with hb0 | hb0 <;> rcases hb1 with hb1 | hb1 <;>
      rcases hb2 with hb2 | hb2 <;> rcases hb3 with hb3 | hb3 <;>
      simp_all [BABYBEAR_MODULUS]
  exact (eq_of_modEq_of_canonical hcong hsmall (hcanon (QTY order.val))).symm

theorem qty_column_bounds
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf))
    (order : Fin 4) :
    0 ≤ a (QTY order.val) ∧ a (QTY order.val) < 16 := by
  rw [qty_recompose_exact hcanon hsat order]
  have hbits := darkBazaarPrivateN4K4_private_bits_decoded hcanon hsat
  have hb0 := hbits.qty order 0; have hb1 := hbits.qty order 1
  have hb2 := hbits.qty order 2; have hb3 := hbits.qty order 3
  rcases hb0 with hb0 | hb0 <;> rcases hb1 with hb1 | hb1 <;>
    rcases hb2 with hb2 | hb2 <;> rcases hb3 with hb3 | hb3 <;> simp_all

theorem bit_bounds {x : Int} (h : x = 0 ∨ x = 1) : 0 ≤ x ∧ x ≤ 1 := by
  rcases h with rfl | rfl <;> omega

/-- Generic exact six-bit decomposition for market difference and tie-slack columns. -/
theorem six_bit_recompose_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf))
    (col : Nat) (bit : Nat → Nat)
    (hbody : recompose col bit DIFF_BITS ∈ semanticBodies)
    (hbits : ∀ b : Fin 6, a (bit b.val) = 0 ∨ a (bit b.val) = 1) :
    a col = a (bit 0) + 2 * a (bit 1) + 4 * a (bit 2) + 8 * a (bit 3) +
      16 * a (bit 4) + 32 * a (bit 5) := by
  have hb0 : 0 ≤ a (bit 0) ∧ a (bit 0) ≤ 1 := by simpa using bit_bounds (hbits 0)
  have hb1 : 0 ≤ a (bit 1) ∧ a (bit 1) ≤ 1 := by simpa using bit_bounds (hbits 1)
  have hb2 : 0 ≤ a (bit 2) ∧ a (bit 2) ≤ 1 := by simpa using bit_bounds (hbits 2)
  have hb3 : 0 ≤ a (bit 3) ∧ a (bit 3) ≤ 1 := by simpa using bit_bounds (hbits 3)
  have hb4 : 0 ≤ a (bit 4) ∧ a (bit 4) ≤ 1 := by simpa using bit_bounds (hbits 4)
  have hb5 : 0 ≤ a (bit 5) ∧ a (bit 5) ≤ 1 := by simpa using bit_bounds (hbits 5)
  have hgate := semantic_gate_vanishes hsat hbody
  have hres :
      (a (bit 0) + 2 * a (bit 1) + 4 * a (bit 2) + 8 * a (bit 3) +
        16 * a (bit 4) + 32 * a (bit 5)) - a col ≡
        0 [ZMOD BABYBEAR_MODULUS] := by
    norm_num [recompose, sumE, weighted, sub, neg, mul, add, v, c, DIFF_BITS,
      EmittedExpr.eval, List.range_succ, Function.comp_apply] at hgate
    simpa [sub_eq_add_neg, add_assoc] using hgate
  have hcong :
      a (bit 0) + 2 * a (bit 1) + 4 * a (bit 2) + 8 * a (bit 3) +
        16 * a (bit 4) + 32 * a (bit 5) ≡ a col [ZMOD BABYBEAR_MODULUS] := by
    simpa using hres.add_right (a col)
  have hsmall :
      0 ≤ a (bit 0) + 2 * a (bit 1) + 4 * a (bit 2) + 8 * a (bit 3) +
        16 * a (bit 4) + 32 * a (bit 5) ∧
      a (bit 0) + 2 * a (bit 1) + 4 * a (bit 2) + 8 * a (bit 3) +
        16 * a (bit 4) + 32 * a (bit 5) < BABYBEAR_MODULUS := by
    simp only [BABYBEAR_MODULUS]
    omega
  exact (eq_of_modEq_of_canonical hcong hsmall (hcanon col)).symm

theorem min_diff_recompose_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) (price : Fin 4) :
    a (MIN_DIFF price.val) =
      a (MIN_DIFF_BIT price.val 0) + 2 * a (MIN_DIFF_BIT price.val 1) +
      4 * a (MIN_DIFF_BIT price.val 2) + 8 * a (MIN_DIFF_BIT price.val 3) +
      16 * a (MIN_DIFF_BIT price.val 4) + 32 * a (MIN_DIFF_BIT price.val 5) := by
  apply six_bit_recompose_exact hcanon hsat _ _ (min_diff_recompose_body_mem price)
  exact (darkBazaarPrivateN4K4_private_bits_decoded hcanon hsat).minDiff price

theorem max_diff_recompose_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) (price : Fin 4) :
    a (MAX_DIFF price.val) =
      a (MAX_DIFF_BIT price.val 0) + 2 * a (MAX_DIFF_BIT price.val 1) +
      4 * a (MAX_DIFF_BIT price.val 2) + 8 * a (MAX_DIFF_BIT price.val 3) +
      16 * a (MAX_DIFF_BIT price.val 4) + 32 * a (MAX_DIFF_BIT price.val 5) := by
  apply six_bit_recompose_exact hcanon hsat _ _ (max_diff_recompose_body_mem price)
  exact (darkBazaarPrivateN4K4_private_bits_decoded hcanon hsat).maxDiff price

theorem low_slack_recompose_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) (price : Fin 4) :
    a (LOW_SLACK price.val) =
      a (LOW_SLACK_BIT price.val 0) + 2 * a (LOW_SLACK_BIT price.val 1) +
      4 * a (LOW_SLACK_BIT price.val 2) + 8 * a (LOW_SLACK_BIT price.val 3) +
      16 * a (LOW_SLACK_BIT price.val 4) + 32 * a (LOW_SLACK_BIT price.val 5) := by
  apply six_bit_recompose_exact hcanon hsat _ _ (low_slack_recompose_body_mem price)
  exact (darkBazaarPrivateN4K4_private_bits_decoded hcanon hsat).lowSlack price

theorem six_bit_column_bounds
    {a : Assignment} {col : Nat} {bit : Nat → Nat}
    (hrec : a col = a (bit 0) + 2 * a (bit 1) + 4 * a (bit 2) + 8 * a (bit 3) +
      16 * a (bit 4) + 32 * a (bit 5))
    (hbits : ∀ b : Fin 6, a (bit b.val) = 0 ∨ a (bit b.val) = 1) :
    0 ≤ a col ∧ a col ≤ 63 := by
  rw [hrec]
  have hb0 : 0 ≤ a (bit 0) ∧ a (bit 0) ≤ 1 := by simpa using bit_bounds (hbits 0)
  have hb1 : 0 ≤ a (bit 1) ∧ a (bit 1) ≤ 1 := by simpa using bit_bounds (hbits 1)
  have hb2 : 0 ≤ a (bit 2) ∧ a (bit 2) ≤ 1 := by simpa using bit_bounds (hbits 2)
  have hb3 : 0 ≤ a (bit 3) ∧ a (bit 3) ≤ 1 := by simpa using bit_bounds (hbits 3)
  have hb4 : 0 ≤ a (bit 4) ∧ a (bit 4) ≤ 1 := by simpa using bit_bounds (hbits 4)
  have hb5 : 0 ≤ a (bit 5) ∧ a (bit 5) ≤ 1 := by simpa using bit_bounds (hbits 5)
  omega

theorem min_diff_column_bounds
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) (price : Fin 4) :
    0 ≤ a (MIN_DIFF price.val) ∧ a (MIN_DIFF price.val) ≤ 63 :=
  six_bit_column_bounds (min_diff_recompose_exact hcanon hsat price)
    ((darkBazaarPrivateN4K4_private_bits_decoded hcanon hsat).minDiff price)

theorem max_diff_column_bounds
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) (price : Fin 4) :
    0 ≤ a (MAX_DIFF price.val) ∧ a (MAX_DIFF price.val) ≤ 63 :=
  six_bit_column_bounds (max_diff_recompose_exact hcanon hsat price)
    ((darkBazaarPrivateN4K4_private_bits_decoded hcanon hsat).maxDiff price)

theorem low_slack_column_bounds
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) (price : Fin 4) :
    0 ≤ a (LOW_SLACK price.val) ∧ a (LOW_SLACK price.val) ≤ 63 :=
  six_bit_column_bounds (low_slack_recompose_exact hcanon hsat price)
    ((darkBazaarPrivateN4K4_private_bits_decoded hcanon hsat).lowSlack price)

theorem kind_sum_body_mem (order : Fin 4) :
    sub (sumE ((List.range 8).map (fun t => v (KIND order.val t)))) (c 1) ∈
      semanticBodies := by
  fin_cases order <;> decide

theorem kind_sum_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) (order : Fin 4) :
    a (KIND order.val 0) + a (KIND order.val 1) + a (KIND order.val 2) +
      a (KIND order.val 3) + a (KIND order.val 4) + a (KIND order.val 5) +
      a (KIND order.val 6) + a (KIND order.val 7) = 1 := by
  have hbits := darkBazaarPrivateN4K4_private_bits_decoded hcanon hsat
  have hb0 : 0 ≤ a (KIND order.val 0) ∧ a (KIND order.val 0) ≤ 1 := by
    simpa using bit_bounds (hbits.kind order 0)
  have hb1 : 0 ≤ a (KIND order.val 1) ∧ a (KIND order.val 1) ≤ 1 := by
    simpa using bit_bounds (hbits.kind order 1)
  have hb2 : 0 ≤ a (KIND order.val 2) ∧ a (KIND order.val 2) ≤ 1 := by
    simpa using bit_bounds (hbits.kind order 2)
  have hb3 : 0 ≤ a (KIND order.val 3) ∧ a (KIND order.val 3) ≤ 1 := by
    simpa using bit_bounds (hbits.kind order 3)
  have hb4 : 0 ≤ a (KIND order.val 4) ∧ a (KIND order.val 4) ≤ 1 := by
    simpa using bit_bounds (hbits.kind order 4)
  have hb5 : 0 ≤ a (KIND order.val 5) ∧ a (KIND order.val 5) ≤ 1 := by
    simpa using bit_bounds (hbits.kind order 5)
  have hb6 : 0 ≤ a (KIND order.val 6) ∧ a (KIND order.val 6) ≤ 1 := by
    simpa using bit_bounds (hbits.kind order 6)
  have hb7 : 0 ≤ a (KIND order.val 7) ∧ a (KIND order.val 7) ≤ 1 := by
    simpa using bit_bounds (hbits.kind order 7)
  have hgate := semantic_gate_vanishes hsat (kind_sum_body_mem order)
  have hres :
      (a (KIND order.val 0) + a (KIND order.val 1) + a (KIND order.val 2) +
        a (KIND order.val 3) + a (KIND order.val 4) + a (KIND order.val 5) +
        a (KIND order.val 6) + a (KIND order.val 7)) - 1 ≡
        0 [ZMOD BABYBEAR_MODULUS] := by
    norm_num [sumE, sub, neg, mul, add, v, c, EmittedExpr.eval,
      List.range_succ, Function.comp_apply] at hgate
    simpa [sub_eq_add_neg, add_assoc] using hgate
  have hcong :
      a (KIND order.val 0) + a (KIND order.val 1) + a (KIND order.val 2) +
        a (KIND order.val 3) + a (KIND order.val 4) + a (KIND order.val 5) +
        a (KIND order.val 6) + a (KIND order.val 7) ≡ 1 [ZMOD BABYBEAR_MODULUS] := by
    simpa using hres.add_right 1
  apply eq_of_modEq_of_canonical hcong
  · simp only [BABYBEAR_MODULUS]
    omega
  · norm_num [BABYBEAR_MODULUS]

def kindColumnValue (a : Assignment) (order : Fin 4) : Int :=
  a (KIND order.val 1) + 2 * a (KIND order.val 2) + 3 * a (KIND order.val 3) +
    4 * a (KIND order.val 4) + 5 * a (KIND order.val 5) +
    6 * a (KIND order.val 6) + 7 * a (KIND order.val 7)

theorem kindColumnValue_bounds
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) (order : Fin 4) :
    0 ≤ kindColumnValue a order ∧ kindColumnValue a order < 8 := by
  have hbits := darkBazaarPrivateN4K4_private_bits_decoded hcanon hsat
  have hb0 : 0 ≤ a (KIND order.val 0) ∧ a (KIND order.val 0) ≤ 1 := by
    simpa using bit_bounds (hbits.kind order 0)
  have hb1 : 0 ≤ a (KIND order.val 1) ∧ a (KIND order.val 1) ≤ 1 := by
    simpa using bit_bounds (hbits.kind order 1)
  have hb2 : 0 ≤ a (KIND order.val 2) ∧ a (KIND order.val 2) ≤ 1 := by
    simpa using bit_bounds (hbits.kind order 2)
  have hb3 : 0 ≤ a (KIND order.val 3) ∧ a (KIND order.val 3) ≤ 1 := by
    simpa using bit_bounds (hbits.kind order 3)
  have hb4 : 0 ≤ a (KIND order.val 4) ∧ a (KIND order.val 4) ≤ 1 := by
    simpa using bit_bounds (hbits.kind order 4)
  have hb5 : 0 ≤ a (KIND order.val 5) ∧ a (KIND order.val 5) ≤ 1 := by
    simpa using bit_bounds (hbits.kind order 5)
  have hb6 : 0 ≤ a (KIND order.val 6) ∧ a (KIND order.val 6) ≤ 1 := by
    simpa using bit_bounds (hbits.kind order 6)
  have hb7 : 0 ≤ a (KIND order.val 7) ∧ a (KIND order.val 7) ≤ 1 := by
    simpa using bit_bounds (hbits.kind order 7)
  have hsum := kind_sum_exact hcanon hsat order
  simp only [kindColumnValue]
  omega

def decodedKind (a : Assignment) (order : Fin 4) : Fin 8 :=
  ⟨(kindColumnValue a order).toNat % 8, Nat.mod_lt _ (by decide)⟩

def decodedQty (a : Assignment) (order : Fin 4) : Fin 16 :=
  ⟨(a (QTY order.val)).toNat % 16, Nat.mod_lt _ (by decide)⟩

def decodedWitness (a : Assignment) : PrivateWitness where
  orders := fun order => ⟨decodedKind a order, decodedQty a order⟩
  blinding := fun lane => a (BLINDING lane.val)

def columnPublic (a : Assignment) : PublicStatement where
  session := a SESSION
  rule := a RULE
  orderRoot := fun lane => a (ROOT lane.val)
  pStar := (a PSTAR).toNat
  vStar := a VSTAR

def piPublic (pis : Assignment) : PublicStatement where
  session := pis 0
  rule := pis 1
  orderRoot := fun lane => pis (2 + lane.val)
  pStar := (pis 10).toNat
  vStar := pis 11

def permHash8 (permOut : List Int → List Int) (xs : List Int) (lane : Fin 8) : Int :=
  (permOut xs).getD lane.val 0

theorem decoded_kind_value
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) (order : Fin 4) :
    ((decodedWitness a).orders order).kind.val = (kindColumnValue a order).toNat := by
  simp only [decodedWitness, decodedKind]
  exact Nat.mod_eq_of_lt ((Int.toNat_lt (kindColumnValue_bounds hcanon hsat order).1).2
    (kindColumnValue_bounds hcanon hsat order).2)

theorem decoded_kind_coe
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) (order : Fin 4) :
    (((decodedWitness a).orders order).kind.val : Int) = kindColumnValue a order := by
  rw [decoded_kind_value hcanon hsat]
  exact Int.toNat_of_nonneg (kindColumnValue_bounds hcanon hsat order).1

theorem decoded_qty_value
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) (order : Fin 4) :
    ((decodedWitness a).orders order).qty.val = (a (QTY order.val)).toNat := by
  simp only [decodedWitness, decodedQty]
  exact Nat.mod_eq_of_lt ((Int.toNat_lt (qty_column_bounds hcanon hsat order).1).2
    (qty_column_bounds hcanon hsat order).2)

theorem decoded_qty_coe
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) (order : Fin 4) :
    (((decodedWitness a).orders order).qty.val : Int) = a (QTY order.val) := by
  rw [decoded_qty_value hcanon hsat]
  exact Int.toNat_of_nonneg (qty_column_bounds hcanon hsat order).1

theorem decoded_blinding_canonical (a : Assignment) (hcanon : CanonicalAssignment a) :
    CanonicalBlinding (decodedWitness a) := by
  intro lane
  simpa [decodedWitness, BLINDING, BABYBEAR_MODULUS] using hcanon (BLINDING lane.val)

theorem kindValue_eval (a : Assignment) (order : Nat) :
    (kindValue order).eval a =
      a (KIND order 1) + 2 * a (KIND order 2) + 3 * a (KIND order 3) +
      4 * a (KIND order 4) + 5 * a (KIND order 5) +
      6 * a (KIND order 6) + 7 * a (KIND order 7) := by
  norm_num [kindValue, sumE, weighted, add, mul, v, c, EmittedExpr.eval,
    List.range_succ, Function.comp_apply, add_assoc]

theorem rule_body_mem : sub (v RULE) (c RULE_ID) ∈ semanticBodies := by decide

theorem rule_column_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) :
    a RULE = RULE_ID := by
  have hgate := semantic_gate_vanishes hsat rule_body_mem
  have hres : a RULE - RULE_ID ≡ 0 [ZMOD BABYBEAR_MODULUS] := by
    simpa [sub, neg, mul, add, v, c, EmittedExpr.eval, ← sub_eq_add_neg] using hgate
  have hcong : a RULE ≡ RULE_ID [ZMOD BABYBEAR_MODULUS] := by
    simpa using hres.add_right RULE_ID
  exact eq_of_modEq_of_canonical hcong (hcanon RULE) (by
    norm_num [RULE_ID, BABYBEAR_MODULUS])

theorem order_pack_body_mem (order : Fin 4) :
    sub (v (ORDER_PACK order.val))
      (add (kindValue order.val) (weighted 8 (v (QTY order.val)))) ∈ semanticBodies := by
  fin_cases order <;> decide

theorem order_pack_column_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) (order : Fin 4) :
    a (ORDER_PACK order.val) = kindColumnValue a order + 8 * a (QTY order.val) := by
  have hk := kindColumnValue_bounds hcanon hsat order
  have hq := qty_column_bounds hcanon hsat order
  have hgate := semantic_gate_vanishes hsat (order_pack_body_mem order)
  have hkv := kindValue_eval a order.val
  have hres :
      a (ORDER_PACK order.val) - (kindColumnValue a order + 8 * a (QTY order.val)) ≡
        0 [ZMOD BABYBEAR_MODULUS] := by
    simp only [sub, neg, weighted, mul, add, v, c, EmittedExpr.eval] at hgate
    rw [hkv] at hgate
    simpa [kindColumnValue,
      sub_eq_add_neg, add_assoc] using hgate
  have hcong : a (ORDER_PACK order.val) ≡
      kindColumnValue a order + 8 * a (QTY order.val) [ZMOD BABYBEAR_MODULUS] := by
    simpa using hres.add_right (kindColumnValue a order + 8 * a (QTY order.val))
  apply eq_of_modEq_of_canonical hcong (hcanon (ORDER_PACK order.val))
  simp only [BABYBEAR_MODULUS]
  omega

theorem order_pack_column_bounds
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) (order : Fin 4) :
    0 ≤ a (ORDER_PACK order.val) ∧ a (ORDER_PACK order.val) < 128 := by
  rw [order_pack_column_exact hcanon hsat order]
  have hk := kindColumnValue_bounds hcanon hsat order
  have hq := qty_column_bounds hcanon hsat order
  omega

theorem order_pack_decoded
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) (order : Fin 4) :
    a (ORDER_PACK order.val) = orderCode ((decodedWitness a).orders order) := by
  rw [order_pack_column_exact hcanon hsat order]
  simp only [orderCode]
  rw [decoded_kind_coe hcanon hsat order, decoded_qty_coe hcanon hsat order]

theorem packed_book_body_mem :
    sub (v PACKED_BOOK)
      (sumE ((List.range 4).map
        (fun i => weighted ((128 : Int) ^ i) (v (ORDER_PACK i))))) ∈ semanticBodies := by
  decide

theorem packed_book_column_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) :
    a PACKED_BOOK = a (ORDER_PACK 0) + 128 * a (ORDER_PACK 1) +
      16384 * a (ORDER_PACK 2) + 2097152 * a (ORDER_PACK 3) := by
  have h0 : 0 ≤ a (ORDER_PACK 0) ∧ a (ORDER_PACK 0) < 128 := by
    simpa using order_pack_column_bounds hcanon hsat (0 : Fin 4)
  have h1 : 0 ≤ a (ORDER_PACK 1) ∧ a (ORDER_PACK 1) < 128 := by
    simpa using order_pack_column_bounds hcanon hsat (1 : Fin 4)
  have h2 : 0 ≤ a (ORDER_PACK 2) ∧ a (ORDER_PACK 2) < 128 := by
    simpa using order_pack_column_bounds hcanon hsat (2 : Fin 4)
  have h3 : 0 ≤ a (ORDER_PACK 3) ∧ a (ORDER_PACK 3) < 128 := by
    simpa using order_pack_column_bounds hcanon hsat (3 : Fin 4)
  have hgate := semantic_gate_vanishes hsat packed_book_body_mem
  have hres :
      a PACKED_BOOK - (a (ORDER_PACK 0) + 128 * a (ORDER_PACK 1) +
        16384 * a (ORDER_PACK 2) + 2097152 * a (ORDER_PACK 3)) ≡
        0 [ZMOD BABYBEAR_MODULUS] := by
    norm_num [sumE, weighted, sub, neg, mul, add, v, c, EmittedExpr.eval,
      List.range_succ, Function.comp_apply, add_assoc] at hgate
    simpa [sub_eq_add_neg, add_assoc] using hgate
  have hcong : a PACKED_BOOK ≡
      a (ORDER_PACK 0) + 128 * a (ORDER_PACK 1) +
        16384 * a (ORDER_PACK 2) + 2097152 * a (ORDER_PACK 3)
      [ZMOD BABYBEAR_MODULUS] := by
    simpa using hres.add_right
      (a (ORDER_PACK 0) + 128 * a (ORDER_PACK 1) +
        16384 * a (ORDER_PACK 2) + 2097152 * a (ORDER_PACK 3))
  apply eq_of_modEq_of_canonical hcong (hcanon PACKED_BOOK)
  simp only [BABYBEAR_MODULUS]
  omega

theorem packed_book_decoded
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) :
    a PACKED_BOOK = packedBook (decodedWitness a) := by
  rw [packed_book_column_exact hcanon hsat]
  have h0 := order_pack_decoded hcanon hsat (0 : Fin 4)
  have h1 := order_pack_decoded hcanon hsat (1 : Fin 4)
  have h2 := order_pack_decoded hcanon hsat (2 : Fin 4)
  have h3 := order_pack_decoded hcanon hsat (3 : Fin 4)
  have h0' : a (ORDER_PACK 0) = orderCode ((decodedWitness a).orders 0) := by simpa using h0
  have h1' : a (ORDER_PACK 1) = orderCode ((decodedWitness a).orders 1) := by simpa using h1
  have h2' : a (ORDER_PACK 2) = orderCode ((decodedWitness a).orders 2) := by simpa using h2
  have h3' : a (ORDER_PACK 3) = orderCode ((decodedWitness a).orders 3) := by simpa using h3
  rw [h0', h1', h2', h3']
  simp [packedBook, List.ofFn_succ, add_assoc]

/-! ## 5. Commitment and public-input identification. -/

theorem root_input_decoded
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) :
    rootInputExprs.map (·.eval a) =
      rootPreimage (columnPublic a).session (decodedWitness a) := by
  have hp := packed_book_decoded hcanon hsat
  have hr := rule_column_exact hcanon hsat
  simp only [rootInputExprs, rootPreimage, columnPublic, decodedWitness, BLINDING,
    ROOT_DOMAIN_TAG, List.ofFn_succ, v, c, DIGEST_WIDTH, BLINDING_BASE]
  norm_num [List.range_succ, Function.comp_apply, EmittedExpr.eval]
  exact ⟨hr, by simpa [decodedWitness, BLINDING, BLINDING_BASE] using hp⟩

theorem column_root_semantic
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (permOut : List Int → List Int)
    (hcanon : CanonicalAssignment a)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) :
    (columnPublic a).orderRoot =
      orderRoot (permHash8 permOut) (columnPublic a).session (decodedWitness a) := by
  have hwide := wide_root_lookup_sound permOut hChip hsat
  rw [root_input_decoded hcanon hsat] at hwide
  funext lane
  have h := congrArg (fun xs : List Int => xs.getD lane.val 0) hwide
  fin_cases lane <;>
    simpa [columnPublic, orderRoot, permHash8, rootDigestCols,
      DIGEST_WIDTH, ROOT, List.range_succ] using h

theorem pi_public_eq_column
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hcanonPis : CanonicalAssignment pis)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) :
    piPublic pis = columnPublic a := by
  have hs : pis 0 = a SESSION :=
    (eq_of_modEq_of_canonical (public_pin_sound hsat (by
      simp [publicPins, DIGEST_WIDTH, ROOT, List.range_succ]))
      (hcanon SESSION) (hcanonPis 0)).symm
  have hr : pis 1 = a RULE :=
    (eq_of_modEq_of_canonical (public_pin_sound hsat (by
      simp [publicPins, DIGEST_WIDTH, ROOT, List.range_succ]))
      (hcanon RULE) (hcanonPis 1)).symm
  have hroot : (fun lane : Fin 8 => pis (2 + lane.val)) =
      fun lane => a (ROOT lane.val) := by
    funext lane
    exact (eq_of_modEq_of_canonical (public_pin_sound hsat (by
      fin_cases lane <;> simp [publicPins, DIGEST_WIDTH, ROOT, List.range_succ]))
      (hcanon (ROOT lane.val)) (hcanonPis (2 + lane.val))).symm
  have hp : pis 10 = a PSTAR :=
    (eq_of_modEq_of_canonical (public_pin_sound hsat (by
      simp [publicPins, DIGEST_WIDTH, ROOT, List.range_succ]))
      (hcanon PSTAR) (hcanonPis 10)).symm
  have hv : pis 11 = a VSTAR :=
    (eq_of_modEq_of_canonical (public_pin_sound hsat (by
      simp [publicPins, DIGEST_WIDTH, ROOT, List.range_succ]))
      (hcanon VSTAR) (hcanonPis 11)).symm
  simp only [piPublic, columnPublic]
  rw [hs, hr, hroot, hp, hv]

/-! ## 6. Exact market-column identification. -/

theorem kind_one_selected
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) (order : Fin 4) :
    a (KIND order.val 0) = 1 ∨ a (KIND order.val 1) = 1 ∨
    a (KIND order.val 2) = 1 ∨ a (KIND order.val 3) = 1 ∨
    a (KIND order.val 4) = 1 ∨ a (KIND order.val 5) = 1 ∨
    a (KIND order.val 6) = 1 ∨ a (KIND order.val 7) = 1 := by
  have hbits := darkBazaarPrivateN4K4_private_bits_decoded hcanon hsat
  have hsum := kind_sum_exact hcanon hsat order
  have h0 : a (KIND order.val 0) = 0 ∨ a (KIND order.val 0) = 1 := by
    simpa using hbits.kind order (0 : Fin 8)
  have h1 : a (KIND order.val 1) = 0 ∨ a (KIND order.val 1) = 1 := by
    simpa using hbits.kind order (1 : Fin 8)
  have h2 : a (KIND order.val 2) = 0 ∨ a (KIND order.val 2) = 1 := by
    simpa using hbits.kind order (2 : Fin 8)
  have h3 : a (KIND order.val 3) = 0 ∨ a (KIND order.val 3) = 1 := by
    simpa using hbits.kind order (3 : Fin 8)
  have h4 : a (KIND order.val 4) = 0 ∨ a (KIND order.val 4) = 1 := by
    simpa using hbits.kind order (4 : Fin 8)
  have h5 : a (KIND order.val 5) = 0 ∨ a (KIND order.val 5) = 1 := by
    simpa using hbits.kind order (5 : Fin 8)
  have h6 : a (KIND order.val 6) = 0 ∨ a (KIND order.val 6) = 1 := by
    simpa using hbits.kind order (6 : Fin 8)
  have h7 : a (KIND order.val 7) = 0 ∨ a (KIND order.val 7) = 1 := by
    simpa using hbits.kind order (7 : Fin 8)
  rcases h0 with h0 | h0
  · rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · rcases h3 with h3 | h3
        · rcases h4 with h4 | h4
          · rcases h5 with h5 | h5
            · rcases h6 with h6 | h6
              · rcases h7 with h7 | h7
                · omega
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h7))))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6))))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5)))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4))))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
      · exact Or.inr (Or.inr (Or.inl h2))
    · exact Or.inr (Or.inl h1)
  · exact Or.inl h0

/-- Every kind column is the exact selector for the unique decoded integer kind. -/
theorem kind_selector_decoded
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) (order : Fin 4) (kind : Fin 8) :
    a (KIND order.val kind.val) =
      if kindColumnValue a order = (kind.val : Int) then 1 else 0 := by
  have hsum := kind_sum_exact hcanon hsat order
  have hsel := kind_one_selected hcanon hsat order
  have hbits := darkBazaarPrivateN4K4_private_bits_decoded hcanon hsat
  have hb0 : 0 ≤ a (KIND order.val 0) ∧ a (KIND order.val 0) ≤ 1 := by
    simpa using bit_bounds (hbits.kind order (0 : Fin 8))
  have hb1 : 0 ≤ a (KIND order.val 1) ∧ a (KIND order.val 1) ≤ 1 := by
    simpa using bit_bounds (hbits.kind order (1 : Fin 8))
  have hb2 : 0 ≤ a (KIND order.val 2) ∧ a (KIND order.val 2) ≤ 1 := by
    simpa using bit_bounds (hbits.kind order (2 : Fin 8))
  have hb3 : 0 ≤ a (KIND order.val 3) ∧ a (KIND order.val 3) ≤ 1 := by
    simpa using bit_bounds (hbits.kind order (3 : Fin 8))
  have hb4 : 0 ≤ a (KIND order.val 4) ∧ a (KIND order.val 4) ≤ 1 := by
    simpa using bit_bounds (hbits.kind order (4 : Fin 8))
  have hb5 : 0 ≤ a (KIND order.val 5) ∧ a (KIND order.val 5) ≤ 1 := by
    simpa using bit_bounds (hbits.kind order (5 : Fin 8))
  have hb6 : 0 ≤ a (KIND order.val 6) ∧ a (KIND order.val 6) ≤ 1 := by
    simpa using bit_bounds (hbits.kind order (6 : Fin 8))
  have hb7 : 0 ≤ a (KIND order.val 7) ∧ a (KIND order.val 7) ≤ 1 := by
    simpa using bit_bounds (hbits.kind order (7 : Fin 8))
  rcases hsel with hsel | hsel | hsel | hsel | hsel | hsel | hsel | hsel <;>
    fin_cases kind <;>
    simp only [kindColumnValue] <;> split_ifs <;> omega

theorem fin8_cases (x : Fin 8) :
    x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 := by
  fin_cases x <;> simp

set_option maxRecDepth 4000 in
theorem bidActive_decoded
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) (order price : Fin 4) :
    (bidActive order.val price.val).eval a =
      if (((decodedWitness a).orders order).toLimitOrder.side = Side.bid ∧
          price.val ≤ ((decodedWitness a).orders order).toLimitOrder.limit)
      then 1 else 0 := by
  have hk := decoded_kind_coe hcanon hsat order
  have s0 := kind_selector_decoded hcanon hsat order (0 : Fin 8)
  have s1 := kind_selector_decoded hcanon hsat order (1 : Fin 8)
  have s2 := kind_selector_decoded hcanon hsat order (2 : Fin 8)
  have s3 := kind_selector_decoded hcanon hsat order (3 : Fin 8)
  have s4 := kind_selector_decoded hcanon hsat order (4 : Fin 8)
  have s5 := kind_selector_decoded hcanon hsat order (5 : Fin 8)
  have s6 := kind_selector_decoded hcanon hsat order (6 : Fin 8)
  have s7 := kind_selector_decoded hcanon hsat order (7 : Fin 8)
  have hcases := fin8_cases ((decodedWitness a).orders order).kind
  rcases hcases with hkind | hkind | hkind | hkind | hkind | hkind | hkind | hkind
  all_goals
    rw [hkind] at hk
    norm_num at hk
    rw [← hk] at s0 s1 s2 s3 s4 s5 s6 s7
    norm_num at s0 s1 s2 s3 s4 s5 s6 s7
    fin_cases price <;>
      norm_num [bidActive, sumE, add, v, c, EmittedExpr.eval,
        List.range_succ, Function.comp_apply, PrivateOrder.toLimitOrder,
        hkind, s0, s1, s2, s3, s4, s5, s6, s7]
  all_goals decide

set_option maxRecDepth 4000 in
theorem askActive_decoded
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) (order price : Fin 4) :
    (askActive order.val price.val).eval a =
      if (((decodedWitness a).orders order).toLimitOrder.side = Side.ask ∧
          ((decodedWitness a).orders order).toLimitOrder.limit ≤ price.val)
      then 1 else 0 := by
  have hk := decoded_kind_coe hcanon hsat order
  have s0 := kind_selector_decoded hcanon hsat order (0 : Fin 8)
  have s1 := kind_selector_decoded hcanon hsat order (1 : Fin 8)
  have s2 := kind_selector_decoded hcanon hsat order (2 : Fin 8)
  have s3 := kind_selector_decoded hcanon hsat order (3 : Fin 8)
  have s4 := kind_selector_decoded hcanon hsat order (4 : Fin 8)
  have s5 := kind_selector_decoded hcanon hsat order (5 : Fin 8)
  have s6 := kind_selector_decoded hcanon hsat order (6 : Fin 8)
  have s7 := kind_selector_decoded hcanon hsat order (7 : Fin 8)
  have hcases := fin8_cases ((decodedWitness a).orders order).kind
  rcases hcases with hkind | hkind | hkind | hkind | hkind | hkind | hkind | hkind
  all_goals
    rw [hkind] at hk
    norm_num at hk
    rw [← hk] at s0 s1 s2 s3 s4 s5 s6 s7
    norm_num at s0 s1 s2 s3 s4 s5 s6 s7
    fin_cases price <;>
      norm_num [askActive, sumE, add, v, c, EmittedExpr.eval,
        List.range_succ, Function.comp_apply, PrivateOrder.toLimitOrder,
        hkind, s0, s1, s2, s3, s4, s5, s6, s7]
  all_goals decide

theorem demand_body_mem (price : Fin 4) :
    sub (v (DEMAND price.val)) (demandExpr price.val) ∈ semanticBodies := by
  fin_cases price <;> decide

theorem supply_body_mem (price : Fin 4) :
    sub (v (SUPPLY price.val)) (supplyExpr price.val) ∈ semanticBodies := by
  fin_cases price <;> decide

theorem demandExpr_decoded
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) (price : Fin 4) :
    (demandExpr price.val).eval a = demand (privateBook (decodedWitness a)) price.val := by
  have h0 := bidActive_decoded hcanon hsat (0 : Fin 4) price
  have h1 := bidActive_decoded hcanon hsat (1 : Fin 4) price
  have h2 := bidActive_decoded hcanon hsat (2 : Fin 4) price
  have h3 := bidActive_decoded hcanon hsat (3 : Fin 4) price
  have q0 := decoded_qty_coe hcanon hsat (0 : Fin 4)
  have q1 := decoded_qty_coe hcanon hsat (1 : Fin 4)
  have q2 := decoded_qty_coe hcanon hsat (2 : Fin 4)
  have q3 := decoded_qty_coe hcanon hsat (3 : Fin 4)
  norm_num [demandExpr, sumE, mul, add, v, c, EmittedExpr.eval,
    List.range_succ, Function.comp_apply]
  norm_num at h0 h1 h2 h3 q0 q1 q2 q3
  rw [h0, h1, h2, h3]
  rw [← q0, ← q1, ← q2, ← q3]
  simp [privateBook, demand, demandIncr, PrivateOrder.toLimitOrder, List.ofFn_succ]

theorem supplyExpr_decoded
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) (price : Fin 4) :
    (supplyExpr price.val).eval a = supply (privateBook (decodedWitness a)) price.val := by
  have h0 := askActive_decoded hcanon hsat (0 : Fin 4) price
  have h1 := askActive_decoded hcanon hsat (1 : Fin 4) price
  have h2 := askActive_decoded hcanon hsat (2 : Fin 4) price
  have h3 := askActive_decoded hcanon hsat (3 : Fin 4) price
  have q0 := decoded_qty_coe hcanon hsat (0 : Fin 4)
  have q1 := decoded_qty_coe hcanon hsat (1 : Fin 4)
  have q2 := decoded_qty_coe hcanon hsat (2 : Fin 4)
  have q3 := decoded_qty_coe hcanon hsat (3 : Fin 4)
  norm_num [supplyExpr, sumE, mul, add, v, c, EmittedExpr.eval,
    List.range_succ, Function.comp_apply]
  norm_num at h0 h1 h2 h3 q0 q1 q2 q3
  rw [h0, h1, h2, h3]
  rw [← q0, ← q1, ← q2, ← q3]
  simp [privateBook, supply, supplyIncr, PrivateOrder.toLimitOrder, List.ofFn_succ]

theorem demand_decoded_bounds
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) (price : Fin 4) :
    0 ≤ demand (privateBook (decodedWitness a)) price.val ∧
      demand (privateBook (decodedWitness a)) price.val ≤ 60 := by
  have q0 := qty_column_bounds hcanon hsat (0 : Fin 4)
  have q1 := qty_column_bounds hcanon hsat (1 : Fin 4)
  have q2 := qty_column_bounds hcanon hsat (2 : Fin 4)
  have q3 := qty_column_bounds hcanon hsat (3 : Fin 4)
  have h0 := bidActive_decoded hcanon hsat (0 : Fin 4) price
  have h1 := bidActive_decoded hcanon hsat (1 : Fin 4) price
  have h2 := bidActive_decoded hcanon hsat (2 : Fin 4) price
  have h3 := bidActive_decoded hcanon hsat (3 : Fin 4) price
  norm_num at h0 h1 h2 h3 q0 q1 q2 q3
  have b0 : (bidActive 0 price.val).eval a = 0 ∨ (bidActive 0 price.val).eval a = 1 := by
    rw [h0]; split <;> simp
  have b1 : (bidActive 1 price.val).eval a = 0 ∨ (bidActive 1 price.val).eval a = 1 := by
    rw [h1]; split <;> simp
  have b2 : (bidActive 2 price.val).eval a = 0 ∨ (bidActive 2 price.val).eval a = 1 := by
    rw [h2]; split <;> simp
  have b3 : (bidActive 3 price.val).eval a = 0 ∨ (bidActive 3 price.val).eval a = 1 := by
    rw [h3]; split <;> simp
  rw [← demandExpr_decoded hcanon hsat price]
  norm_num [demandExpr, sumE, mul, add, v, c, EmittedExpr.eval,
    List.range_succ, Function.comp_apply]
  rcases b0 with b0 | b0 <;> rcases b1 with b1 | b1 <;>
    rcases b2 with b2 | b2 <;> rcases b3 with b3 | b3 <;> simp_all <;> omega

theorem supply_decoded_bounds
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) (price : Fin 4) :
    0 ≤ supply (privateBook (decodedWitness a)) price.val ∧
      supply (privateBook (decodedWitness a)) price.val ≤ 60 := by
  have q0 := qty_column_bounds hcanon hsat (0 : Fin 4)
  have q1 := qty_column_bounds hcanon hsat (1 : Fin 4)
  have q2 := qty_column_bounds hcanon hsat (2 : Fin 4)
  have q3 := qty_column_bounds hcanon hsat (3 : Fin 4)
  have h0 := askActive_decoded hcanon hsat (0 : Fin 4) price
  have h1 := askActive_decoded hcanon hsat (1 : Fin 4) price
  have h2 := askActive_decoded hcanon hsat (2 : Fin 4) price
  have h3 := askActive_decoded hcanon hsat (3 : Fin 4) price
  norm_num at h0 h1 h2 h3 q0 q1 q2 q3
  have b0 : (askActive 0 price.val).eval a = 0 ∨ (askActive 0 price.val).eval a = 1 := by
    rw [h0]; split <;> simp
  have b1 : (askActive 1 price.val).eval a = 0 ∨ (askActive 1 price.val).eval a = 1 := by
    rw [h1]; split <;> simp
  have b2 : (askActive 2 price.val).eval a = 0 ∨ (askActive 2 price.val).eval a = 1 := by
    rw [h2]; split <;> simp
  have b3 : (askActive 3 price.val).eval a = 0 ∨ (askActive 3 price.val).eval a = 1 := by
    rw [h3]; split <;> simp
  rw [← supplyExpr_decoded hcanon hsat price]
  norm_num [supplyExpr, sumE, mul, add, v, c, EmittedExpr.eval,
    List.range_succ, Function.comp_apply]
  rcases b0 with b0 | b0 <;> rcases b1 with b1 | b1 <;>
    rcases b2 with b2 | b2 <;> rcases b3 with b3 | b3 <;> simp_all <;> omega

theorem demand_column_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) (price : Fin 4) :
    a (DEMAND price.val) = demand (privateBook (decodedWitness a)) price.val := by
  have hgate := semantic_gate_vanishes hsat (demand_body_mem price)
  simp only [sub, neg, mul, add, v, c, EmittedExpr.eval] at hgate
  rw [demandExpr_decoded hcanon hsat price] at hgate
  have hcong : a (DEMAND price.val) ≡ demand (privateBook (decodedWitness a)) price.val
      [ZMOD BABYBEAR_MODULUS] := by
    simpa using hgate.add_right (demand (privateBook (decodedWitness a)) price.val)
  exact eq_of_modEq_of_canonical hcong (hcanon (DEMAND price.val)) (by
    have h := demand_decoded_bounds hcanon hsat price
    simp only [BABYBEAR_MODULUS]
    omega)

theorem supply_column_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) (price : Fin 4) :
    a (SUPPLY price.val) = supply (privateBook (decodedWitness a)) price.val := by
  have hgate := semantic_gate_vanishes hsat (supply_body_mem price)
  simp only [sub, neg, mul, add, v, c, EmittedExpr.eval] at hgate
  rw [supplyExpr_decoded hcanon hsat price] at hgate
  have hcong : a (SUPPLY price.val) ≡ supply (privateBook (decodedWitness a)) price.val
      [ZMOD BABYBEAR_MODULUS] := by
    simpa using hgate.add_right (supply (privateBook (decodedWitness a)) price.val)
  exact eq_of_modEq_of_canonical hcong (hcanon (SUPPLY price.val)) (by
    have h := supply_decoded_bounds hcanon hsat price
    simp only [BABYBEAR_MODULUS]
    omega)

def InZeroResidueWindow (x : Int) : Prop :=
  -BABYBEAR_MODULUS < x ∧ x < BABYBEAR_MODULUS

theorem eq_zero_of_modEq_zero_of_window {x : Int}
    (hmod : x ≡ 0 [ZMOD BABYBEAR_MODULUS])
    (hwindow : InZeroResidueWindow x) : x = 0 := by
  obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp hmod
  rcases hwindow with ⟨hlo, hhi⟩
  simp only [BABYBEAR_MODULUS] at hk hlo hhi
  omega

theorem volume_body_mem (price : Fin 4) :
    sub (v (VOLUME price.val))
      (add (mul (v (MIN_CHOOSE price.val)) (v (DEMAND price.val)))
        (mul (sub (c 1) (v (MIN_CHOOSE price.val))) (v (SUPPLY price.val)))) ∈
      semanticBodies := by
  fin_cases price <;> decide

theorem min_diff_relation_body_mem (price : Fin 4) :
    sub (v (MIN_DIFF price.val))
      (add (mul (v (MIN_CHOOSE price.val))
          (sub (v (SUPPLY price.val)) (v (DEMAND price.val))))
        (mul (sub (c 1) (v (MIN_CHOOSE price.val)))
          (sub (v (DEMAND price.val)) (v (SUPPLY price.val))))) ∈ semanticBodies := by
  fin_cases price <;> decide

theorem volume_column_selected_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) (price : Fin 4) :
    a (VOLUME price.val) =
      a (MIN_CHOOSE price.val) * a (DEMAND price.val) +
        (1 - a (MIN_CHOOSE price.val)) * a (SUPPLY price.val) := by
  have hc := (darkBazaarPrivateN4K4_private_bits_decoded hcanon hsat).minChoose price
  have hd := demand_decoded_bounds hcanon hsat price
  have hs := supply_decoded_bounds hcanon hsat price
  have hde := demand_column_exact hcanon hsat price
  have hse := supply_column_exact hcanon hsat price
  have hgate := semantic_gate_vanishes hsat (volume_body_mem price)
  have hres : a (VOLUME price.val) -
      (a (MIN_CHOOSE price.val) * a (DEMAND price.val) +
        (1 - a (MIN_CHOOSE price.val)) * a (SUPPLY price.val)) ≡
        0 [ZMOD BABYBEAR_MODULUS] := by
    simpa [sub, neg, mul, add, v, c, EmittedExpr.eval, sub_eq_add_neg] using hgate
  have hcong : a (VOLUME price.val) ≡
      a (MIN_CHOOSE price.val) * a (DEMAND price.val) +
        (1 - a (MIN_CHOOSE price.val)) * a (SUPPLY price.val)
      [ZMOD BABYBEAR_MODULUS] := by
    simpa using hres.add_right
      (a (MIN_CHOOSE price.val) * a (DEMAND price.val) +
        (1 - a (MIN_CHOOSE price.val)) * a (SUPPLY price.val))
  apply eq_of_modEq_of_canonical hcong (hcanon (VOLUME price.val))
  rw [hde, hse]
  rcases hc with hc | hc <;> simp [hc, BABYBEAR_MODULUS] <;> omega

theorem min_diff_relation_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) (price : Fin 4) :
    a (MIN_DIFF price.val) =
      a (MIN_CHOOSE price.val) * (a (SUPPLY price.val) - a (DEMAND price.val)) +
        (1 - a (MIN_CHOOSE price.val)) *
          (a (DEMAND price.val) - a (SUPPLY price.val)) := by
  have hc := (darkBazaarPrivateN4K4_private_bits_decoded hcanon hsat).minChoose price
  have hd := demand_decoded_bounds hcanon hsat price
  have hs := supply_decoded_bounds hcanon hsat price
  have hde := demand_column_exact hcanon hsat price
  have hse := supply_column_exact hcanon hsat price
  have hm := min_diff_column_bounds hcanon hsat price
  have hgate := semantic_gate_vanishes hsat (min_diff_relation_body_mem price)
  have hres : a (MIN_DIFF price.val) -
      (a (MIN_CHOOSE price.val) * (a (SUPPLY price.val) - a (DEMAND price.val)) +
        (1 - a (MIN_CHOOSE price.val)) *
          (a (DEMAND price.val) - a (SUPPLY price.val))) ≡
        0 [ZMOD BABYBEAR_MODULUS] := by
    simpa [sub, neg, mul, add, v, c, EmittedExpr.eval, sub_eq_add_neg] using hgate
  apply sub_eq_zero.mp
  apply eq_zero_of_modEq_zero_of_window hres
  simp only [InZeroResidueWindow, BABYBEAR_MODULUS]
  rw [hde, hse]
  rcases hc with hc | hc <;> simp [hc] <;> omega

theorem volume_column_semantic
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) (price : Fin 4) :
    a (VOLUME price.val) = execVol (privateBook (decodedWitness a)) price.val := by
  have hc := (darkBazaarPrivateN4K4_private_bits_decoded hcanon hsat).minChoose price
  have hv := volume_column_selected_exact hcanon hsat price
  have hm := min_diff_relation_exact hcanon hsat price
  have hmb := min_diff_column_bounds hcanon hsat price
  have hd := demand_column_exact hcanon hsat price
  have hs := supply_column_exact hcanon hsat price
  rcases hc with hc | hc
  · have hle : a (SUPPLY price.val) ≤ a (DEMAND price.val) := by
      simp [hc] at hm
      omega
    simp [hc] at hv
    unfold execVol
    rw [← hd, ← hs, min_eq_right hle]
    exact hv
  · have hle : a (DEMAND price.val) ≤ a (SUPPLY price.val) := by
      simp [hc] at hm
      omega
    simp [hc] at hv
    unfold execVol
    rw [← hd, ← hs, min_eq_left hle]
    exact hv

theorem volume_column_bounds
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) (price : Fin 4) :
    0 ≤ a (VOLUME price.val) ∧ a (VOLUME price.val) ≤ 60 := by
  rw [volume_column_semantic hcanon hsat price]
  simp only [execVol]
  have hd := demand_decoded_bounds hcanon hsat price
  have hs := supply_decoded_bounds hcanon hsat price
  omega

theorem select_sum_body_mem :
    sub (sumE ((List.range 4).map (fun price => v (SELECT price)))) (c 1) ∈
      semanticBodies := by decide

theorem pstar_body_mem :
    sub (v PSTAR)
      (sumE ((List.range 4).map
        (fun (price : Nat) => weighted (price : Int) (v (SELECT price))))) ∈
      semanticBodies := by decide

theorem vstar_body_mem :
    sub (v VSTAR)
      (sumE ((List.range 4).map
        (fun price => mul (v (SELECT price)) (v (VOLUME price))))) ∈ semanticBodies := by decide

theorem max_diff_relation_body_mem (price : Fin 4) :
    sub (v (MAX_DIFF price.val)) (sub (v VSTAR) (v (VOLUME price.val))) ∈
      semanticBodies := by
  fin_cases price <;> decide

theorem low_slack_relation_body_mem (price : Fin 4) :
    sub (v (LOW_SLACK price.val))
      (sub (v (MAX_DIFF price.val)) (laterSelected price.val)) ∈ semanticBodies := by
  fin_cases price <;> decide

theorem select_sum_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) :
    a (SELECT 0) + a (SELECT 1) + a (SELECT 2) + a (SELECT 3) = 1 := by
  have hbits := darkBazaarPrivateN4K4_private_bits_decoded hcanon hsat
  have hb0 := hbits.select 0; have hb1 := hbits.select 1
  have hb2 := hbits.select 2; have hb3 := hbits.select 3
  have hgate := semantic_gate_vanishes hsat select_sum_body_mem
  have hres :
      (a (SELECT 0) + a (SELECT 1) + a (SELECT 2) + a (SELECT 3)) - 1 ≡
        0 [ZMOD BABYBEAR_MODULUS] := by
    norm_num [sumE, sub, neg, mul, add, v, c, EmittedExpr.eval,
      List.range_succ, Function.comp_apply, add_assoc] at hgate
    simpa [sub_eq_add_neg, add_assoc] using hgate
  have hcong : a (SELECT 0) + a (SELECT 1) + a (SELECT 2) + a (SELECT 3) ≡
      1 [ZMOD BABYBEAR_MODULUS] := by
    simpa using hres.add_right 1
  apply eq_of_modEq_of_canonical hcong
  · rcases hb0 with hb0 | hb0 <;> rcases hb1 with hb1 | hb1 <;>
      rcases hb2 with hb2 | hb2 <;> rcases hb3 with hb3 | hb3 <;>
      simp_all [BABYBEAR_MODULUS]
  · norm_num [BABYBEAR_MODULUS]

theorem pstar_column_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) :
    a PSTAR = a (SELECT 1) + 2 * a (SELECT 2) + 3 * a (SELECT 3) := by
  have hbits := darkBazaarPrivateN4K4_private_bits_decoded hcanon hsat
  have hb1 := hbits.select 1; have hb2 := hbits.select 2; have hb3 := hbits.select 3
  have hgate := semantic_gate_vanishes hsat pstar_body_mem
  have hres : a PSTAR - (a (SELECT 1) + 2 * a (SELECT 2) + 3 * a (SELECT 3)) ≡
      0 [ZMOD BABYBEAR_MODULUS] := by
    norm_num [sumE, weighted, sub, neg, mul, add, v, c, EmittedExpr.eval,
      List.range_succ, Function.comp_apply, add_assoc] at hgate
    simpa [sub_eq_add_neg, add_assoc] using hgate
  have hcong : a PSTAR ≡ a (SELECT 1) + 2 * a (SELECT 2) + 3 * a (SELECT 3)
      [ZMOD BABYBEAR_MODULUS] := by
    simpa using hres.add_right (a (SELECT 1) + 2 * a (SELECT 2) + 3 * a (SELECT 3))
  apply eq_of_modEq_of_canonical hcong (hcanon PSTAR)
  rcases hb1 with hb1 | hb1 <;> rcases hb2 with hb2 | hb2 <;>
    rcases hb3 with hb3 | hb3 <;> simp_all [BABYBEAR_MODULUS]

theorem vstar_column_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) :
    a VSTAR =
      a (SELECT 0) * a (VOLUME 0) + a (SELECT 1) * a (VOLUME 1) +
        a (SELECT 2) * a (VOLUME 2) + a (SELECT 3) * a (VOLUME 3) := by
  have hbits := darkBazaarPrivateN4K4_private_bits_decoded hcanon hsat
  have hs0 := hbits.select 0; have hs1 := hbits.select 1
  have hs2 := hbits.select 2; have hs3 := hbits.select 3
  have hv0 := volume_column_bounds hcanon hsat (0 : Fin 4)
  have hv1 := volume_column_bounds hcanon hsat (1 : Fin 4)
  have hv2 := volume_column_bounds hcanon hsat (2 : Fin 4)
  have hv3 := volume_column_bounds hcanon hsat (3 : Fin 4)
  have hgate := semantic_gate_vanishes hsat vstar_body_mem
  have hres : a VSTAR -
      (a (SELECT 0) * a (VOLUME 0) + a (SELECT 1) * a (VOLUME 1) +
        a (SELECT 2) * a (VOLUME 2) + a (SELECT 3) * a (VOLUME 3)) ≡
        0 [ZMOD BABYBEAR_MODULUS] := by
    norm_num [sumE, sub, neg, mul, add, v, c, EmittedExpr.eval,
      List.range_succ, Function.comp_apply, add_assoc] at hgate
    simpa [sub_eq_add_neg, add_assoc] using hgate
  have hcong : a VSTAR ≡
      a (SELECT 0) * a (VOLUME 0) + a (SELECT 1) * a (VOLUME 1) +
        a (SELECT 2) * a (VOLUME 2) + a (SELECT 3) * a (VOLUME 3)
      [ZMOD BABYBEAR_MODULUS] := by
    simpa using hres.add_right
      (a (SELECT 0) * a (VOLUME 0) + a (SELECT 1) * a (VOLUME 1) +
        a (SELECT 2) * a (VOLUME 2) + a (SELECT 3) * a (VOLUME 3))
  apply eq_of_modEq_of_canonical hcong (hcanon VSTAR)
  rcases hs0 with hs0 | hs0 <;> rcases hs1 with hs1 | hs1 <;>
    rcases hs2 with hs2 | hs2 <;> rcases hs3 with hs3 | hs3 <;>
    simp_all [BABYBEAR_MODULUS] <;> omega

theorem vstar_column_bounds
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) :
    0 ≤ a VSTAR ∧ a VSTAR ≤ 60 := by
  rw [vstar_column_exact hcanon hsat]
  have hbits := darkBazaarPrivateN4K4_private_bits_decoded hcanon hsat
  have hs0 := hbits.select 0; have hs1 := hbits.select 1
  have hs2 := hbits.select 2; have hs3 := hbits.select 3
  have hsum := select_sum_exact hcanon hsat
  have hv0 := volume_column_bounds hcanon hsat (0 : Fin 4)
  have hv1 := volume_column_bounds hcanon hsat (1 : Fin 4)
  have hv2 := volume_column_bounds hcanon hsat (2 : Fin 4)
  have hv3 := volume_column_bounds hcanon hsat (3 : Fin 4)
  rcases hs0 with hs0 | hs0 <;> rcases hs1 with hs1 | hs1 <;>
    rcases hs2 with hs2 | hs2 <;> rcases hs3 with hs3 | hs3 <;> simp_all

theorem max_diff_relation_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) (price : Fin 4) :
    a (MAX_DIFF price.val) = a VSTAR - a (VOLUME price.val) := by
  have hm := max_diff_column_bounds hcanon hsat price
  have hv := volume_column_bounds hcanon hsat price
  have hs := vstar_column_bounds hcanon hsat
  have hgate := semantic_gate_vanishes hsat (max_diff_relation_body_mem price)
  have hres : a (MAX_DIFF price.val) - (a VSTAR - a (VOLUME price.val)) ≡
      0 [ZMOD BABYBEAR_MODULUS] := by
    simpa [sub, neg, mul, add, v, c, EmittedExpr.eval, sub_eq_add_neg] using hgate
  apply sub_eq_zero.mp
  exact eq_zero_of_modEq_zero_of_window hres (by
    simp only [InZeroResidueWindow, BABYBEAR_MODULUS]
    omega)

theorem low_slack_relation_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) (price : Fin 4) :
    a (LOW_SLACK price.val) =
      a (MAX_DIFF price.val) - (laterSelected price.val).eval a := by
  have hl := low_slack_column_bounds hcanon hsat price
  have hm := max_diff_column_bounds hcanon hsat price
  have hbits := darkBazaarPrivateN4K4_private_bits_decoded hcanon hsat
  have hs0 := hbits.select 0; have hs1 := hbits.select 1
  have hs2 := hbits.select 2; have hs3 := hbits.select 3
  have hlater : 0 ≤ (laterSelected price.val).eval a ∧
      (laterSelected price.val).eval a ≤ 3 := by
    fin_cases price <;>
      norm_num [laterSelected, sumE, add, v, c, EmittedExpr.eval,
        List.range_succ, Function.comp_apply, add_assoc] <;>
      rcases hs0 with hs0 | hs0 <;> rcases hs1 with hs1 | hs1 <;>
      rcases hs2 with hs2 | hs2 <;> rcases hs3 with hs3 | hs3 <;> simp_all
  have hgate := semantic_gate_vanishes hsat (low_slack_relation_body_mem price)
  have hres : a (LOW_SLACK price.val) -
      (a (MAX_DIFF price.val) - (laterSelected price.val).eval a) ≡
      0 [ZMOD BABYBEAR_MODULUS] := by
    simpa [sub, neg, mul, add, v, c, EmittedExpr.eval, sub_eq_add_neg] using hgate
  apply sub_eq_zero.mp
  exact eq_zero_of_modEq_zero_of_window hres (by
    simp only [InZeroResidueWindow, BABYBEAR_MODULUS]
    omega)

/-- Optimality plus strict dominance over all lower indices uniquely identifies
the fixed lowest-price clearing bucket. -/
theorem crossing_eq_of_optimal_and_lowest (bk : OrderBook) {chosen : Nat}
    (hchosen : chosen < PRICE_COUNT)
    (hmax : ∀ q < PRICE_COUNT, execVol bk q ≤ execVol bk chosen)
    (hlow : ∀ q < chosen, execVol bk q < execVol bk chosen) :
    crossing bk PRICE_COUNT = chosen := by
  have hwlt := crossing_lt bk (by decide : 0 < PRICE_COUNT)
  have hcw := hmax (crossing bk PRICE_COUNT) hwlt
  have hwc : execVol bk chosen ≤ execVol bk (crossing bk PRICE_COUNT) := by
    simpa only [execVol, clearedVolume] using clearedVolume_optimal bk PRICE_COUNT hchosen
  by_contra hne
  have hcases : crossing bk PRICE_COUNT < chosen ∨
      chosen < crossing bk PRICE_COUNT := by omega
  cases hcases with
  | inl h =>
      have := hlow (crossing bk PRICE_COUNT) h
      omega
  | inr h =>
      have hstrict : execVol bk chosen < execVol bk (crossing bk PRICE_COUNT) := by
        simpa only [clearedVolume] using crossing_strict_before bk h
      omega

theorem column_pstar_semantic
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) :
    (columnPublic a).pStar = crossing (privateBook (decodedWitness a)) PRICE_COUNT := by
  have hbits := darkBazaarPrivateN4K4_private_bits_decoded hcanon hsat
  have hb0 := hbits.select (0 : Fin 4); have hb1 := hbits.select (1 : Fin 4)
  have hb2 := hbits.select (2 : Fin 4); have hb3 := hbits.select (3 : Fin 4)
  have hsum := select_sum_exact hcanon hsat
  have hp := pstar_column_exact hcanon hsat
  have hv := vstar_column_exact hcanon hsat
  have hd0 := max_diff_relation_exact hcanon hsat (0 : Fin 4)
  have hd1 := max_diff_relation_exact hcanon hsat (1 : Fin 4)
  have hd2 := max_diff_relation_exact hcanon hsat (2 : Fin 4)
  have hd3 := max_diff_relation_exact hcanon hsat (3 : Fin 4)
  have hdb0 := max_diff_column_bounds hcanon hsat (0 : Fin 4)
  have hdb1 := max_diff_column_bounds hcanon hsat (1 : Fin 4)
  have hdb2 := max_diff_column_bounds hcanon hsat (2 : Fin 4)
  have hdb3 := max_diff_column_bounds hcanon hsat (3 : Fin 4)
  have hl0 := low_slack_relation_exact hcanon hsat (0 : Fin 4)
  have hl1 := low_slack_relation_exact hcanon hsat (1 : Fin 4)
  have hl2 := low_slack_relation_exact hcanon hsat (2 : Fin 4)
  have hl3 := low_slack_relation_exact hcanon hsat (3 : Fin 4)
  have hlb0 := low_slack_column_bounds hcanon hsat (0 : Fin 4)
  have hlb1 := low_slack_column_bounds hcanon hsat (1 : Fin 4)
  have hlb2 := low_slack_column_bounds hcanon hsat (2 : Fin 4)
  have hlb3 := low_slack_column_bounds hcanon hsat (3 : Fin 4)
  have he0 := volume_column_semantic hcanon hsat (0 : Fin 4)
  have he1 := volume_column_semantic hcanon hsat (1 : Fin 4)
  have he2 := volume_column_semantic hcanon hsat (2 : Fin 4)
  have he3 := volume_column_semantic hcanon hsat (3 : Fin 4)
  norm_num [laterSelected, sumE, add, v, c, EmittedExpr.eval,
    List.range_succ, Function.comp_apply, add_assoc] at hl0 hl1 hl2 hl3
  rcases hb0 with hb0 | hb0 <;> rcases hb1 with hb1 | hb1 <;>
    rcases hb2 with hb2 | hb2 <;> rcases hb3 with hb3 | hb3 <;> simp_all
  all_goals
    symm
    apply crossing_eq_of_optimal_and_lowest
    · simp [columnPublic, hp, PRICE_COUNT]
    · intro q hq
      simp only [PRICE_COUNT] at hq
      have hcases : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by omega
      rcases hcases with rfl | rfl | rfl | rfl <;> simp_all [columnPublic]
    · intro q hq
      have hcases : q = 0 ∨ q = 1 ∨ q = 2 := by
        change q < (a PSTAR).toNat at hq
        rw [hp] at hq
        omega
      rcases hcases with rfl | rfl | rfl <;> simp_all [columnPublic] <;> omega

theorem column_vstar_semantic
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) :
    (columnPublic a).vStar = clearedVolume (privateBook (decodedWitness a)) PRICE_COUNT := by
  have hbits := darkBazaarPrivateN4K4_private_bits_decoded hcanon hsat
  have hb0 := hbits.select (0 : Fin 4); have hb1 := hbits.select (1 : Fin 4)
  have hb2 := hbits.select (2 : Fin 4); have hb3 := hbits.select (3 : Fin 4)
  have hsum := select_sum_exact hcanon hsat
  have hp := pstar_column_exact hcanon hsat
  have hv := vstar_column_exact hcanon hsat
  have he0 := volume_column_semantic hcanon hsat (0 : Fin 4)
  have he1 := volume_column_semantic hcanon hsat (1 : Fin 4)
  have he2 := volume_column_semantic hcanon hsat (2 : Fin 4)
  have he3 := volume_column_semantic hcanon hsat (3 : Fin 4)
  have hcross := column_pstar_semantic hcanon hsat
  simp only [columnPublic] at hcross ⊢
  rw [clearedVolume, ← hcross]
  rcases hb0 with hb0 | hb0 <;> rcases hb1 with hb1 | hb1 <;>
    rcases hb2 with hb2 | hb2 <;> rcases hb3 with hb3 | hb3 <;>
    simp_all [execVol]

theorem darkBazaarPrivateN4K4_column_accepts
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (permOut : List Int → List Int)
    (hcanon : CanonicalAssignment a)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) :
    Accepts (permHash8 permOut) (columnPublic a) (decodedWitness a) := by
  refine ⟨decoded_blinding_canonical a hcanon, ?_, ?_, ?_, ?_⟩
  · simpa [columnPublic] using rule_column_exact hcanon hsat
  · exact column_root_semantic permOut hcanon hChip hsat
  · exact column_pstar_semantic hcanon hsat
  · exact column_vstar_semantic hcanon hsat

/-- **`DarkBazaarDescriptorToAccepts` is closed.** Satisfaction of the emitted
AIR, canonical trace and PI representatives, and the sound wide-Poseidon table
imply the exact private-book commitment and lowest-price volume-argmax semantics. -/
theorem darkBazaarPrivateN4K4_descriptor_to_accepts
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (permOut : List Int → List Int)
    (hcanon : CanonicalAssignment a)
    (hcanonPis : CanonicalAssignment pis)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) :
    Accepts (permHash8 permOut) (piPublic pis) (decodedWitness a) := by
  rw [pi_public_eq_column hcanon hcanonPis hsat]
  exact darkBazaarPrivateN4K4_column_accepts permOut hcanon hChip hsat

#assert_all_clean [
  Market.DarkBazaarPrivateDescriptor.orderCode_injective,
  Market.DarkBazaarPrivateDescriptor.packedBook_eq_bignumVal,
  Market.DarkBazaarPrivateDescriptor.bookLimbs_ranged,
  Market.DarkBazaarPrivateDescriptor.packedBook_injective_on_orders,
  Market.DarkBazaarPrivateDescriptor.argmaxUpto_strict_before,
  Market.DarkBazaarPrivateDescriptor.crossing_strict_before,
  Market.DarkBazaarPrivateDescriptor.check_sound,
  Market.DarkBazaarPrivateDescriptor.two_distinct_openings_yield_root_collision,
  Market.DarkBazaarPrivateDescriptor.darkBazaarPrivateN4K4_emitted_air_sound,
  Market.DarkBazaarPrivateDescriptor.binaryBody_zero_iff,
  Market.DarkBazaarPrivateDescriptor.darkBazaarPrivateN4K4_private_bits_decoded,
  Market.DarkBazaarPrivateDescriptor.packed_book_decoded,
  Market.DarkBazaarPrivateDescriptor.column_root_semantic,
  Market.DarkBazaarPrivateDescriptor.demand_column_exact,
  Market.DarkBazaarPrivateDescriptor.supply_column_exact,
  Market.DarkBazaarPrivateDescriptor.volume_column_semantic,
  Market.DarkBazaarPrivateDescriptor.column_pstar_semantic,
  Market.DarkBazaarPrivateDescriptor.column_vstar_semantic,
  Market.DarkBazaarPrivateDescriptor.pi_public_eq_column,
  Market.DarkBazaarPrivateDescriptor.darkBazaarPrivateN4K4_descriptor_to_accepts]

end Market.DarkBazaarPrivateDescriptor
