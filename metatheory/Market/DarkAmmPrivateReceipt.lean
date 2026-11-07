/-
# Market.DarkAmmPrivateReceipt — semantic contract for a hiding AMM transition receipt.

The public statement is `(session, rule, k, oldRoot[8], newRoot[8])`.  The
private witness carries bounded old reserves, nonzero trade amounts, and two
independent eight-felt blinds.  The new reserves are derived, never supplied as
an unconstrained second state.  Acceptance proves:

* the old hidden state opens `oldRoot` and already has product `k`;
* `dy ≤ y`, `dx > 0`, and `dy > 0`;
* the derived state is `(x+dx, y-dy)` and also has product `k`; and
* that derived state opens `newRoot` under the same state-commitment domain,
  so it can be consumed verbatim as the next transition's `oldRoot`.

The roots are abstract eight-lane hashes here.  A deployed descriptor must use
the repository's full-arity wide Poseidon chip and prove its `Satisfied2`
denotation refines this checker.  Collision resistance is named as the exact
bad event; no false finite-field injectivity theorem is asserted.
-/

import Market.DarkAmmPrivateSwap
import Dregg2.Tactics
import Mathlib.Tactic

namespace Market.DarkAmmPrivateReceipt

set_option autoImplicit false

def RESERVE_BOUND : Nat := 1024
def AMOUNT_BOUND : Nat := 1024
def DIGEST_WIDTH : Nat := 8
def BABYBEAR_MODULUS : Int := 2013265921
def RULE_ID : Int := 1145916752
/- A state commitment has one domain regardless of whether it is consumed as
an old state or produced as a new state. Keeping distinct old/new tags would
make `newRoot` unusable as the following transition's `oldRoot` except through
a hash collision, defeating receipt chaining. -/
def STATE_ROOT_DOMAIN_TAG : Int := 1145916751
def OLD_ROOT_DOMAIN_TAG : Int := STATE_ROOT_DOMAIN_TAG
def NEW_ROOT_DOMAIN_TAG : Int := STATE_ROOT_DOMAIN_TAG

structure PrivateWitness where
  x : Fin RESERVE_BOUND
  y : Fin RESERVE_BOUND
  dx : Fin AMOUNT_BOUND
  dy : Fin AMOUNT_BOUND
  oldBlind : Fin DIGEST_WIDTH → Int
  newBlind : Fin DIGEST_WIDTH → Int

structure PublicStatement where
  session : Int
  rule : Int
  k : Nat
  oldRoot : List Int
  newRoot : List Int
  deriving DecidableEq, Repr

def postX (w : PrivateWitness) : Nat := w.x.val + w.dx.val
def postY (w : PrivateWitness) : Nat := w.y.val - w.dy.val

def oldPreimage (pub : PublicStatement) (w : PrivateWitness) : List Int :=
  [OLD_ROOT_DOMAIN_TAG, pub.session, RULE_ID, pub.k, w.x.val, w.y.val] ++
    List.ofFn w.oldBlind ++ [0, 0]

def newPreimage (pub : PublicStatement) (w : PrivateWitness) : List Int :=
  [NEW_ROOT_DOMAIN_TAG, pub.session, RULE_ID, pub.k, postX w, postY w] ++
    List.ofFn w.newBlind ++ [0, 0]

/-- The receipt's output commitment is literally in the input-commitment
domain of the following receipt. Carrying the post reserves and new blind into
the next witness makes the two hash preimages equal, not merely related by an
informal protocol convention. -/
theorem newPreimage_eq_next_oldPreimage
    {pub nextPub : PublicStatement} {w next : PrivateWitness}
    (hsession : nextPub.session = pub.session)
    (hk : nextPub.k = pub.k)
    (hx : next.x.val = postX w)
    (hy : next.y.val = postY w)
    (hblind : next.oldBlind = w.newBlind) :
    newPreimage pub w = oldPreimage nextPub next := by
  simp [newPreimage, oldPreimage, OLD_ROOT_DOMAIN_TAG, NEW_ROOT_DOMAIN_TAG,
    STATE_ROOT_DOMAIN_TAG, hsession, hk, hx, hy, hblind]

#guard (oldPreimage
  { session := 1, rule := RULE_ID, k := 1, oldRoot := [], newRoot := [] }
  { x := ⟨1, by decide⟩, y := ⟨1, by decide⟩, dx := ⟨1, by decide⟩,
    dy := ⟨1, by decide⟩, oldBlind := fun _ => 0, newBlind := fun _ => 0 }).length == 16

def oldRoot (hash8 : List Int → List Int)
    (pub : PublicStatement) (w : PrivateWitness) : List Int :=
  hash8 (oldPreimage pub w)

def newRoot (hash8 : List Int → List Int)
    (pub : PublicStatement) (w : PrivateWitness) : List Int :=
  hash8 (newPreimage pub w)

def CanonicalBlind (blind : Fin DIGEST_WIDTH → Int) : Prop :=
  ∀ i, 0 ≤ blind i ∧ blind i < BABYBEAR_MODULUS

def canonicalBlindCheck (blind : Fin DIGEST_WIDTH → Int) : Bool :=
  (List.ofFn blind).all fun z => decide (0 ≤ z ∧ z < BABYBEAR_MODULUS)

theorem canonicalBlindCheck_iff (blind : Fin DIGEST_WIDTH → Int) :
    canonicalBlindCheck blind = true ↔ CanonicalBlind blind := by
  simp only [canonicalBlindCheck, CanonicalBlind, List.all_eq_true, List.mem_ofFn,
    decide_eq_true_eq]
  constructor
  · intro h i
    exact h _ ⟨i, rfl⟩
  · rintro h _ ⟨i, rfl⟩
    exact h i

/-- Exact fixed-family relation for the future hiding descriptor. -/
def Accepts (hash8 : List Int → List Int)
    (pub : PublicStatement) (w : PrivateWitness) : Prop :=
  CanonicalBlind w.oldBlind ∧
  CanonicalBlind w.newBlind ∧
  pub.rule = RULE_ID ∧
  pub.oldRoot = oldRoot hash8 pub w ∧
  pub.newRoot = newRoot hash8 pub w ∧
  0 < w.dx.val ∧
  0 < w.dy.val ∧
  w.dy.val ≤ w.y.val ∧
  w.x.val * w.y.val = pub.k ∧
  postX w * postY w = pub.k

def check (hash8 : List Int → List Int)
    (pub : PublicStatement) (w : PrivateWitness) : Bool :=
  canonicalBlindCheck w.oldBlind &&
  canonicalBlindCheck w.newBlind &&
  (pub.rule == RULE_ID) &&
  (pub.oldRoot == oldRoot hash8 pub w) &&
  (pub.newRoot == newRoot hash8 pub w) &&
  decide (0 < w.dx.val) &&
  decide (0 < w.dy.val) &&
  decide (w.dy.val ≤ w.y.val) &&
  decide (w.x.val * w.y.val = pub.k) &&
  decide (postX w * postY w = pub.k)

theorem check_iff (hash8 : List Int → List Int)
    (pub : PublicStatement) (w : PrivateWitness) :
    check hash8 pub w = true ↔ Accepts hash8 pub w := by
  simp [check, Accepts, canonicalBlindCheck_iff, and_assoc]

/-- Accepted receipt semantics refine the executable private-swap law. -/
theorem accepts_implies_admissible
    {hash8 : List Int → List Int}
    {pub : PublicStatement} {w : PrivateWitness}
    (h : Accepts hash8 pub w) :
    DarkAmmPrivateSwap.Admissible
      { x := w.x.val, y := w.y.val, k := pub.k }
      { dx := w.dx.val, dy := w.dy.val } := by
  exact ⟨h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩

theorem accepts_old_product
    {hash8 : List Int → List Int}
    {pub : PublicStatement} {w : PrivateWitness}
    (h : Accepts hash8 pub w) : w.x.val * w.y.val = pub.k :=
  h.2.2.2.2.2.2.2.2.1

theorem accepted_commit_is_derived_post
    {hash8 : List Int → List Int}
    {pub : PublicStatement} {w : PrivateWitness}
    (h : Accepts hash8 pub w) :
    DarkAmmPrivateSwap.commit
      { x := w.x.val, y := w.y.val, k := pub.k }
      { dx := w.dx.val, dy := w.dy.val } =
    { x := postX w, y := postY w, k := pub.k } := by
  exact DarkAmmPrivateSwap.admitted_commits_post (accepts_implies_admissible h)

/-- Exact computational bad event used by either state-root binding claim. -/
def RootCollision (hash8 : List Int → List Int)
    (left right : List Int) : Prop :=
  left ≠ right ∧ hash8 left = hash8 right

theorem distinct_accepted_old_openings_yield_collision
    {hash8 : List Int → List Int}
    {pub : PublicStatement} {left right : PrivateWitness}
    (hl : Accepts hash8 pub left) (hr : Accepts hash8 pub right)
    (hdiff : oldPreimage pub left ≠ oldPreimage pub right) :
    RootCollision hash8 (oldPreimage pub left) (oldPreimage pub right) := by
  exact ⟨hdiff, hl.2.2.2.1.symm.trans hr.2.2.2.1⟩

theorem distinct_accepted_new_openings_yield_collision
    {hash8 : List Int → List Int}
    {pub : PublicStatement} {left right : PrivateWitness}
    (hl : Accepts hash8 pub left) (hr : Accepts hash8 pub right)
    (hdiff : newPreimage pub left ≠ newPreimage pub right) :
    RootCollision hash8 (newPreimage pub left) (newPreimage pub right) := by
  exact ⟨hdiff, hl.2.2.2.2.1.symm.trans hr.2.2.2.2.1⟩

/-! Executable positive and refusal teeth. -/

def fixtureWitness : PrivateWitness where
  x := ⟨100, by decide⟩
  y := ⟨900, by decide⟩
  dx := ⟨50, by decide⟩
  dy := ⟨300, by decide⟩
  oldBlind := fun i => 1000 + i.val
  newBlind := fun i => 2000 + i.val

def toyHash8 (xs : List Int) : List Int :=
  (List.range DIGEST_WIDTH).map fun lane => xs.sum + 17 * lane

def fixturePublic : PublicStatement where
  session := 77
  rule := RULE_ID
  k := 90000
  oldRoot := oldRoot toyHash8
    { session := 77, rule := RULE_ID, k := 90000,
      oldRoot := [], newRoot := [] } fixtureWitness
  newRoot := newRoot toyHash8
    { session := 77, rule := RULE_ID, k := 90000,
      oldRoot := [], newRoot := [] } fixtureWitness

def wrongWitness : PrivateWitness :=
  { fixtureWitness with dy := ⟨301, by decide⟩ }

#guard check toyHash8 fixturePublic fixtureWitness
#guard !check toyHash8 fixturePublic wrongWitness
#guard !check toyHash8 { fixturePublic with k := 90001 } fixtureWitness
#guard !check toyHash8 { fixturePublic with oldRoot := [0] } fixtureWitness
#guard !check toyHash8 { fixturePublic with newRoot := [0] } fixtureWitness

theorem fixture_accepts : Accepts toyHash8 fixturePublic fixtureWitness :=
  (check_iff toyHash8 fixturePublic fixtureWitness).mp rfl

theorem wrong_quote_refused : ¬ Accepts toyHash8 fixturePublic wrongWitness := by
  intro h
  have hc := (check_iff toyHash8 fixturePublic wrongWitness).mpr h
  change false = true at hc
  contradiction

#assert_all_clean [
  Market.DarkAmmPrivateReceipt.canonicalBlindCheck_iff,
  Market.DarkAmmPrivateReceipt.check_iff,
  Market.DarkAmmPrivateReceipt.accepts_implies_admissible,
  Market.DarkAmmPrivateReceipt.accepts_old_product,
  Market.DarkAmmPrivateReceipt.accepted_commit_is_derived_post,
  Market.DarkAmmPrivateReceipt.newPreimage_eq_next_oldPreimage,
  Market.DarkAmmPrivateReceipt.distinct_accepted_old_openings_yield_collision,
  Market.DarkAmmPrivateReceipt.distinct_accepted_new_openings_yield_collision,
  Market.DarkAmmPrivateReceipt.fixture_accepts,
  Market.DarkAmmPrivateReceipt.wrong_quote_refused]

end Market.DarkAmmPrivateReceipt
