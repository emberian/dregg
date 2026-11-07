/-
# A live DescriptorIR2 backend for intensional-CCC interaction receipts

`IntensionalCCCInteractionBridge` proves that a typed STLC local step determines
an exact executable Boolean interaction receipt, but deliberately stops before
emitting a circuit descriptor.  This module closes that backend boundary.

For a step at arbitrary finite address depth `d`, the emitted one-row IR-v2
statement publishes the complete lossless receipt layout (root rule and all
`d` path tags) and two domain-separated endpoint commitments.  The main row is
bound field-for-field to those public inputs.  Two live hash sites recompute
the before/after commitments from the published layout.  Thus an arbitrary
satisfying trace cannot substitute a different rule, binder side, or address;
under the named collision-resistance boundary it cannot substitute a different
receipt behind either endpoint commitment either.

The construction honestly binds the executable receipt, not the full typed
source nets.  The old bridge intentionally forgets those nets: two syntactically
different beta redexes have the same root/address receipt.  The final section
formalizes that obstruction.  Binding full typed endpoints requires a separate
typed-syntax commitment or a materialized typed-net table; DescriptorIR2 cannot
recover information already erased by `layout`.

This is a standalone additive module.  Integration imports are left to the
owner of the canonical direct-logic umbrella.
-/

import Dregg2.Calculus.IntensionalCCCInteractionBridge
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Calculus.IntensionalCCCInteractionDescriptorIR2

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Calculus.IntensionalCCCTrace
open Dregg2.Calculus.IntensionalCCCInteractionBridge
open Dregg2.Calculus.IntensionalCCCInteractionBridge.Receipt

abbrev BoolLocalCert := Dregg2.Calculus.InteractionNetTrace.LocalCert

set_option autoImplicit false

def BABYBEAR_MODULUS : Int := 2013265921

/-! ## 1. Lossless receipt words -/

def rootCode : RootTag -> Nat
  | .beta => 0
  | .eta => 1
  | .fstPair => 2
  | .sndPair => 3

theorem rootCode_injective : Function.Injective rootCode := by
  intro a b h
  cases a <;> cases b <;> simp [rootCode] at h ⊢

def pathWords (path : List PathTag) : List Int :=
  path.map fun tag => tag.code

theorem pathWords_injective : Function.Injective pathWords := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      cases ys <;> simp [pathWords] at h ⊢
  | cons x xs ih =>
      intro ys h
      cases ys with
      | nil => simp [pathWords] at h
      | cons y ys =>
          simp only [pathWords, List.map_cons, List.cons.injEq] at h
          have hxy : x = y := pathTag_code_injective (Int.ofNat_inj.mp h.1)
          subst y
          have htail : xs = ys := ih h.2
          subst ys
          rfl

/-- The public lossless encoding of one root rule and its complete local
address.  These are small tags, not a hash. -/
def layoutWords (source : Layout) : List Int :=
  (rootCode source.root : Int) :: pathWords source.path

theorem layoutWords_injective : Function.Injective layoutWords := by
  intro left right h
  have hrootCode : rootCode left.root = rootCode right.root := by
    exact Int.ofNat_inj.mp (List.cons.inj h).1
  have hpathWords : pathWords left.path = pathWords right.path :=
    (List.cons.inj h).2
  have hroot : left.root = right.root := rootCode_injective hrootCode
  have hpath : left.path = right.path := pathWords_injective hpathWords
  cases left
  cases right
  simp_all

/-- The certificate and its two executable endpoints determined by a layout. -/
def localCertOfLayout (source : Layout) : BoolLocalCert where
  context := encodeContext source.path
  rule := source.root.rule

def receiptOfLayout (source : Layout) : CheckedReceipt :=
  let cert := localCertOfLayout source
  ⟨cert.before, cert, cert.after⟩

@[simp] theorem receiptOfLayout_checks (source : Layout) :
    (receiptOfLayout source).check = true := by
  simp [receiptOfLayout, localCertOfLayout, CheckedReceipt.check,
    Dregg2.Calculus.InteractionNetTrace.LocalCert.check]

theorem localCertOfLayout_injective : Function.Injective localCertOfLayout := by
  intro left right h
  have hcontext : encodeContext left.path = encodeContext right.path :=
    congrArg (fun c : BoolLocalCert => c.context) h
  have hrule : left.root.rule = right.root.rule :=
    congrArg (fun c : BoolLocalCert => c.rule) h
  have hroot : left.root = right.root := rootTag_rule_injective hrule
  have hpath : left.path = right.path := encodeContext_injective hcontext
  cases left
  cases right
  simp_all

theorem receiptOfLayout_injective : Function.Injective receiptOfLayout := by
  intro left right h
  apply localCertOfLayout_injective
  exact congrArg CheckedReceipt.cert h

theorem stepReceipt_eq_receiptOfLayout
    {Γ : List Ty} {A : Ty} {before after : Net Γ A}
    (step : LocalStep before after) :
    stepReceipt step = receiptOfLayout (layout step) := by
  rfl

/-! ## 2. Public columns and domain-separated commitments -/

def BEFORE_DOMAIN : Int := 1001
def AFTER_DOMAIN : Int := 1002

def rootCol : Nat := 0
def pathCol (i : Nat) : Nat := i + 1
def beforeDomainCol (depth : Nat) : Nat := depth + 1
def afterDomainCol (depth : Nat) : Nat := depth + 2
def beforeDigestCol (depth : Nat) : Nat := depth + 3
def afterDigestCol (depth : Nat) : Nat := depth + 4
def traceWidth (depth : Nat) : Nat := depth + 5

def beforeWords (source : Layout) : List Int :=
  BEFORE_DOMAIN :: layoutWords source

def afterWords (source : Layout) : List Int :=
  AFTER_DOMAIN :: layoutWords source

def beforeCommit (hash : List Int -> Int) (source : Layout) : Int :=
  hash (beforeWords source)

def afterCommit (hash : List Int -> Int) (source : Layout) : Int :=
  hash (afterWords source)

/-- All row cells are verifier-visible.  The endpoint digests are recomputed
again by the two hash sites below, so they are not merely trusted PIs. -/
def publicOf (hash : List Int -> Int) (source : Layout) : Assignment
  | 0 => rootCode source.root
  | k + 1 =>
      if hpath : k < source.path.length then
        source.path[k].code
      else if k = source.path.length then BEFORE_DOMAIN
      else if k = source.path.length + 1 then AFTER_DOMAIN
      else if k = source.path.length + 2 then beforeCommit hash source
      else if k = source.path.length + 3 then afterCommit hash source
      else 0

@[simp] theorem publicOf_root (hash : List Int -> Int) (source : Layout) :
    publicOf hash source rootCol = rootCode source.root := rfl

@[simp] theorem publicOf_path (hash : List Int -> Int) (source : Layout)
    (i : Nat) (hi : i < source.path.length) :
    publicOf hash source (pathCol i) = source.path[i].code := by
  simp [publicOf, pathCol, hi]

@[simp] theorem publicOf_beforeDomain (hash : List Int -> Int) (source : Layout) :
    publicOf hash source (beforeDomainCol source.path.length) = BEFORE_DOMAIN := by
  simp [publicOf, beforeDomainCol]

@[simp] theorem publicOf_afterDomain (hash : List Int -> Int) (source : Layout) :
    publicOf hash source (afterDomainCol source.path.length) = AFTER_DOMAIN := by
  simp [publicOf, afterDomainCol]

@[simp] theorem publicOf_beforeDigest (hash : List Int -> Int) (source : Layout) :
    publicOf hash source (beforeDigestCol source.path.length) = beforeCommit hash source := by
  simp [publicOf, beforeDigestCol]

@[simp] theorem publicOf_afterDigest (hash : List Int -> Int) (source : Layout) :
    publicOf hash source (afterDigestCol source.path.length) = afterCommit hash source := by
  simp [publicOf, afterDigestCol]

def layoutInputs (depth : Nat) : List HashInput :=
  .col rootCol :: (List.range depth).map fun i => .col (pathCol i)

def beforeInputs (depth : Nat) : List HashInput :=
  .col (beforeDomainCol depth) :: layoutInputs depth

def afterInputs (depth : Nat) : List HashInput :=
  .col (afterDomainCol depth) :: layoutInputs depth

def endpointHashSites (depth : Nat) : List VmHashSite :=
  [ { digestCol := beforeDigestCol depth
      inputs := beforeInputs depth, arity := depth + 2 }
  , { digestCol := afterDigestCol depth
      inputs := afterInputs depth, arity := depth + 2 } ]

/-- The live shared Poseidon2 table accepts at most `CHIP_RATE = 16` absorbed
felts in one site.  Hence the directly deployable one-site-per-endpoint fragment
has address depth at most fourteen.  Deeper receipts remain meaningful in the
abstract IR denotation but require a multi-block sponge lowering. -/
def LiveDepth (depth : Nat) : Prop := depth + 2 <= CHIP_RATE

def MAX_LIVE_DEPTH : Nat := CHIP_RATE - 2

theorem max_live_depth_exact : MAX_LIVE_DEPTH = 14 := by decide

theorem endpointHashSites_within_live_rate (depth : Nat) (hdepth : LiveDepth depth)
    (site : VmHashSite) (hsite : site ∈ endpointHashSites depth) :
    site.arity <= CHIP_RATE := by
  simp [endpointHashSites] at hsite
  rcases hsite with rfl | rfl <;> exact hdepth

/-! ## 3. Live descriptor compiler -/

def publicPins (depth : Nat) : List VmConstraint2 :=
  (List.range (traceWidth depth)).map fun c =>
    .base (.piBinding .first c c)

/-- One reusable descriptor shape per address depth.  A typed step selects the
public statement, not a new arithmetic program. -/
def descriptorAtDepth (depth : Nat) : EffectVmDescriptor2 :=
  { name := "dregg-intensional-ccc-local-receipt-v2-depth-" ++ toString depth
  , traceWidth := traceWidth depth
  , piCount := traceWidth depth
  , tables := [mainTableDef (traceWidth depth)]
  , constraints := publicPins depth
  , hashSites := endpointHashSites depth
  , ranges := [] }

def descriptor {Γ : List Ty} {A : Ty} {before after : Net Γ A}
    (step : LocalStep before after) :
    EffectVmDescriptor2 :=
  descriptorAtDepth (layout step).path.length

theorem descriptor_shape_exact (depth : Nat) :
    (descriptorAtDepth depth).traceWidth = depth + 5 /\
      (descriptorAtDepth depth).piCount = depth + 5 /\
      (descriptorAtDepth depth).constraints.length = depth + 5 /\
      (descriptorAtDepth depth).hashSites.length = 2 /\
      (descriptorAtDepth depth).ranges = [] := by
  simp [descriptorAtDepth, traceWidth, publicPins, endpointHashSites]

structure Cost where
  addressDepth : Nat
  publicInputs : Nat
  traceColumns : Nat
  linearPiConstraints : Nat
  hashSites : Nat
  absorbedFelts : Nat
  maxArithmeticGateDegree : Nat
  deriving DecidableEq, Repr

def costAtDepth (depth : Nat) : Cost :=
  { addressDepth := depth
  , publicInputs := (descriptorAtDepth depth).piCount
  , traceColumns := (descriptorAtDepth depth).traceWidth
  , linearPiConstraints := (descriptorAtDepth depth).constraints.length
  , hashSites := (descriptorAtDepth depth).hashSites.length
  , absorbedFelts := 2 * (depth + 2)
  , maxArithmeticGateDegree := 1 }

theorem cost_exact (depth : Nat) :
    costAtDepth depth =
      { addressDepth := depth, publicInputs := depth + 5,
        traceColumns := depth + 5, linearPiConstraints := depth + 5,
        hashSites := 2, absorbedFelts := 2 * (depth + 2),
        maxArithmeticGateDegree := 1 } := by
  simp [costAtDepth, descriptorAtDepth, traceWidth, publicPins, endpointHashSites]

/-! ## 4. Constructive complete witness -/

def rowOf (hash : List Int -> Int) (source : Layout) : Assignment :=
  publicOf hash source

def traceOf (hash : List Int -> Int) (source : Layout) : VmTrace :=
  { rows := [rowOf hash source]
  , pub := publicOf hash source
  , tf := fun _ => [] }

private theorem resolved_layoutInputs (hash : List Int -> Int) (source : Layout)
    (acc : List Int) :
    (layoutInputs source.path.length).map
        (HashInput.resolve (envAt (traceOf hash source) 0) acc) = layoutWords source := by
  simp only [layoutInputs, List.map_cons, HashInput.resolve, layoutWords, List.cons.injEq]
  constructor
  · rfl
  · rw [List.map_map]
    apply List.ext_getElem
    · simp [pathWords]
    · intro i hiLeft hiRight
      have hi : i < source.path.length := by simpa [pathWords] using hiRight
      simp [HashInput.resolve, envAt, traceOf, rowOf, pathWords, publicOf_path, hi]

private theorem resolved_beforeInputs (hash : List Int -> Int) (source : Layout)
    (acc : List Int) :
    (beforeInputs source.path.length).map
        (HashInput.resolve (envAt (traceOf hash source) 0) acc) = beforeWords source := by
  simp only [beforeInputs, List.map_cons, beforeWords, List.cons.injEq]
  constructor
  · change publicOf hash source (beforeDomainCol source.path.length) = BEFORE_DOMAIN
    exact publicOf_beforeDomain hash source
  · exact resolved_layoutInputs hash source acc

private theorem resolved_afterInputs (hash : List Int -> Int) (source : Layout)
    (acc : List Int) :
    (afterInputs source.path.length).map
        (HashInput.resolve (envAt (traceOf hash source) 0) acc) = afterWords source := by
  simp only [afterInputs, List.map_cons, afterWords, List.cons.injEq]
  constructor
  · change publicOf hash source (afterDomainCol source.path.length) = AFTER_DOMAIN
    exact publicOf_afterDomain hash source
  · exact resolved_layoutInputs hash source acc

theorem traceOf_hashes (hash : List Int -> Int) (source : Layout) :
    siteHoldsAll hash (envAt (traceOf hash source) 0)
      (endpointHashSites source.path.length) := by
  change
    rowOf hash source (beforeDigestCol source.path.length) =
        hash ((beforeInputs source.path.length).map
          (HashInput.resolve (envAt (traceOf hash source) 0) [])) /\
      rowOf hash source (afterDigestCol source.path.length) =
        hash ((afterInputs source.path.length).map
          (HashInput.resolve (envAt (traceOf hash source) 0)
            [hash ((beforeInputs source.path.length).map
              (HashInput.resolve (envAt (traceOf hash source) 0) []))])) /\ True
  rw [rowOf, publicOf_beforeDigest, beforeCommit, resolved_beforeInputs hash source []]
  rw [publicOf_afterDigest, afterCommit]
  constructor
  · rfl
  · constructor
    · rw [show (afterInputs source.path.length).map
          (HashInput.resolve (envAt (traceOf hash source) 0)
            [hash (beforeWords source)]) = afterWords source by
          exact resolved_afterInputs hash source [hash (beforeWords source)]]
    · trivial

theorem memLog_descriptorAtDepth (depth : Nat) (trace : VmTrace) :
    memLog (descriptorAtDepth depth) trace = [] := by
  simp [memLog, memOpsOf, descriptorAtDepth, publicPins]

theorem mapLog_descriptorAtDepth (depth : Nat) (trace : VmTrace) :
    mapLog (descriptorAtDepth depth) trace = [] := by
  simp [mapLog, mapOpsOf, descriptorAtDepth, publicPins]

/-- Every typed local step constructs a complete live IR-v2 witness. -/
theorem trace_complete (hash : List Int -> Int)
    {Γ : List Ty} {A : Ty} {before after : Net Γ A}
    (step : LocalStep before after) :
    Satisfied2 hash (descriptor step) (fun _ => 0)
      (fun _ => ((0 : Int), 0)) []
      (traceOf hash (layout step)) := by
  let depth := (layout step).path.length
  refine ⟨?_, ?_, ?_, List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    have hi0 : i = 0 := by
      simp [traceOf] at hi
      omega
    subst i
    simp only [descriptor, descriptorAtDepth] at hc
    simp only [publicPins, List.mem_map] at hc
    obtain ⟨col, hcol, rfl⟩ := hc
    simp [VmConstraint2.holdsAt, traceOf, rowOf, envAt]
  · intro i hi
    have hi0 : i = 0 := by
      simp [traceOf] at hi
      omega
    subst i
    exact traceOf_hashes hash (layout step)
  · intro i hi r hr
    simp [descriptor, descriptorAtDepth] at hr
  · intro op hop
    rw [show descriptor step = descriptorAtDepth (layout step).path.length by rfl,
      memLog_descriptorAtDepth] at hop
    cases hop
  · rw [show descriptor step = descriptorAtDepth (layout step).path.length by rfl,
      memLog_descriptorAtDepth]
    trivial
  · rw [show descriptor step = descriptorAtDepth (layout step).path.length by rfl,
      memLog_descriptorAtDepth]
    simpa using
      (memCheck_nil (fun _ : Int => 0) (fun _ : Int => ((0 : Int), 0)))
  · rw [show descriptor step = descriptorAtDepth (layout step).path.length by rfl,
      memLog_descriptorAtDepth]
    simp [traceOf]
  · rw [show descriptor step = descriptorAtDepth (layout step).path.length by rfl,
      mapLog_descriptorAtDepth]
    simp [traceOf]

/-! ## 5. Arbitrary satisfying-trace soundness -/

def withPublic (hash : List Int -> Int) (source : Layout) (trace : VmTrace) : VmTrace :=
  { trace with pub := publicOf hash source }

def CanonicalFirstLayoutRow (source : Layout) (trace : VmTrace) : Prop :=
  (0 <= (envAt trace 0).loc rootCol /\
    (envAt trace 0).loc rootCol < BABYBEAR_MODULUS) /\
  forall i, i < source.path.length ->
    0 <= (envAt trace 0).loc (pathCol i) /\
      (envAt trace 0).loc (pathCol i) < BABYBEAR_MODULUS

def StatementSatisfied (hash : List Int -> Int)
    {Γ : List Ty} {A : Ty} {before after : Net Γ A}
    (step : LocalStep before after)
    (trace : VmTrace) : Prop :=
  trace.rows ≠ [] /\
    CanonicalFirstLayoutRow (layout step) trace /\
    Satisfied2 hash (descriptor step) (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (withPublic hash (layout step) trace)

theorem eq_of_modEq_of_canonical {x y : Int}
    (hmod : x ≡ y [ZMOD 2013265921])
    (hx : 0 <= x /\ x < BABYBEAR_MODULUS)
    (hy : 0 <= y /\ y < BABYBEAR_MODULUS) : x = y := by
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hmod
  simp only [BABYBEAR_MODULUS] at hk hx hy
  omega

theorem public_pin_modEq (hash : List Int -> Int) (source : Layout)
    (trace : VmTrace) (hne : trace.rows ≠ [])
    (hsat : Satisfied2 hash (descriptorAtDepth source.path.length) (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (withPublic hash source trace))
    (c : Nat) (hc : c < traceWidth source.path.length) :
    (envAt trace 0).loc c ≡ publicOf hash source c [ZMOD 2013265921] := by
  have hpos : 0 < (withPublic hash source trace).rows.length := by
    simp [withPublic]
    exact List.length_pos_iff.mpr hne
  have h := hsat.rowConstraints 0 hpos
    (.base (.piBinding .first c c)) (by
      simp [descriptorAtDepth, publicPins, hc])
  simpa [VmConstraint2.holdsAt, withPublic, envAt] using h

theorem root_code_bound (root : RootTag) :
    0 <= (rootCode root : Int) /\ (rootCode root : Int) < BABYBEAR_MODULUS := by
  cases root <;> decide

theorem path_code_bound (tag : PathTag) :
    0 <= (tag.code : Int) /\ (tag.code : Int) < BABYBEAR_MODULUS := by
  cases tag <;> decide

theorem satisfying_root_exact (hash : List Int -> Int)
    {Γ : List Ty} {A : Ty} {before after : Net Γ A}
    (step : LocalStep before after)
    (trace : VmTrace) (h : StatementSatisfied hash step trace) :
    (envAt trace 0).loc rootCol = rootCode (layout step).root := by
  exact eq_of_modEq_of_canonical
    (public_pin_modEq hash (layout step) trace h.1 h.2.2 rootCol (by
      simp [traceWidth, rootCol]))
    h.2.1.1 (root_code_bound (layout step).root)

theorem satisfying_path_exact (hash : List Int -> Int)
    {Γ : List Ty} {A : Ty} {before after : Net Γ A}
    (step : LocalStep before after)
    (trace : VmTrace) (h : StatementSatisfied hash step trace)
    (i : Nat) (hi : i < (layout step).path.length) :
    (envAt trace 0).loc (pathCol i) = (layout step).path[i].code := by
  exact eq_of_modEq_of_canonical
    (by simpa [publicOf_path hash (layout step) i hi] using
      public_pin_modEq hash (layout step) trace h.1 h.2.2 (pathCol i) (by
        simp [traceWidth, pathCol]
        omega))
    (h.2.1.2 i hi) (path_code_bound (layout step).path[i])

def firstRowLayoutWords (depth : Nat) (trace : VmTrace) : List Int :=
  (envAt trace 0).loc rootCol ::
    (List.range depth).map fun i => (envAt trace 0).loc (pathCol i)

/-- Soundness for an arbitrary satisfying witness: its exact decoded root and
address are the typed step's receipt layout, not prover-selected data. -/
theorem satisfying_layout_words_exact (hash : List Int -> Int)
    {Γ : List Ty} {A : Ty} {before after : Net Γ A}
    (step : LocalStep before after)
    (trace : VmTrace) (h : StatementSatisfied hash step trace) :
    firstRowLayoutWords (layout step).path.length trace = layoutWords (layout step) := by
  simp only [firstRowLayoutWords, layoutWords, List.cons.injEq]
  constructor
  · exact satisfying_root_exact hash step trace h
  · apply List.ext_getElem
    · simp [pathWords]
    · intro i hiLeft hiRight
      have hi : i < (layout step).path.length := by simpa [pathWords] using hiRight
      simp [pathWords, satisfying_path_exact hash step trace h i hi]

/-- Any candidate receipt matching the satisfying row is definitionally the
exact executable receipt translated from the typed step, including both
before and after graph endpoints. -/
theorem satisfying_trace_binds_exact_receipt (hash : List Int -> Int)
    {Γ : List Ty} {A : Ty} {before after : Net Γ A}
    (step : LocalStep before after)
    (trace : VmTrace) (h : StatementSatisfied hash step trace)
    (candidate : Layout)
    (hcandidate : layoutWords candidate =
      firstRowLayoutWords (layout step).path.length trace) :
    receiptOfLayout candidate = stepReceipt step := by
  rw [satisfying_layout_words_exact hash step trace h] at hcandidate
  have : candidate = layout step := layoutWords_injective hcandidate
  subst candidate
  exact (stepReceipt_eq_receiptOfLayout step).symm

/-- The arbitrary-trace binding theorem composes with the existing receipt
checker and the typed local-step theorem.  Acceptance therefore witnesses both
an exact Boolean interaction and preservation of the original higher-order
typed denotation; the Boolean graph is not misrepresented as that denotation. -/
theorem satisfying_trace_relation_sound (hash : List Int -> Int)
    {Γ : List Ty} {A : Ty} {before after : Net Γ A}
    (step : LocalStep before after) (trace : VmTrace)
    (h : StatementSatisfied hash step trace) (candidate : Layout)
    (hcandidate : layoutWords candidate =
      firstRowLayoutWords (layout step).path.length trace)
    (env : Env Γ) :
    (receiptOfLayout candidate).check = true /\
      after.denote env = before.denote env := by
  have hreceipt := satisfying_trace_binds_exact_receipt
    hash step trace h candidate hcandidate
  rw [hreceipt]
  exact translatedStep_checked_and_source_sound step env

/-- The endpoint PIs carried by an arbitrary satisfying trace equal the two
domain-separated layout commitments in the field. -/
theorem satisfying_endpoint_commitments (hash : List Int -> Int)
    {Γ : List Ty} {A : Ty} {before after : Net Γ A}
    (step : LocalStep before after)
    (trace : VmTrace) (h : StatementSatisfied hash step trace) :
    (envAt trace 0).loc (beforeDigestCol (layout step).path.length) ≡
        beforeCommit hash (layout step) [ZMOD 2013265921] /\
      (envAt trace 0).loc (afterDigestCol (layout step).path.length) ≡
        afterCommit hash (layout step) [ZMOD 2013265921] := by
  constructor
  · simpa using public_pin_modEq hash (layout step) trace h.1 h.2.2
      (beforeDigestCol (layout step).path.length) (by
        simp [beforeDigestCol, traceWidth])
  · simpa using public_pin_modEq hash (layout step) trace h.1 h.2.2
      (afterDigestCol (layout step).path.length) (by
        simp [afterDigestCol, traceWidth])

/-- One collision-resistant endpoint commitment is already binding because
its preimage contains the full lossless receipt layout. -/
theorem beforeCommit_binds (hash : List Int -> Int)
    (hCR : Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR hash)
    {left right : Layout}
    (h : beforeCommit hash left = beforeCommit hash right) :
    receiptOfLayout left = receiptOfLayout right := by
  have hwords : beforeWords left = beforeWords right := hCR _ _ h
  have hlayout : layoutWords left = layoutWords right := (List.cons.inj hwords).2
  exact congrArg receiptOfLayout (layoutWords_injective hlayout)

/-! ## 6. Exact wire guard, refusal, and the typed-endpoint obstruction -/

namespace Reference

def nestedStep := IntensionalCCCInteractionBridge.Receipt.Reference.underShareBody
def nestedLayout : Layout := layout nestedStep
def nestedDescriptor : EffectVmDescriptor2 := descriptor nestedStep

theorem nested_layout_exact : nestedLayout = ⟨.beta, [.shareBody]⟩ := by decide

theorem nested_cost_exact :
    costAtDepth nestedLayout.path.length =
      { addressDepth := 1, publicInputs := 6, traceColumns := 6,
        linearPiConstraints := 6, hashSites := 2, absorbedFelts := 6,
        maxArithmeticGateDegree := 1 } := by
  rw [nested_layout_exact]
  exact cost_exact 1

#guard emitVmJson2 nestedDescriptor ==
  "{\"name\":\"dregg-intensional-ccc-local-receipt-v2-depth-1\",\"ir\":2,\"trace_width\":6,\"public_input_count\":6,\"challenges\":0,\"tables\":[{\"id\":0,\"name\":\"main\",\"arity\":6,\"sem\":\"main\"}],\"constraints\":[{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":0,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":1,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":2,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":3,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":4,\"pi_index\":4},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":5,\"pi_index\":5}],\"hash_sites\":[{\"digest_col\":4,\"arity\":3,\"inputs\":[{\"t\":\"col\",\"c\":2},{\"t\":\"col\",\"c\":0},{\"t\":\"col\",\"c\":1}]},{\"digest_col\":5,\"arity\":3,\"inputs\":[{\"t\":\"col\",\"c\":3},{\"t\":\"col\",\"c\":0},{\"t\":\"col\",\"c\":1}]}],\"ranges\":[]}"

def tamperedPathPublic (hash : List Int -> Int) : Assignment :=
  fun c => if c = pathCol 0 then PathTag.shareValue.code
    else publicOf hash nestedLayout c

def tamperedTrace (hash : List Int -> Int) : VmTrace :=
  { rows := [rowOf hash nestedLayout]
  , pub := tamperedPathPublic hash
  , tf := fun _ => [] }

/-- A one-cell `shareBody -> shareValue` public tamper is refused while all
honest row and hash-site data are retained. -/
theorem binder_side_tamper_refused (hash : List Int -> Int) :
    ¬ Satisfied2 hash nestedDescriptor (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (tamperedTrace hash) := by
  intro hsat
  have h := hsat.rowConstraints 0 (by simp [tamperedTrace])
    (.base (.piBinding .first (pathCol 0) (pathCol 0))) (by
      simp [nestedDescriptor, descriptor, nestedStep, descriptorAtDepth,
        publicPins, pathCol, traceWidth])
  have hmod : (10 : Int) ≡ 9 [ZMOD 2013265921] := by
    simpa [VmConstraint2.holdsAt, tamperedTrace, rowOf, nested_layout_exact,
      tamperedPathPublic, pathCol, publicOf, PathTag.code, envAt] using h
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hmod
  omega

/- Two genuinely different typed beta redexes. -/
def betaOne : LocalStep
    (Net.app (Net.lam (Net.var (.zero : Var [.nat] .nat))) (Net.lit 1))
    (Net.share (Net.lit 1) (Net.var (.zero : Var [.nat] .nat))) :=
  .beta (Net.var .zero) (Net.lit 1)

def betaTwo : LocalStep
    (Net.app (Net.lam (Net.var (.zero : Var [.nat] .nat))) (Net.lit 2))
    (Net.share (Net.lit 2) (Net.var (.zero : Var [.nat] .nat))) :=
  .beta (Net.var .zero) (Net.lit 2)

theorem distinct_typed_sources :
    (Net.app (Net.lam (Net.var (.zero : Var [.nat] .nat))) (Net.lit 1)) ≠
      (Net.app (Net.lam (Net.var (.zero : Var [.nat] .nat))) (Net.lit 2)) := by
  intro h
  have hlitHeq : HEq (Net.lit 1 : Net [] .nat) (Net.lit 2 : Net [] .nat) :=
    (Net.app.inj h).2.2
  have hlit : (Net.lit 1 : Net [] .nat) = Net.lit 2 := eq_of_heq hlitHeq
  have : (1 : Nat) = 2 := Net.lit.inj hlit
  omega

theorem layout_forgets_typed_endpoints : layout betaOne = layout betaTwo := by
  rfl

theorem receipt_backend_cannot_distinguish_typed_endpoints :
    stepReceipt betaOne = stepReceipt betaTwo := by
  rw [stepReceipt_eq_receiptOfLayout, stepReceipt_eq_receiptOfLayout,
    layout_forgets_typed_endpoints]

/-- Formal obstruction: no decoder from receipt layout can recover every exact
typed beta source.  A future full typed-net backend must add new statement
data rather than pretending the existing Boolean receipt contains it. -/
theorem no_exact_typed_source_decoder :
    ¬ (exists decode : Layout -> Net [] .nat,
      decode (layout betaOne) =
          Net.app (Net.lam (Net.var (.zero : Var [.nat] .nat))) (Net.lit 1) /\
      decode (layout betaTwo) =
          Net.app (Net.lam (Net.var (.zero : Var [.nat] .nat))) (Net.lit 2)) := by
  rintro ⟨decode, h1, h2⟩
  have hs :
      (Net.app (Net.lam (Net.var (.zero : Var [.nat] .nat))) (Net.lit 1) : Net [] .nat) =
      Net.app (Net.lam (Net.var (.zero : Var [.nat] .nat))) (Net.lit 2) := by
    rw [<- h1, <- h2, layout_forgets_typed_endpoints]
  exact distinct_typed_sources hs

end Reference

#assert_all_clean [
  rootCode_injective,
  pathWords_injective,
  layoutWords_injective,
  receiptOfLayout_checks,
  localCertOfLayout_injective,
  receiptOfLayout_injective,
  stepReceipt_eq_receiptOfLayout,
  max_live_depth_exact,
  endpointHashSites_within_live_rate,
  descriptor_shape_exact,
  cost_exact,
  traceOf_hashes,
  trace_complete,
  satisfying_root_exact,
  satisfying_path_exact,
  satisfying_layout_words_exact,
  satisfying_trace_binds_exact_receipt,
  satisfying_trace_relation_sound,
  satisfying_endpoint_commitments,
  beforeCommit_binds,
  Reference.nested_layout_exact,
  Reference.nested_cost_exact,
  Reference.binder_side_tamper_refused,
  Reference.distinct_typed_sources,
  Reference.layout_forgets_typed_endpoints,
  Reference.receipt_backend_cannot_distinguish_typed_endpoints,
  Reference.no_exact_typed_source_decoder
]

end Dregg2.Calculus.IntensionalCCCInteractionDescriptorIR2
