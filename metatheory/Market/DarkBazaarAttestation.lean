/-
# Market.DarkBazaarAttestation — the strongest honest Dark Bazaar attestation join

The clearing proof and the settlement receipt are different proof objects.  This
module gives their present exact meeting point without pretending that the
registered Cert-F public input already contains an order root or a price bucket.

The joined carrier is:

  committed `(book,K)` source
    → exact volume-argmax leakage `(p*,V*)`
    → source-compiled, registered market4 Cert-F statement with objective `V*`
    → exact two-leg fhEgg settlement receipt.

Every arrow is an equality in the structure.  In particular the source-to-Cert-F
compiler is explicit: the deployed market4 descriptor has one public input (the
objective), so output-only acceptance cannot manufacture this binding.

Privacy grades are also kept separate.  Tier 1 below means that the WORLD view
factors through `(p*,V*)`; the solver input is definitionally the plaintext book.
Tier 0 is a separately named distributed/no-viewer protocol obligation.

Pure.  This file specifies and proves the join; it does not claim that the
production source compiler or the Tier-0 distributed carrier is installed.
-/
import Market.MpcClearingSecurity
import Market.CertFDescriptor
import Market.FhEggLedgerBinding
import Dregg2.Tactics

namespace Market.DarkBazaarAttestation

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Exec
open Dregg2.Intent.Ring
open Market.CertFDescriptor
open Market.MpcClearingSecurity

set_option autoImplicit false

theorem crossingLeakage_ext {x y : CrossingLeakage}
    (hp : x.pStar = y.pStar) (hV : x.vStar = y.vStar) : x = y := by
  cases x
  cases y
  simp_all

/-! ## 1. The committed order-source carrier. -/

/-- Everything that determines the uniform-price clearing rule: the private book
and the public bucket domain.  Committing only the book while leaving `K`
unbound would permit two different output functions under one source identity. -/
structure OrderSourcePayload where
  book : OrderBook
  K : Nat
  deriving DecidableEq, Repr

/-- An ideal binding carrier for the batch commitment.  In a cryptographic
instantiation, `binding` is discharged by the commitment security reduction; it
is not inferred from digest equality by Lean. -/
structure OrderCommitmentCarrier where
  Digest : Type
  commit : OrderSourcePayload → Digest
  binding : Function.Injective commit

/-- A valid, nonempty-price-domain source and its exact commitment identity. -/
structure CommittedOrderSource (C : OrderCommitmentCarrier) where
  payload : OrderSourcePayload
  valid : OrdersValid payload.book
  K_pos : 0 < payload.K
  root : C.Digest
  root_eq : root = C.commit payload

theorem committed_source_eq_of_root_eq {C : OrderCommitmentCarrier}
    {x y : CommittedOrderSource C} (hroot : x.root = y.root) : x = y := by
  have hpayload : x.payload = y.payload := C.binding <| by
    calc
      C.commit x.payload = x.root := x.root_eq.symm
      _ = y.root := hroot
      _ = C.commit y.payload := y.root_eq
  cases x
  cases y
  simp_all

/-! ## 2. The exact registered Cert-F statement. -/

/-- The public statement carried by a Cert-F attestation.  Registration pins the
whole Lean-authored descriptor and its public program, rather than merely the
string name `"cert-f"`. -/
structure RegisteredCertFStatement where
  program : CertFProg
  descriptor : EffectVmDescriptor2
  publicObjective : Int
  program_registered : program = market4Prog
  descriptor_registered : descriptor = certFMarket4Descriptor

/-- An accepted trace for the registered market4 Cert-F wire.  `objective_binds`
connects the statement's only public scalar to the descriptor's objective column. -/
structure RegisteredCertFAttestation where
  statement : RegisteredCertFStatement
  hash : List Int → Int
  assignment : Assignment
  canonical : ∀ col, CanonCell (assignment col)
  accepted :
    Satisfied2 hash certFMarket4Descriptor m0 f0 []
      (constTrace market4Prog assignment)
  objective_binds :
    statement.publicObjective = assignment market4Prog.objCol

/-- Acceptance of the exact registered wire yields the repository's real integer
`Market.Certified` predicate, and its public objective is the exact integer
objective of that certificate. -/
theorem registered_certF_sound (cert : RegisteredCertFAttestation) :
    Market.Certified (integerFlowLP market4Prog)
      (integerFlow market4Prog cert.assignment)
      (integerPotential market4Prog cert.assignment)
      (integerSlack market4Prog cert.assignment) ∧
    cert.statement.publicObjective = objOf market4Prog cert.assignment := by
  have hsound := market4_deployed_emit_Certified_sound cert.canonical cert.accepted
  exact ⟨hsound.1, cert.objective_binds.trans hsound.2⟩

/-- The registered statement is genuinely the byte-pinned market4 program and has
exactly one public input.  Consequently neither an order root nor `p*` is already
present in this descriptor statement. -/
theorem registered_certF_statement_shape (s : RegisteredCertFStatement) :
    s.program = market4Prog ∧
    s.descriptor = certFMarket4Descriptor ∧
    s.descriptor.piCount = 1 := by
  refine ⟨s.program_registered, s.descriptor_registered, ?_⟩
  rw [s.descriptor_registered]
  decide

/-! ## 3. Exact settlement receipts. -/

/-- The data-bearing settlement receipt.  It deliberately contains no proof
field: `ExactSettlementReceipt` below is the independently checkable relation. -/
structure SettlementReceipt (C : OrderCommitmentCarrier) where
  sourceRoot : C.Digest
  pStar : Nat
  vStar : Int
  nodes : List MatchNode
  pre : RecordKernelState
  post : RecordKernelState

theorem settlementReceipt_ext {C : OrderCommitmentCarrier}
    {x y : SettlementReceipt C}
    (hroot : x.sourceRoot = y.sourceRoot)
    (hp : x.pStar = y.pStar) (hV : x.vStar = y.vStar)
    (hnodes : x.nodes = y.nodes) (hpre : x.pre = y.pre)
    (hpost : x.post = y.post) : x = y := by
  cases x
  cases y
  simp_all

/-- Exact receipt relation: the same source root and `(p*,V*)`, lowered to the
canonical fhEgg node list and its exact pre/post states. -/
def ExactSettlementReceipt {C : OrderCommitmentCarrier}
    (source : CommittedOrderSource C) (out : CrossingLeakage)
    (receipt : SettlementReceipt C) : Prop :=
  receipt.sourceRoot = source.root ∧
  receipt.pStar = out.pStar ∧
  receipt.vStar = out.vStar ∧
  receipt.nodes = fhEggMatchNodes out.pStar out.vStar ∧
  receipt.pre = fhEggSettlePre out.pStar out.vStar ∧
  receipt.post = fhEggSettlePost out.pStar out.vStar

/-- Exact receipt data cannot name a spurious state transition: positivity plus
the receipt relation reconstructs the verified `settleRing` execution. -/
theorem exact_settlement_receipt_settles {C : OrderCommitmentCarrier}
    {source : CommittedOrderSource C} {out : CrossingLeakage}
    {receipt : SettlementReceipt C}
    (hexact : ExactSettlementReceipt source out receipt)
    (hp : 0 < out.pStar) (hV : 0 < out.vStar) :
    settleRing receipt.pre (settlementsOf receipt.nodes) = some receipt.post := by
  rcases hexact with ⟨_, _, _, hnodes, hpre, hpost⟩
  rw [hnodes, hpre, hpost]
  exact fhEggMatchNodes_settle out.pStar out.vStar hp hV

/-! ## 4. The honest joined envelope. -/

/-- The explicit source→Cert-F compiler carrier.  Its injectivity prevents a
constant compiler from laundering unrelated sources into one registered program.
The current theorem consumes this carrier; installing it for production orders is
a separate implementation/refinement obligation. -/
structure OrderToCertFCompiler where
  compile : OrderSourcePayload → CertFProg
  binding : Function.Injective compile

/-- One honest end-to-end Dark Bazaar attestation.  The fields are the exact welds
which the presently separate proof objects do not supply by themselves. -/
structure EndToEndAttestation
    (C : OrderCommitmentCarrier) (compiler : OrderToCertFCompiler) where
  source : CommittedOrderSource C
  clearing : MpcClearing
  clearing_book : clearing.bk = source.payload.book
  clearing_K : clearing.K = source.payload.K
  output : CrossingLeakage
  output_exact : output = clearing.leakage
  certF : RegisteredCertFAttestation
  certF_source : certF.statement.program = compiler.compile source.payload
  certF_volume : certF.statement.publicObjective = output.vStar
  price_pos : 0 < output.pStar
  volume_pos : 0 < output.vStar
  receipt : SettlementReceipt C
  receipt_exact : ExactSettlementReceipt source output receipt

/-- Tier-1 public hiding: the WORLD-visible transcript factors through only
`(p*,V*)` and the public circuit shape `(K,b)`.  This says nothing about hiding
the plaintext from the solver.

⚠ This used to read `mpcSim att.clearing.K att.clearing.maskedLen att.output` —
feeding the simulator the attestation's own transcript length, which was a free
field.  The simulator now derives every size from `(K,b)`, so the statement no
longer supplies the number whose book-independence it is asserting. -/
def Tier1WorldHiding {C : OrderCommitmentCarrier} {compiler : OrderToCertFCompiler}
    (att : EndToEndAttestation C compiler) : Prop :=
  att.clearing.mpcView =
    mpcSim att.clearing.K att.clearing.b att.output

/-- At Tier 1 the solver input is the plaintext book, stated without euphemism. -/
def tier1SolverInput {C : OrderCommitmentCarrier} {compiler : OrderToCertFCompiler}
    (att : EndToEndAttestation C compiler) : OrderBook :=
  att.clearing.bk

theorem tier1_world_hiding {C : OrderCommitmentCarrier}
    {compiler : OrderToCertFCompiler} (att : EndToEndAttestation C compiler) :
    Tier1WorldHiding att := by
  unfold Tier1WorldHiding
  rw [att.clearing.reveal_only, att.output_exact]

theorem tier1_solver_sees_source_book {C : OrderCommitmentCarrier}
    {compiler : OrderToCertFCompiler} (att : EndToEndAttestation C compiler) :
    tier1SolverInput att = att.source.payload.book :=
  att.clearing_book

/-- **The strongest honest end-to-end join now.**  One accepted envelope binds:

* the committed source payload;
* the actual volume-argmax `(p*,V*)` and its optimality theorem;
* the exact registered Cert-F program, certificate, and public objective `V*`;
* the exact canonical receipt and its real `settleRing` execution;
* the Tier-1 world-view simulator.

The compiler and commitment binding hypotheses remain visible in the carriers. -/
theorem honest_end_to_end_join {C : OrderCommitmentCarrier}
    {compiler : OrderToCertFCompiler} (att : EndToEndAttestation C compiler) :
    att.source.root = C.commit att.source.payload ∧
    att.output =
      ⟨crossing att.source.payload.book att.source.payload.K,
        clearedVolume att.source.payload.book att.source.payload.K⟩ ∧
    (∀ q < att.source.payload.K,
      execVol att.source.payload.book q ≤ att.output.vStar) ∧
    Tier1WorldHiding att ∧
    att.certF.statement.program = compiler.compile att.source.payload ∧
    att.certF.statement.program = market4Prog ∧
    Market.Certified (integerFlowLP market4Prog)
      (integerFlow market4Prog att.certF.assignment)
      (integerPotential market4Prog att.certF.assignment)
      (integerSlack market4Prog att.certF.assignment) ∧
    att.certF.statement.publicObjective =
      objOf market4Prog att.certF.assignment ∧
    att.certF.statement.publicObjective = att.output.vStar ∧
    ExactSettlementReceipt att.source att.output att.receipt ∧
    settleRing att.receipt.pre (settlementsOf att.receipt.nodes) =
      some att.receipt.post := by
  have hout : att.output =
      ⟨crossing att.source.payload.book att.source.payload.K,
        clearedVolume att.source.payload.book att.source.payload.K⟩ := by
    rw [att.output_exact]
    apply crossingLeakage_ext
    · exact congrArg (fun bk => crossing bk att.clearing.K) att.clearing_book |>.trans <| by
        rw [att.clearing_K]
    · exact congrArg (fun bk => clearedVolume bk att.clearing.K) att.clearing_book |>.trans <| by
        rw [att.clearing_K]
  have hcert := registered_certF_sound att.certF
  refine ⟨att.source.root_eq, hout, ?_, tier1_world_hiding att,
    att.certF_source, att.certF.statement.program_registered,
    hcert.1, hcert.2, att.certF_volume, att.receipt_exact, ?_⟩
  · intro q hq
    have hq' : q < att.clearing.K := by simpa [att.clearing_K] using hq
    have hopt := att.clearing.vStar_optimal hq'
    rw [att.output_exact]
    simpa [att.clearing_book, MpcClearing.leakage] using hopt
  · exact exact_settlement_receipt_settles att.receipt_exact
      att.price_pos att.volume_pos

/-- No-spurious-settlement corollary, exposing the exact data equalities as well
as execution. -/
theorem no_spurious_settlement {C : OrderCommitmentCarrier}
    {compiler : OrderToCertFCompiler} (att : EndToEndAttestation C compiler) :
    att.receipt.sourceRoot = C.commit att.source.payload ∧
    att.receipt.nodes = fhEggMatchNodes att.output.pStar att.output.vStar ∧
    att.receipt.pre = fhEggSettlePre att.output.pStar att.output.vStar ∧
    att.receipt.post = fhEggSettlePost att.output.pStar att.output.vStar ∧
    settleRing att.receipt.pre (settlementsOf att.receipt.nodes) =
      some att.receipt.post := by
  rcases att.receipt_exact with ⟨hroot, _, _, hnodes, hpre, hpost⟩
  exact ⟨hroot.trans att.source.root_eq, hnodes, hpre, hpost,
    exact_settlement_receipt_settles att.receipt_exact att.price_pos att.volume_pos⟩

/-- Binding of the committed source propagates through deterministic clearing to
the public output and exact receipt. -/
theorem end_to_end_binding {C : OrderCommitmentCarrier}
    {compiler : OrderToCertFCompiler}
    (a b : EndToEndAttestation C compiler)
    (hroot : a.source.root = b.source.root) :
    a.source = b.source ∧
    a.output = b.output ∧
    a.certF.statement.publicObjective = b.certF.statement.publicObjective ∧
    a.receipt = b.receipt := by
  have hsource : a.source = b.source := committed_source_eq_of_root_eq hroot
  have hbook : a.clearing.bk = b.clearing.bk := by
    rw [a.clearing_book, b.clearing_book, hsource]
  have hK : a.clearing.K = b.clearing.K := by
    rw [a.clearing_K, b.clearing_K, hsource]
  have hout : a.output = b.output := by
    rw [a.output_exact, b.output_exact]
    apply crossingLeakage_ext
    · unfold MpcClearing.leakage MpcClearing.pStar
      rw [hbook, hK]
    · unfold MpcClearing.leakage MpcClearing.vStar
      rw [hbook, hK]
  have hobj : a.certF.statement.publicObjective =
      b.certF.statement.publicObjective := by
    rw [a.certF_volume, b.certF_volume, hout]
  have hreceipt : a.receipt = b.receipt := by
    rcases a.receipt_exact with ⟨aroot, ap, av, anodes, apre, apost⟩
    rcases b.receipt_exact with ⟨broot, bp, bv, bnodes, bpre, bpost⟩
    apply settlementReceipt_ext
    · exact aroot.trans (congrArg CommittedOrderSource.root hsource |>.trans broot.symm)
    · exact ap.trans (congrArg CrossingLeakage.pStar hout |>.trans bp.symm)
    · exact av.trans (congrArg CrossingLeakage.vStar hout |>.trans bv.symm)
    · rw [anodes, bnodes, hout]
    · rw [apre, bpre, hout]
    · rw [apost, bpost, hout]
  exact ⟨hsource, hout, hobj, hreceipt⟩

/-! ## 5. RED: output-only attestation does not bind source orders. -/

structure OutputOnlyAttestation where
  output : CrossingLeakage
  deriving DecidableEq, Repr

def OutputOnlyAttestation.Accepts (att : OutputOnlyAttestation)
    (book : OrderBook) (K : Nat) : Prop :=
  att.output = ⟨crossing book K, clearedVolume book K⟩

def sameOutputAttestation : OutputOnlyAttestation := ⟨⟨1, 8⟩⟩

/-- Two genuinely different source books have the exact same output-only
attestation. -/
theorem output_only_collision :
    bookA ≠ bookB ∧
    sameOutputAttestation.Accepts bookA 3 ∧
    sameOutputAttestation.Accepts bookB 3 := by
  refine ⟨by decide, ?_, ?_⟩
  · simp [OutputOnlyAttestation.Accepts, sameOutputAttestation, bookA,
      workBook_crossing, workBook_clearedVolume]
  · simp [OutputOnlyAttestation.Accepts, sameOutputAttestation,
      bookB_crossing, bookB_clearedVolume]

/-- **RED theorem.**  No rule which accepts solely by equality of `(p*,V*)` can
claim source-order binding. -/
theorem output_only_attestation_does_not_bind_source :
    ¬ ∀ (att : OutputOnlyAttestation) (book₁ book₂ : OrderBook) (K : Nat),
      att.Accepts book₁ K → att.Accepts book₂ K → book₁ = book₂ := by
  intro hbind
  have h := hbind sameOutputAttestation bookA bookB 3
    output_only_collision.2.1 output_only_collision.2.2
  exact output_only_collision.1 h

/-! ## 6. Composite private-proof receipt boundary. -/

/-- The two typed input-reference variants in the canonical fhEgg claim. -/
inductive CompositePrivateInput where
  | ciphertext (digest : Nat)
  | commitment (digest : Nat)
  deriving DecidableEq, Repr

/-- The claim fields at the current composite-receipt boundary.  The private
proof statement binds `orderRoot` and `output`; the BFV ciphertext digests are
listed alongside that statement, but are not yet inputs to the proof relation. -/
structure CompositePrivateClaim where
  orderRoot : Nat
  output : CrossingLeakage
  bfvIdentity : Nat
  orderedInputs : List CompositePrivateInput
  deriving DecidableEq, Repr

/-- The two independently checked authorization facts and the public statement
actually verified by the private clearing proof. -/
structure CompositePrivateReceipt where
  authenticatedQuorum : Bool
  privateProofVerified : Bool
  proofRoot : Nat
  proofOutput : CrossingLeakage
  policyBfvIdentity : Nat
  deriving DecidableEq, Repr

/-- Exact fixed-family claim layout mirrored by the Rust verifier: four ordered
ciphertext rows and one terminal commitment to the proved root. -/
def CompositePrivateClaim.CanonicalInputShape
    (claim : CompositePrivateClaim) : Prop :=
  ∃ c₀ c₁ c₂ c₃,
    claim.orderedInputs =
      [.ciphertext c₀, .ciphertext c₁, .ciphertext c₂, .ciphertext c₃,
       .commitment claim.orderRoot]

/-- Exact current acceptance rule: neither authorization alone is sufficient,
the verified private-proof statement must equal the claim root and output, the
BFV key domain is relying-party pinned, and the input vector has the exact
fixed-family shape. -/
def CompositePrivateReceipt.Accepts (receipt : CompositePrivateReceipt)
    (claim : CompositePrivateClaim) : Prop :=
  receipt.authenticatedQuorum = true ∧
  receipt.privateProofVerified = true ∧
  receipt.proofRoot = claim.orderRoot ∧
  receipt.proofOutput = claim.output ∧
  claim.bfvIdentity = receipt.policyBfvIdentity ∧
  claim.CanonicalInputShape

/-- Acceptance exposes both independent checks and both statement bindings. -/
theorem composite_receipt_acceptance_requires_both_and_binds_statement
    {receipt : CompositePrivateReceipt} {claim : CompositePrivateClaim}
    (h : receipt.Accepts claim) :
    receipt.authenticatedQuorum = true ∧
    receipt.privateProofVerified = true ∧
    receipt.proofRoot = claim.orderRoot ∧
    receipt.proofOutput = claim.output ∧
    claim.bfvIdentity = receipt.policyBfvIdentity ∧
    claim.CanonicalInputShape :=
  h

def compositeClaimA : CompositePrivateClaim :=
  { orderRoot := 41
    output := ⟨1, 8⟩
    bfvIdentity := 17
    orderedInputs :=
      [.ciphertext 101, .ciphertext 102, .ciphertext 103, .ciphertext 104,
       .commitment 41] }

def compositeClaimB : CompositePrivateClaim :=
  { orderRoot := 41
    output := ⟨1, 8⟩
    bfvIdentity := 17
    orderedInputs :=
      [.ciphertext 201, .ciphertext 202, .ciphertext 203, .ciphertext 204,
       .commitment 41] }

def compositeReceipt : CompositePrivateReceipt :=
  { authenticatedQuorum := true
    privateProofVerified := true
    proofRoot := 41
    proofOutput := ⟨1, 8⟩
    policyBfvIdentity := 17 }

/-- Concrete residual seam: two claims with different separately listed BFV
ciphertext digests are accepted by the same authenticated private proof. -/
theorem composite_receipt_bfv_digest_collision :
    compositeClaimA.orderedInputs ≠ compositeClaimB.orderedInputs ∧
    compositeReceipt.Accepts compositeClaimA ∧
    compositeReceipt.Accepts compositeClaimB := by
  simp [CompositePrivateReceipt.Accepts, compositeClaimA, compositeClaimB,
    compositeReceipt, CompositePrivateClaim.CanonicalInputShape]

/-- **RED theorem.**  The current composite rule authenticates the quorum and
private proof, but cannot claim that acceptance binds the separately listed BFV
ciphertext digests. -/
theorem composite_receipt_does_not_bind_bfv_ciphertext_digests :
    ¬ ∀ (receipt : CompositePrivateReceipt)
        (claim₁ claim₂ : CompositePrivateClaim),
      receipt.Accepts claim₁ → receipt.Accepts claim₂ →
      claim₁.orderedInputs = claim₂.orderedInputs := by
  intro hbind
  have h := hbind compositeReceipt compositeClaimA compositeClaimB
    composite_receipt_bfv_digest_collision.2.1
    composite_receipt_bfv_digest_collision.2.2
  exact composite_receipt_bfv_digest_collision.1 h

/-! ## 7. Tier-1/Tier-0 separation. -/

/-- An abstract distributed carrier for the still-separate Tier-0 protocol. -/
structure Tier0DistributedProtocol (C : OrderCommitmentCarrier) where
  Ciphertext : Type
  Proof : Type
  DistributedView : Type
  encrypt : OrderSourcePayload → Ciphertext
  view : Ciphertext → DistributedView
  simulate : CrossingLeakage → DistributedView
  verify : C.Digest → CrossingLeakage → RegisteredCertFStatement → Proof → Bool

/-- The precise Tier-0 residual: every distributed view is output-simulable, and
every accepted distributed proof extracts one committed source whose exact
clearing output and registered statement it binds.  Tier-1 world hiding proves
neither clause for such a protocol. -/
def Tier0NoViewerDistributedAttestationResidual
    (C : OrderCommitmentCarrier) (compiler : OrderToCertFCompiler)
    (P : Tier0DistributedProtocol C) : Prop :=
  (∀ source : CommittedOrderSource C,
      P.view (P.encrypt source.payload) =
        P.simulate
          ⟨crossing source.payload.book source.payload.K,
            clearedVolume source.payload.book source.payload.K⟩) ∧
  (∀ root out statement proof,
      P.verify root out statement proof = true →
      ∃ source : CommittedOrderSource C,
        source.root = root ∧
        out =
          ⟨crossing source.payload.book source.payload.K,
            clearedVolume source.payload.book source.payload.K⟩ ∧
        statement.program = compiler.compile source.payload ∧
        statement.publicObjective = out.vStar)

/-- Concrete Tier-1 separation tooth: the public views coincide while the two
plaintext solver inputs are different.  Public-view hiding is therefore not a
no-viewer theorem about the solver.

⚠ `mcA` and `mcB` used to each carry `maskedLen := 144`, so this tooth's
`same_leakage_indistinguishable … rfl` discharged transcript-length agreement by
having hand-written the same number twice — and `144` is a length the deployed
circuit cannot emit at `K = 3` for any bit width
(`MpcClearingSecurity.maskedOpens_three_never_144`).  Both now carry the public
shape `(K,b) = (3,8)` and the agreement is derived. -/
def mcB : MpcClearing :=
  { bk := bookB
    hvalid := bookB_valid
    K := 3
    hK := by norm_num
    b := 8
    hb := by norm_num
    hfit := by unfold MpcClearingSecurity.CurvesFit bookB; decide
    ρ := 2
    hρ := by norm_num }

theorem tier1_world_hiding_does_not_hide_solver_input :
    mcA.mpcView = mcB.mpcView ∧ mcA.bk ≠ mcB.bk := by
  constructor
  · apply MpcClearing.same_leakage_indistinguishable mcA mcB rfl rfl
    apply crossingLeakage_ext <;>
      simp [MpcClearing.leakage, MpcClearing.pStar, MpcClearing.vStar,
        mcA, mcB, bookA, workBook_crossing, workBook_clearedVolume,
        bookB_crossing, bookB_clearedVolume]
  · decide

#guard certFMarket4Descriptor.piCount == 1
#guard (crossing bookA 3, clearedVolume bookA 3) == (1, 8)
#guard (crossing bookB 3, clearedVolume bookB 3) == (1, 8)

#assert_all_clean [
  Market.DarkBazaarAttestation.committed_source_eq_of_root_eq,
  Market.DarkBazaarAttestation.registered_certF_sound,
  Market.DarkBazaarAttestation.registered_certF_statement_shape,
  Market.DarkBazaarAttestation.exact_settlement_receipt_settles,
  Market.DarkBazaarAttestation.tier1_world_hiding,
  Market.DarkBazaarAttestation.tier1_solver_sees_source_book,
  Market.DarkBazaarAttestation.honest_end_to_end_join,
  Market.DarkBazaarAttestation.no_spurious_settlement,
  Market.DarkBazaarAttestation.end_to_end_binding,
  Market.DarkBazaarAttestation.output_only_collision,
  Market.DarkBazaarAttestation.output_only_attestation_does_not_bind_source,
  Market.DarkBazaarAttestation.composite_receipt_acceptance_requires_both_and_binds_statement,
  Market.DarkBazaarAttestation.composite_receipt_bfv_digest_collision,
  Market.DarkBazaarAttestation.composite_receipt_does_not_bind_bfv_ciphertext_digests,
  Market.DarkBazaarAttestation.tier1_world_hiding_does_not_hide_solver_input]

end Market.DarkBazaarAttestation
