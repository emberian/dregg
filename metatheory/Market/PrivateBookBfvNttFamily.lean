/-
# Market.PrivateBookBfvNttFamily -- one exact NTT family target

`PrivateBookBfvSliceDescriptor` proves one of the 98,304 production BFV
coefficient equations with a 4,096-term schoolbook accumulator.  Instantiating
that descriptor literally would therefore commit 98,304 independent proofs and
402,653,184 accumulator rows.  This file fixes the next Lean-first lowering:

* one per-session public-key NTT certificate (six transforms), reusable by all
  private books under that key;
* one per-book family trace containing twelve shared-`u` forward transforms,
  twenty-four ciphertext inverse transforms, all 98,304 pointwise products, and
  all 98,304 terminal error/message/quotient equations; and
* one recursively folded wire proof binding the key certificate, the existing
  private-book proof, and the family trace.

The row schedule is deliberately not a random projection.  Every RNS row and
every output coefficient occurs exactly once at the pointwise and terminal
boundaries.  The live per-book schedule is 1,032,192 rows and pads to 2^20,
versus 402,653,184 schoolbook term rows (exactly 384 times the padded family
height).  Public-key preprocessing is another 147,456 live rows, padded to
2^18, but is paid once per key rather than once per private book.

This module is isolated from the Rust descriptor registry while the 14-bit limb
butterfly is lowered.  It supplies the exact shape, the semantic contract back
to `WgpuBfvNttSpec.negacyclicMul`, and an executable two-production-modulus,
eight-coefficient odd-NTT gate with positive and mutation teeth.  A descriptor
fingerprint will be added only after the emitted AIR and Rust witness builder
exist; JSON identity is not used here as evidence of semantic refinement.
-/
import Market.PrivateBookBfvBindingAir
import Dregg2.Crypto.WgpuBfvNttSpec
import Dregg2.Tactics

namespace Market.PrivateBookBfvNttFamily

open Dregg2.Crypto.WgpuBfvNttSpec
open Market.PrivateBookBfvBindingAir
open Finset

set_option autoImplicit false

/-! ## 1. Production family geometry -/

def ORDER_COUNT : Nat := 4
def CIPHER_POLY_COUNT : Nat := 2
def RNS_MODULUS_COUNT : Nat := 3
def DEGREE : Nat := deployedDegree
def LOG_DEGREE : Nat := 12

/-- Number of exact public ciphertext coefficient equations. -/
def EQUATION_COUNT : Nat :=
  ORDER_COUNT * CIPHER_POLY_COUNT * RNS_MODULUS_COUNT * DEGREE

/-- The old slice plan spends one full schoolbook row per secret coefficient
for every output equation. -/
def SCHOOLBOOK_FAMILY_ROWS : Nat := EQUATION_COUNT * DEGREE

/-- One radix-2 transform has `N/2` butterflies at each of `log₂ N` stages. -/
def BUTTERFLIES_PER_TRANSFORM : Nat := (DEGREE / 2) * LOG_DEGREE

/-- `u` is shared between the two ciphertext polynomials: four orders times
three RNS moduli, not twenty-four duplicate forward transforms. -/
def FORWARD_U_TRANSFORMS : Nat := ORDER_COUNT * RNS_MODULUS_COUNT

/-- Each `(order, ciphertext-poly, modulus)` product needs one inverse transform. -/
def INVERSE_PRODUCT_TRANSFORMS : Nat :=
  ORDER_COUNT * CIPHER_POLY_COUNT * RNS_MODULUS_COUNT

/-- Six public-key transforms are certified once per collective key. -/
def PUBLIC_KEY_TRANSFORMS : Nat := CIPHER_POLY_COUNT * RNS_MODULUS_COUNT

def FORWARD_U_ROWS : Nat := FORWARD_U_TRANSFORMS * BUTTERFLIES_PER_TRANSFORM
def INVERSE_PRODUCT_ROWS : Nat :=
  INVERSE_PRODUCT_TRANSFORMS * BUTTERFLIES_PER_TRANSFORM
def PUBLIC_KEY_CERT_ROWS : Nat := PUBLIC_KEY_TRANSFORMS * BUTTERFLIES_PER_TRANSFORM

/-- One exact modular multiplication row for every spectral coefficient. -/
def POINTWISE_ROWS : Nat := EQUATION_COUNT

/-- One terminal row discharges two final-butterfly outputs.  Both outputs get
their own error/message/canonical-ciphertext/quotient equations. -/
def TERMINAL_ROWS : Nat := EQUATION_COUNT / 2

def LIVE_FAMILY_ROWS : Nat :=
  FORWARD_U_ROWS + POINTWISE_ROWS + INVERSE_PRODUCT_ROWS + TERMINAL_ROWS

/-- One power-of-two HidingFRI matrix contains the complete per-book family. -/
def FAMILY_PADDED_ROWS : Nat := 2 ^ 20

/-- The reusable key-certificate matrix. -/
def KEY_CERT_PADDED_ROWS : Nat := 2 ^ 18

/-- Proposed v1 narrow NTT row.  Its exact inventory is pinned below: eight
schedule/routing columns, six three-limb residues, one three-limb quotient,
two reduction flags, eleven exact integer carries, four permutation-bus tags,
and two reserved terminal selectors.  Limbs use radix 2^14 so every individual
three-term convolution expression stays below BabyBear rather than relying on
field wrap. -/
def NTT_TRACE_WIDTH : Nat := 8 + 6 * 3 + 3 + 2 + 11 + 4 + 2

/-- Existing private-book matrix, committed once rather than copied through all
NTT rows.  A lookup/permutation bus carries the four private order codes into
the terminal rows while the eight-lane root remains the public join. -/
def PRIVATE_BOOK_TRACE_WIDTH : Nat := 181
def PRIVATE_BOOK_REAL_ROWS : Nat := 1

/-- The external object is one recursive envelope.  Internally it opens one
per-book NTT batch plus the stable key certificate; it is not a list of 98,304
independent coefficient proofs. -/
def EXTERNAL_PROOF_COUNT : Nat := 1
def FAMILY_LEAF_PROOF_COUNT : Nat := 1
def KEY_CERT_PROOF_COUNT_PER_KEY : Nat := 1

theorem production_geometry :
    EQUATION_COUNT = 98304 ∧
    SCHOOLBOOK_FAMILY_ROWS = 402653184 ∧
    BUTTERFLIES_PER_TRANSFORM = 24576 ∧
    FORWARD_U_ROWS = 294912 ∧
    POINTWISE_ROWS = 98304 ∧
    INVERSE_PRODUCT_ROWS = 589824 ∧
    TERMINAL_ROWS = 49152 ∧
    LIVE_FAMILY_ROWS = 1032192 ∧
    FAMILY_PADDED_ROWS = 1048576 ∧
    PUBLIC_KEY_CERT_ROWS = 147456 ∧
    KEY_CERT_PADDED_ROWS = 262144 ∧
    NTT_TRACE_WIDTH = 48 := by
  norm_num [EQUATION_COUNT, SCHOOLBOOK_FAMILY_ROWS, BUTTERFLIES_PER_TRANSFORM,
    FORWARD_U_ROWS, POINTWISE_ROWS, INVERSE_PRODUCT_ROWS, TERMINAL_ROWS,
    LIVE_FAMILY_ROWS, FAMILY_PADDED_ROWS, PUBLIC_KEY_CERT_ROWS,
    KEY_CERT_PADDED_ROWS, NTT_TRACE_WIDTH, FORWARD_U_TRANSFORMS,
    INVERSE_PRODUCT_TRANSFORMS, PUBLIC_KEY_TRANSFORMS, ORDER_COUNT,
    CIPHER_POLY_COUNT, RNS_MODULUS_COUNT, DEGREE, LOG_DEGREE, deployedDegree]

/-- Only 1.5625% of the power-of-two family matrix is padding. -/
theorem family_padding_rows :
    FAMILY_PADDED_ROWS - LIVE_FAMILY_ROWS = 16384 := by
  norm_num [FAMILY_PADDED_ROWS, LIVE_FAMILY_ROWS, FORWARD_U_ROWS,
    FORWARD_U_TRANSFORMS, POINTWISE_ROWS, INVERSE_PRODUCT_ROWS,
    INVERSE_PRODUCT_TRANSFORMS, TERMINAL_ROWS, EQUATION_COUNT,
    BUTTERFLIES_PER_TRANSFORM, ORDER_COUNT, CIPHER_POLY_COUNT,
    RNS_MODULUS_COUNT, DEGREE, LOG_DEGREE, deployedDegree]

/-- Exact padded-row compression, before the reusable key certificate is
amortized: 98,304 schoolbook slice proofs become one 2^20 family matrix and its
row budget is 384 times smaller. -/
theorem padded_family_compression :
    SCHOOLBOOK_FAMILY_ROWS = 384 * FAMILY_PADDED_ROWS := by
  norm_num [SCHOOLBOOK_FAMILY_ROWS, EQUATION_COUNT, FAMILY_PADDED_ROWS,
    ORDER_COUNT, CIPHER_POLY_COUNT, RNS_MODULUS_COUNT, DEGREE, deployedDegree]

/-! ## 2. Exact spectral semantics

The odd powers of a primitive `2N`-th root are precisely the evaluation points
for `R_q[X]/(X^N+1)`.  These definitions are executable and intentionally use
`ZMod q`, so there is no lossy BabyBear embedding in the semantic layer.
-/

/-- Evaluate a power-basis polynomial at the `j`th odd power of `psi`. -/
def oddNtt {q n : Nat} (psi : ZMod q) (a : Poly q n) : Poly q n := fun j =>
  ∑ k : Fin n, a k * psi ^ ((2 * j.val + 1) * k.val)

/-- Interpolate from the odd evaluation domain.  The production root contract
must ensure `n` is invertible and `psi` has exact order `2n`; the concrete gate
below checks the resulting equality rather than assuming it. -/
def oddIntt {q n : Nat} (psi : ZMod q) (a : Poly q n) : Poly q n := fun k =>
  (n : ZMod q)⁻¹ *
    ∑ j : Fin n, a j * (psi⁻¹) ^ ((2 * j.val + 1) * k.val)

/-- Forward/pointwise/inverse multiplication on the odd domain. -/
def oddNttMul {q n : Nat} (psi : ZMod q) (a b : Poly q n) : Poly q n :=
  oddIntt psi (fun j => oddNtt psi a j * oddNtt psi b j)

/-! The concrete `2N`-th roots for the three deployed 4,096-degree rows.  These
are ordinary natural representatives in their respective `ZMod` fields.  The
three executable teeth prove `psi^4096 = -1`; the roots are therefore not
metadata accepted on trust. -/

def DEPLOYED_PSI0 : Nat := 5546991020
def DEPLOYED_PSI1 : Nat := 41019061109
def DEPLOYED_PSI2 : Nat := 93693982103

set_option maxRecDepth 100000 in
theorem deployed_psi0_negacyclic_root :
    (DEPLOYED_PSI0 : ZMod 68719403009) ^ deployedDegree = -1 := by
  decide

set_option maxRecDepth 100000 in
theorem deployed_psi1_negacyclic_root :
    (DEPLOYED_PSI1 : ZMod 68719230977) ^ deployedDegree = -1 := by
  decide

set_option maxRecDepth 100000 in
theorem deployed_psi2_negacyclic_root :
    (DEPLOYED_PSI2 : ZMod 137438822401) ^ deployedDegree = -1 := by
  decide

/-- The per-key certificate contains the complete odd-domain transform of both
public-key polynomials in all three RNS rows. -/
structure PublicKeyCertificate where
  spectrum : CipherPolyIx → DeployedRns

/-- Exact certificate relation.  The emitted key-certificate AIR must prove
this relation from the full canonical power-basis key before its spectrum root
may be reused by a per-book family proof. -/
def PublicKeyCertificate.Exact
    (psi : (row : ModulusIx) → ZMod (deployedModulus row))
    (publicKey : CipherPolyIx → WireRns)
    (certificate : PublicKeyCertificate) : Prop :=
  ∀ poly row frequency,
    certificate.spectrum poly row frequency =
      oddNtt (psi row) ((publicKey poly).decode row) frequency

/-- The NTT family witness exposes each stage boundary semantically.  The AIR
lowering routes these values through one permutation bus; this structure fixes
what that bus is obliged to mean. -/
structure SpectralTrace where
  uSpectrum : OrderIx → DeployedRns
  pointwise : OrderIx → CipherPolyIx → DeployedRns
  product : OrderIx → CipherPolyIx → DeployedRns

/-- Complete spectral-stage gates before the terminal BFV quotient equations. -/
structure SpectralTrace.Exact
    (psi : (row : ModulusIx) → ZMod (deployedModulus row))
    (publicKey : CipherPolyIx → WireRns)
    (u : OrderIx → CoeffIx → Int)
    (key : PublicKeyCertificate)
    (trace : SpectralTrace) : Prop where
  keyGate : key.Exact psi publicKey
  uForward : ∀ order row frequency,
    trace.uSpectrum order row frequency =
      oddNtt (psi row) (liftSigned (u order) row) frequency
  pointwiseGate : ∀ order poly row frequency,
    trace.pointwise order poly row frequency =
      trace.uSpectrum order row frequency * key.spectrum poly row frequency
  inverseGate : ∀ order poly row coefficient,
    trace.product order poly row coefficient =
      oddIntt (psi row) (trace.pointwise order poly row) coefficient

/-- The four staged relations compose to the exact odd-NTT implementation;
the public-key spectrum cannot float free of the canonical power-basis key. -/
theorem SpectralTrace.Exact.product_eq_oddNttMul
    {psi : (row : ModulusIx) → ZMod (deployedModulus row)}
    {publicKey : CipherPolyIx → WireRns}
    {u : OrderIx → CoeffIx → Int}
    {key : PublicKeyCertificate} {trace : SpectralTrace}
    (h : trace.Exact psi publicKey u key)
    (order : OrderIx) (poly : CipherPolyIx) (row : ModulusIx)
    (coefficient : CoeffIx) :
    trace.product order poly row coefficient =
      oddNttMul (psi row) (liftSigned (u order) row)
        ((publicKey poly).decode row) coefficient := by
  rw [h.inverseGate order poly row coefficient]
  unfold oddNttMul
  congr 2
  funext frequency
  rw [h.pointwiseGate order poly row frequency,
    h.uForward order row frequency, h.keyGate poly row frequency]

/-- A valid certificate is functional for a fixed key and root table.  This is
the semantic substitution tooth the future spectrum-root mutation test lowers. -/
theorem publicKeyCertificate_functional
    {psi : (row : ModulusIx) → ZMod (deployedModulus row)}
    {publicKey : CipherPolyIx → WireRns}
    {left right : PublicKeyCertificate}
    (hl : left.Exact psi publicKey) (hr : right.Exact psi publicKey) :
    left = right := by
  cases left with
  | mk leftSpectrum =>
    cases right with
    | mk rightSpectrum =>
      congr
      funext poly row frequency
      exact (hl poly row frequency).trans (hr poly row frequency).symm

/-- The exact production obligation for the staged butterfly lowering.  It is
the full extensional refinement contract over all inputs and coefficients, not
a descriptor hash and not a finite differential sample. -/
def OddNttRefines {r n : Nat} {modulus : Fin r → Nat}
    (psi : (row : Fin r) → ZMod (modulus row)) : Prop :=
  ∀ (a b : RnsPoly (n := n) modulus) row coefficient,
    oddNttMul (psi row) (a row) (b row) coefficient =
      rnsNegacyclicMul a b row coefficient

/-- The odd-domain refinement is exactly strong enough to discharge the
existing backend boundary consumed by `PrivateBookBfvBindingAir`. -/
theorem oddNttRefines_is_NttRefines {r n : Nat} {modulus : Fin r → Nat}
    (psi : (row : Fin r) → ZMod (modulus row))
    (h : OddNttRefines (n := n) psi) :
    NttRefines (n := n)
      (fun (a b : RnsPoly (n := n) modulus) row =>
        oddNttMul (psi row) (a row) (b row)) := by
  intro a b row coefficient
  exact h a b row coefficient

/-- Consequently the new family lowering preserves every exact private-book
coefficient equation once its butterfly AIR discharges `OddNttRefines`. -/
theorem oddNtt_family_yields_exact_private_book_bfv_opening
    {S : Semantics}
    (psi : (row : ModulusIx) → ZMod (deployedModulus row))
    (hrefines : OddNttRefines (n := deployedDegree) psi)
    {pub : PublicInput} {witness : EncryptionWitness S} {trace : Trace}
    (hsat : Satisfied S
      (fun a b row => oddNttMul (psi row) (a row) (b row)) pub witness trace) :
    ExactPrivateBookBfvOpening S pub :=
  satisfied_yields_exact_private_book_bfv_opening
    (oddNttRefines_is_NttRefines psi hrefines) hsat

/-! ## 3. Executable multi-coefficient / multi-modulus tooth

This is intentionally larger than a one-coefficient arithmetic example.  It
runs the complete odd forward transforms, pointwise products, and inverse
transforms for all eight coefficients under the first two *production* BFV
moduli, compares every result with the independent schoolbook negacyclic
reference, and binds a claimed output packet.  One changed coefficient rejects.
-/

def TOY_DEGREE : Nat := 8
def Q0 : Nat := 68719403009
def Q1 : Nat := 68719230977
def PSI0 : Nat := 54271157817
def PSI1 : Nat := 29070506508

def toyLeft (q : Nat) : Poly q TOY_DEGREE := fun i =>
  ((3 * i.val * i.val + 5 * i.val + 7 : Nat) : ZMod q)

def toyRight (q : Nat) : Poly q TOY_DEGREE := fun i =>
  ((11 * i.val * i.val + 2 * i.val + 13 : Nat) : ZMod q)

def packetCoefficients : List (Fin TOY_DEGREE) := List.ofFn id

def ModulusPacketAccepts (q psi : Nat) (claim : Fin TOY_DEGREE → Nat) : Prop :=
  ∀ coefficient, coefficient ∈ packetCoefficients →
    claim coefficient < q ∧
    claim coefficient =
      (oddNttMul (psi : ZMod q) (toyLeft q) (toyRight q) coefficient).val ∧
    oddNttMul (psi : ZMod q) (toyLeft q) (toyRight q) coefficient =
      negacyclicMul (toyLeft q) (toyRight q) coefficient

def TwoModulusPacketAccepts
    (claim0 claim1 : Fin TOY_DEGREE → Nat) : Prop :=
  ModulusPacketAccepts Q0 PSI0 claim0 ∧
  ModulusPacketAccepts Q1 PSI1 claim1

def modulusPacketGate (q psi : Nat) (claim : Fin TOY_DEGREE → Nat) : Bool :=
  packetCoefficients.all fun coefficient =>
    decide (claim coefficient < q) &&
    decide (claim coefficient =
      (oddNttMul (psi : ZMod q) (toyLeft q) (toyRight q) coefficient).val) &&
    decide (oddNttMul (psi : ZMod q) (toyLeft q) (toyRight q) coefficient =
      negacyclicMul (toyLeft q) (toyRight q) coefficient)

def twoModulusPacketGate
    (claim0 claim1 : Fin TOY_DEGREE → Nat) : Bool :=
  modulusPacketGate Q0 PSI0 claim0 && modulusPacketGate Q1 PSI1 claim1

def honestClaim (q psi : Nat) : Fin TOY_DEGREE → Nat := fun coefficient =>
  (oddNttMul (psi : ZMod q) (toyLeft q) (toyRight q) coefficient).val

def tamperedQ1Claim : Fin TOY_DEGREE → Nat := fun coefficient =>
  if coefficient = (⟨3, by norm_num [TOY_DEGREE]⟩ : Fin TOY_DEGREE) then
    (honestClaim Q1 PSI1 coefficient + 1) % Q1
  else honestClaim Q1 PSI1 coefficient

set_option maxRecDepth 100000 in
theorem psi0_is_negacyclic_root : (PSI0 : ZMod Q0) ^ TOY_DEGREE = -1 := by
  decide

set_option maxRecDepth 100000 in
theorem psi1_is_negacyclic_root : (PSI1 : ZMod Q1) ^ TOY_DEGREE = -1 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Positive executable tooth: sixteen output equations (eight coefficients at
each of two deployed moduli) pass through the actual odd-NTT computation. -/
theorem two_modulus_packet_accepts :
    twoModulusPacketGate (honestClaim Q0 PSI0) (honestClaim Q1 PSI1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Mutation tooth: changing modulus-1 coefficient three refuses the packet. -/
theorem two_modulus_packet_refuses_mutation :
    twoModulusPacketGate (honestClaim Q0 PSI0) tamperedQ1Claim = false := by
  decide +kernel

/-- The Boolean executor has an exact proposition-level interpretation. -/
theorem twoModulusPacketGate_sound
    {claim0 claim1 : Fin TOY_DEGREE → Nat}
    (h : twoModulusPacketGate claim0 claim1 = true) :
    TwoModulusPacketAccepts claim0 claim1 := by
  rw [twoModulusPacketGate, Bool.and_eq_true] at h
  constructor
  · intro coefficient hmem
    have hcoefficient := List.all_eq_true.mp h.1 coefficient hmem
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcoefficient
    exact ⟨hcoefficient.1.1, hcoefficient.1.2, hcoefficient.2⟩
  · intro coefficient hmem
    have hcoefficient := List.all_eq_true.mp h.2 coefficient hmem
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcoefficient
    exact ⟨hcoefficient.1.1, hcoefficient.1.2, hcoefficient.2⟩

/-! ## 4. Exact residual manifest

This file fixes the target and closes the semantic compositions available
before emission.  It does **not** claim the production family is already a
mintable proof.  The remaining implementation/proof obligations are exactly:

1. emit the radix-`2^14` butterfly AIR, including canonical residues, quotient
   limbs, bounded carries, stage routing, and first/last-stage twists;
2. build the honest family witness and its cross-stage permutation/lookup bus;
3. emit both terminal coefficient equations per final row, including signed
   error, exact SIMD message, canonical ciphertext, and integer quotient gates;
4. emit the six-transform public-key certificate and recursively join its
   spectrum root to the per-book family proof;
5. prove `OddNttRefines` for the production degree/root table (the three
   `psi^4096 = -1` executable teeth above are necessary root checks, not by
   themselves the Fourier orthogonality/refinement theorem).

The former sixth obligation is now closed in `fhegg-fhe::bfv_ntt_gpu`: the
standalone scheduled odd forward/inverse transforms pin all three roots above,
stream exact butterfly rows, cover the complete `2^20 × 48` physical schedule,
and pass the fail-closed RX 6750 XT WGPU gate with CPU/reference parity plus
wrong-root, wrong-stage, wrong-modulus, changed-input, and changed-coefficient
refusals.  This closes device qualification; it does not manufacture any of the
five remaining AIR/proof obligations.

Until all five close, `oddNtt_family_yields_exact_private_book_bfv_opening`
correctly retains `OddNttRefines` as an explicit premise.
-/

def REMAINING_PRODUCTION_OBLIGATIONS : Nat := 5

#guard REMAINING_PRODUCTION_OBLIGATIONS == 5

#assert_all_clean [
  Market.PrivateBookBfvNttFamily.production_geometry,
  Market.PrivateBookBfvNttFamily.family_padding_rows,
  Market.PrivateBookBfvNttFamily.padded_family_compression,
  Market.PrivateBookBfvNttFamily.deployed_psi0_negacyclic_root,
  Market.PrivateBookBfvNttFamily.deployed_psi1_negacyclic_root,
  Market.PrivateBookBfvNttFamily.deployed_psi2_negacyclic_root,
  Market.PrivateBookBfvNttFamily.SpectralTrace.Exact.product_eq_oddNttMul,
  Market.PrivateBookBfvNttFamily.publicKeyCertificate_functional,
  Market.PrivateBookBfvNttFamily.oddNttRefines_is_NttRefines,
  Market.PrivateBookBfvNttFamily.oddNtt_family_yields_exact_private_book_bfv_opening,
  Market.PrivateBookBfvNttFamily.psi0_is_negacyclic_root,
  Market.PrivateBookBfvNttFamily.psi1_is_negacyclic_root,
  Market.PrivateBookBfvNttFamily.two_modulus_packet_accepts,
  Market.PrivateBookBfvNttFamily.two_modulus_packet_refuses_mutation,
  Market.PrivateBookBfvNttFamily.twoModulusPacketGate_sound]

end Market.PrivateBookBfvNttFamily
