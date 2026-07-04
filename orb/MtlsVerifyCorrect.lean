/-
MtlsVerifyCorrect — CORRECTNESS of mutual-TLS client-certificate verification.

This module lifts the mutual-TLS client-authentication decision from a *safety*
statement (the validator never crashes; a rejected chain yields no identity) to
a *correctness* statement: the decision matches, on every input, an independent
specification written directly from the governing standards, and it establishes
a client identity in **exactly** the cases the standards permit — no more, no
less.

The standards fixed here:

  * **RFC 8446 §4.4.2 (Certificate) / §4.4.3 (CertificateVerify).**  In TLS 1.3
    mutual authentication the client sends a `Certificate` message carrying the
    end-entity certificate and its chain, then a `CertificateVerify` message
    carrying a signature, made with the private key of the end-entity
    certificate, over the handshake transcript.  §4.4.2.4 requires the server
    to verify that the presented chain terminates in a trust anchor it is
    configured with; §4.4.3 requires the server to verify the
    `CertificateVerify` signature against the end-entity public key and the
    transcript.  Both checks are mandatory: authentication succeeds only if both
    pass, and on failure the peer is *not* authenticated.

  * **RFC 5280 §6.1 (Certification Path Validation).**  A leaf-first path
    `[c₀, c₁, …, cₙ]` is a valid certification path at verification time `now`
    against a set of trust anchors when: every certificate is inside its
    validity window (§6.1.3 (a)(2)); each non-top certificate's signature
    verifies under the public key of the next certificate up the path
    (§6.1.3 (a)(1)); every certificate that issues another asserts the CA basic
    constraint (§6.1.4, `basicConstraints` `cA = TRUE`); and the top of the path
    is a configured trust anchor (§6.1.1 (d), §6.1.4).

Two named cryptographic boundaries are threaded, never opened: `Env.verifySig`
(certificate signatures, RFC 5280 §6.1.3 (a)(1)) and the `CertificateVerify`
predicate `cvVerify` (RFC 8446 §4.4.3).  Every result holds uniformly for every
possible behaviour of those primitives — the correctness is about the
*composition*, not the cipher.

The specification (`Rfc5280Path`, `IdentityEstablished`) is stated **from the
standards, in set-and-index vocabulary** — membership, adjacency via
`List.zip … tail`, the terminal element via `getLast?` — with no reference to
the validator's recursion.  The headline theorem `establish_correct` proves the
implementation establishes an identity **iff** the specification holds, and the
concrete `#guard`s at the end witness non-vacuity: an unverified chain, an
expired certificate, and a bad `CertificateVerify` each yield **no** identity,
while a well-formed chain with a good signature yields the leaf subject.
-/

import Mtls.Verify
import Mtls.Theorems

namespace Mtls
namespace Correct

/-! ## The CertificateVerify boundary (RFC 8446 §4.4.3)

The handshake transcript that the `CertificateVerify` signature is computed over,
and the signature octets themselves, are opaque byte strings at this layer.  The
predicate `cvVerify leaf transcript sig` is the named cryptographic boundary:
`true` iff `sig` is a valid signature, under the public key bound in the
end-entity certificate `leaf`, over the `CertificateVerify` content derived from
`transcript` (RFC 8446 §4.4.3).  It is never opened; every theorem quantifies
over all its possible behaviours. -/

/-- The handshake transcript input to the `CertificateVerify` signature
(RFC 8446 §4.4.3), as an opaque octet string. -/
abbrev Transcript := List UInt8

/-- The `CertificateVerify` signature octets (RFC 8446 §4.4.3), opaque. -/
abbrev Sig := List UInt8

/-! ## The independent specification

Written directly from RFC 5280 §6.1 and RFC 8446 §4.4.2/§4.4.3, in
set-and-index vocabulary, with no reference to the validator `verifyFrom`. -/

/-- **RFC 5280 §6.1 certification-path validity, stated independently.**

A leaf-first path `chain = [c₀=leaf, …, cₙ=top]` is a valid certification path at
verification time `now` under the trust-anchor set `anchors` and the
certificate-signature primitive `vsig`.  Each field is a declarative,
recursion-free condition citing its RFC 5280 clause; adjacency is expressed by
`List.zip chain chain.tail` (the pairs `(cᵢ, cᵢ₊₁)`), the terminal certificate by
`getLast?`. -/
structure Rfc5280Path (anchors : List Cert) (vsig : Cert → Cert → Bool)
    (now : Time) (chain : Chain) : Prop where
  /-- The path is non-empty: there is an end-entity (leaf) certificate. -/
  hasLeaf  : chain ≠ []
  /-- §6.1.3 (a)(2): every certificate in the path is inside its stated validity
  window at the verification time. -/
  inWindow : ∀ c ∈ chain, c.notBefore ≤ now ∧ now ≤ c.notAfter
  /-- §6.1.3 (a)(1): for each adjacent pair `(child, issuer)` — child then the
  next certificate up the path — the child's signature verifies under the
  issuer's public key. -/
  signed   : ∀ p ∈ chain.zip chain.tail, vsig p.2 p.1 = true
  /-- §6.1.4: every certificate that issues another — every non-leaf certificate,
  i.e. every element after the head — asserts the CA basic constraint. -/
  caChain  : ∀ c ∈ chain.tail, c.isCA = true
  /-- §6.1.1 (d) / §6.1.4: the top (terminal) certificate of the path is a
  configured trust anchor. -/
  anchored : ∃ top, chain.getLast? = some top ∧ top ∈ anchors

/-- **RFC 8446 §4.4.2 + §4.4.3 + RFC 5280 §6.1: the identity-establishment
predicate.**  A client identity `id` is established from a presented chain,
transcript, and `CertificateVerify` signature exactly when:

  * the chain is `leaf :: rest` and `id` is the leaf (end-entity) subject;
  * that chain is a valid RFC 5280 certification path to a configured trust
    anchor at the verification time (§4.4.2.4); and
  * the `CertificateVerify` signature is valid over the transcript under the
    leaf's public key (§4.4.3).

If any conjunct fails there is no established identity — the peer is
unauthenticated. -/
def IdentityEstablished (anchors : List Cert) (vsig : Cert → Cert → Bool)
    (cvVerify : Cert → Transcript → Sig → Bool) (now : Time) (chain : Chain)
    (transcript : Transcript) (sig : Sig) (id : Name) : Prop :=
  ∃ leaf rest,
    chain = leaf :: rest
    ∧ Rfc5280Path anchors vsig now (leaf :: rest)
    ∧ cvVerify leaf transcript sig = true
    ∧ id = leaf.subject

/-! ## The implementation under verification

`establish` is the full mutual-TLS client-authentication decision: it gates the
existing certificate-path identity extractor `Mtls.authenticate` (RFC 5280 chain
validation + leaf-subject extraction) behind the `CertificateVerify` boundary
(RFC 8446 §4.4.3).  The path check is `Mtls.verifyFrom`/`Mtls.authenticate`
verbatim — this module adds only the mandatory second signature check and proves
the composition correct. -/

/-- **The verified decision.**  Establish the leaf (end-entity) subject as the
client identity iff the presented chain validates as an RFC 5280 path
(`verifyFrom`) **and** the `CertificateVerify` signature verifies under the leaf
(`cvVerify`); otherwise no identity. -/
def establish (env : Env) (cvVerify : Cert → Transcript → Sig → Bool)
    (now : Time) (chain : Chain) (transcript : Transcript) (sig : Sig) :
    Option Name :=
  match chain with
  | [] => none
  | leaf :: rest =>
      if verifyFrom env now (leaf :: rest) && cvVerify leaf transcript sig then
        some leaf.subject
      else none

/-- `establish` is exactly the existing identity extractor `Mtls.authenticate`
(RFC 5280 chain + leaf subject) gated by the `CertificateVerify` boundary — the
composition made explicit. -/
theorem establish_eq_authenticate_gate (env : Env)
    (cvVerify : Cert → Transcript → Sig → Bool) (now : Time)
    (leaf : Cert) (rest : Chain) (transcript : Transcript) (sig : Sig) :
    establish env cvVerify now (leaf :: rest) transcript sig
      = if cvVerify leaf transcript sig then
          authenticate env now (leaf :: rest)
        else none := by
  unfold establish authenticate
  by_cases hv : verifyFrom env now (leaf :: rest) = true
  · by_cases hc : cvVerify leaf transcript sig = true <;>
      simp [hv, hc]
  · simp only [Bool.not_eq_true] at hv
    by_cases hc : cvVerify leaf transcript sig = true <;>
      simp [hv, hc]

/-! ## Bridging lemmas: the recursive validator equals the declarative spec

Each impl-side predicate from `Mtls.Verify`/`Mtls.Theorems` is proved equal to
its independent, recursion-free counterpart above.  These are where a wrong
implementation would be caught: if `verifyFrom` skipped the CA check, the window
check, the signature link, or the anchor, one of these equivalences (and hence
`rfc5280_iff`) would fail. -/

/-- The terminal certificate `topOf` (impl, mirrors the validator recursion)
coincides with the declarative `getLast?`. -/
theorem topOf_eq_getLast? (chain : Chain) : topOf chain = chain.getLast? := by
  induction chain with
  | nil => rfl
  | cons c cs ih =>
    cases cs with
    | nil => rfl
    | cons next rest =>
      have h1 : topOf (c :: next :: rest) = topOf (next :: rest) := rfl
      rw [h1, List.getLast?_cons_cons, ih]

/-- Window condition: the declarative field inequalities agree with the impl's
`allValid`/`validAt`. -/
theorem inWindow_iff_allValid (now : Time) (chain : Chain) :
    (∀ c ∈ chain, c.notBefore ≤ now ∧ now ≤ c.notAfter) ↔ allValid now chain := by
  unfold allValid
  constructor
  · intro h c hc; exact validAt_iff.mpr (h c hc)
  · intro h c hc; exact validAt_iff.mp (h c hc)

/-- Adjacency signing: the declarative `zip … tail` pairwise condition agrees
with the impl's recursive `linkedSigned`. -/
theorem signedAdj_iff_linkedSigned (env : Env) (chain : Chain) :
    (∀ p ∈ chain.zip chain.tail, env.verifySig p.2 p.1 = true)
      ↔ linkedSigned env chain := by
  induction chain with
  | nil => simp [linkedSigned]
  | cons c cs ih =>
    cases cs with
    | nil => simp [linkedSigned]
    | cons next rest =>
      simp only [linkedSigned, List.tail_cons, List.zip_cons_cons,
        List.forall_mem_cons]
      rw [← ih]
      simp [List.tail_cons]

/-- CA condition: the declarative `chain.tail` condition agrees with the impl's
`nonLeafCA`. -/
theorem caChain_iff_nonLeafCA (chain : Chain) :
    (∀ c ∈ chain.tail, c.isCA = true) ↔ nonLeafCA chain := by
  cases chain with
  | nil => simp [nonLeafCA]
  | cons c rest => simp [nonLeafCA]

/-- Trust-anchor condition: the declarative `getLast?` condition agrees with the
impl's `topAnchored`. -/
theorem anchoredTop_iff_topAnchored (env : Env) (chain : Chain) :
    (∃ top, chain.getLast? = some top ∧ top ∈ env.anchors)
      ↔ topAnchored env chain := by
  unfold topAnchored
  rw [topOf_eq_getLast?]

/-- **The validator equals the independent RFC 5280 path specification.**  The
total recursive validator `verifyFrom` accepts a chain iff the declarative,
recursion-free `Rfc5280Path` holds of it. -/
theorem rfc5280_iff (env : Env) (now : Time) (chain : Chain) :
    verifyFrom env now chain = true
      ↔ Rfc5280Path env.anchors env.verifySig now chain := by
  rw [verify_iff]
  constructor
  · rintro ⟨hAll, hLink, hCA, hTop⟩
    have hAnchor := (anchoredTop_iff_topAnchored env chain).mpr hTop
    refine
      { hasLeaf := ?_
        inWindow := (inWindow_iff_allValid now chain).mpr hAll
        signed := (signedAdj_iff_linkedSigned env chain).mpr hLink
        caChain := (caChain_iff_nonLeafCA chain).mpr hCA
        anchored := hAnchor }
    obtain ⟨top, htop, _⟩ := hAnchor
    intro hnil; rw [hnil] at htop; simp at htop
  · intro hp
    exact
      ⟨(inWindow_iff_allValid now chain).mp hp.inWindow,
       (signedAdj_iff_linkedSigned env chain).mp hp.signed,
       (caChain_iff_nonLeafCA chain).mp hp.caChain,
       (anchoredTop_iff_topAnchored env chain).mp hp.anchored⟩

/-! ## The refinement theorem

The implementation establishes a client identity **exactly** when the
independent specification holds — both directions, over all inputs, uniformly in
the two cryptographic boundaries. -/

/-- **CORRECTNESS (refinement).**  The mutual-TLS decision `establish` yields the
client identity `id` **iff** `IdentityEstablished` holds: the chain is an RFC 5280
valid path to a configured trust anchor (RFC 8446 §4.4.2.4) *and* the
`CertificateVerify` signature is valid over the transcript (§4.4.3), with `id`
the end-entity subject.  Neither direction is vacuous: an unverified chain or a
bad `CertificateVerify` makes the right side false, and the theorem then forces
`establish = none`. -/
theorem establish_correct (env : Env)
    (cvVerify : Cert → Transcript → Sig → Bool) (now : Time) (chain : Chain)
    (transcript : Transcript) (sig : Sig) (id : Name) :
    establish env cvVerify now chain transcript sig = some id
      ↔ IdentityEstablished env.anchors env.verifySig cvVerify now chain
          transcript sig id := by
  unfold IdentityEstablished
  cases chain with
  | nil =>
    constructor
    · intro h; simp [establish] at h
    · rintro ⟨leaf, rest, hnil, _⟩; exact absurd hnil (by simp)
  | cons leaf rest =>
    simp only [establish]
    constructor
    · intro h
      split at h
      · rename_i hcond
        rw [Bool.and_eq_true] at hcond
        obtain ⟨hv, hcv⟩ := hcond
        exact ⟨leaf, rest, rfl,
          (rfc5280_iff env now (leaf :: rest)).mp hv, hcv,
          (Option.some.inj h).symm⟩
      · exact absurd h (by simp)
    · rintro ⟨leaf', rest', hchain, hpath, hcv, hid⟩
      obtain ⟨rfl, rfl⟩ := List.cons.inj hchain
      have hv : verifyFrom env now (leaf :: rest) = true :=
        (rfc5280_iff env now (leaf :: rest)).mpr hpath
      subst hid
      rw [if_pos (by rw [hv, hcv]; rfl)]

/-! ## No identity without both mandatory checks (RFC 8446 §4.4.2/§4.4.3) -/

/-- No identity is established from a chain that is not a valid RFC 5280 path,
whatever the `CertificateVerify` signature says. -/
theorem no_identity_of_not_path (env : Env)
    (cvVerify : Cert → Transcript → Sig → Bool) (now : Time) (chain : Chain)
    (transcript : Transcript) (sig : Sig)
    (h : ¬ Rfc5280Path env.anchors env.verifySig now chain) :
    establish env cvVerify now chain transcript sig = none := by
  cases hr : establish env cvVerify now chain transcript sig with
  | none => rfl
  | some id =>
    obtain ⟨leaf, rest, hchain, hpath, _, _⟩ :=
      (establish_correct env cvVerify now chain transcript sig id).mp hr
    exact absurd (hchain ▸ hpath) h

/-- No identity is established when the `CertificateVerify` signature over the
transcript is invalid under the leaf, whatever the chain (RFC 8446 §4.4.3). -/
theorem no_identity_of_bad_certverify (env : Env)
    (cvVerify : Cert → Transcript → Sig → Bool) (now : Time)
    (leaf : Cert) (rest : Chain) (transcript : Transcript) (sig : Sig)
    (h : cvVerify leaf transcript sig = false) :
    establish env cvVerify now (leaf :: rest) transcript sig = none := by
  simp [establish, h]

/-! ## Non-vacuity witnesses

Concrete, kernel-evaluated evidence that the refinement is real: acceptance and
each mode of rejection are distinguished.  A trivial `spec := impl` renaming
could not separate these. -/

/-- A directly-trusted, self-issued CA root (subject/issuer name `0`), valid over
`[0, 100]`. -/
def rootCert : Cert := ⟨0, 0, 0, 100, true⟩

/-- An end-entity (leaf) certificate: subject `7`, issued by name `0`, not a CA,
valid over `[0, 100]`. -/
def leafCert : Cert := ⟨7, 0, 0, 100, false⟩

/-- A plausible certificate-signature boundary: a child is signed by an issuer
iff the child's issuer name equals the issuer's subject name. -/
def demoVerifySig (issuer child : Cert) : Bool :=
  decide (child.issuer = issuer.subject)

/-- The verification environment: the demo signature boundary and a single
trust anchor, the self-issued root. -/
def demoEnv : Env := ⟨demoVerifySig, [rootCert]⟩

/-- A `CertificateVerify` boundary that accepts (a good signature). -/
def goodCv : Cert → Transcript → Sig → Bool := fun _ _ _ => true

/-- A `CertificateVerify` boundary that rejects (a bad signature). -/
def badCv : Cert → Transcript → Sig → Bool := fun _ _ _ => false

/-- A valid chain plus a good `CertificateVerify` at a valid time establishes the
leaf subject (`7`). -/
example :
    establish demoEnv goodCv 50 [leafCert, rootCert] [] [] = some 7 := by
  decide

/-- Same valid chain, but a **bad `CertificateVerify`** → no identity. -/
example :
    establish demoEnv badCv 50 [leafCert, rootCert] [] [] = none := by
  decide

/-- Valid chain, good `CertificateVerify`, but the check time is **past the
validity window** (expired) → no identity. -/
example :
    establish demoEnv goodCv 200 [leafCert, rootCert] [] [] = none := by
  decide

/-- An **unverified chain** — the leaf presented alone, terminating in a
non-anchor — with a good `CertificateVerify` → no identity. -/
example :
    establish demoEnv goodCv 50 [leafCert] [] [] = none := by
  decide

/-- A chain whose leaf is **not signed by its issuer** (the link fails the
signature boundary) → no identity, even with a good `CertificateVerify`. -/
example :
    establish demoEnv goodCv 50 [⟨7, 999, 0, 100, false⟩, rootCert] [] []
      = none := by
  decide

end Correct
end Mtls
