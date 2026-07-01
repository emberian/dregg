/-
# Dregg2.Crypto.Deco — §8 discharge: the DECO / zkTLS payment-attestation predicate.

Discharges the Stripe money-in witness kind as a CONSTRUCTED relation, not an opaque oracle. A DECO
zkTLS proof attests that a TLS session with Stripe's API disclosed a settled payment. We model that
verification as an in-circuit relation — a chain of four field-level gates plus a range gadget — and
prove the both-directions bridge, so an accepting proof PROVES the payment facts, modulo the base §8
primitives (ed25519 EUF-CMA, HMAC unforgeability, Poseidon2 CR, STARK extractability) and the external
Web-PKI / honest-Stripe floor. This is the same discipline `Crypto/Bridge.lean` and `Crypto/Custom.lean`
discharge, applied to the DECO session-authentication chain.

    deco_bridge          : Satisfies (c) stmt w ↔ DecoRelation … stmt w
    deco_verify_sound    : verify accepts → ∃ w, DecoRelation … stmt w  (derived off bridge + `extractable`)
    deco_binds_payment   : DecoRelation + §8 carriers → Signed ∧ Tagged ∧ opening (the trust base, named)
    deco_registry_cascade: `registry_sound ∘ deco_verify_sound` through `custom (vk)`

The AUTHENTICATION CHAIN the relation certifies (each link a §8 primitive):
  1. Stripe's server key SIGNS the session key           (`sigVerify serverKey sessionKey sig`) — EUF-CMA
  2. the response transcript is MAC'd under that key      (`macVerify sessionKey transcriptCommit tag`) — HMAC
  3. the transcript commitment OPENS to the field digest  (`transcriptCommit = compress fieldsDigest salt`) — CR
  4. the field digest ENCODES exactly the disclosed facts (`fieldsDigest = encode facts`) — CR
  5. the disclosed amount is non-zero (payment succeeded)  (`1 ≤ facts.amountCents`) — the range gadget

The amount gate (5) rides the honest `RecordCircuit.range` gadget (no primitive seam). Gates (1)–(4)
are field equations threaded through the bridge; their real-world meaning is delivered by the §8
carriers, surfaced explicitly in `deco_binds_payment`. The disclosed `serverKey` is Stripe's
Web-PKI-anchored TLS key (a trusted parameter of the registration), and `encode` is Stripe's response
schema — those two facts are the external floor, carried by the registration, not proved here.
-/
import Dregg2.Crypto.PortalFloor
import Dregg2.Exec.RecordCircuit
import Dregg2.Authority.Predicate
import Dregg2.Tactics

namespace Dregg2.Crypto.Deco

open Dregg2.Exec.RecordCircuit
open Dregg2.Crypto.PortalFloor

universe u

/-! ## The disclosed payment facts + statement (the public-input algebra). -/

/-- **`PaymentFacts`** — the bound facts a verified Stripe payment asserts, disclosed to the verifier.
Faithful to `bridge/src/stripe_mirror.rs::StripePaymentAttestation`: amount (cents), currency (ISO-4217
numeric code), recipient (the dregg cell id), and the payment-intent id (the replay nonce). -/
structure PaymentFacts where
  amountCents : Nat
  currency : Nat
  recipient : Nat
  paymentIntentId : Nat
  deriving DecidableEq, Repr

/-- **The disclosed DECO statement** — the public inputs the verifier sees: the Stripe server's
Web-PKI-anchored TLS `serverKey` (a trusted registration parameter — WHICH endpoint the proof must
authenticate against) and the disclosed `facts`. Everything else (session key, transcript, opening) is
the private witness. -/
structure Statement (Digest : Type u) where
  /-- Stripe's authenticated TLS/server public key — the Web-PKI anchor (disclosed, trusted). -/
  serverKey : Digest
  /-- The disclosed payment facts the proof must bind. -/
  facts : PaymentFacts

/-! ## `CircuitIR` — the DECO AIR witness: the session-authentication chain + the amount range gadget.

The trace carries the private witness of the four-link chain — the session key Stripe signed, the
signature, the committed transcript and its MAC tag, the field digest + opening salt — plus the boolean
bit-decomposition of `amountCents - 1` (the amount range gadget, proving the payment is non-zero /
succeeded). Mirrors the structure a DECO/zkTLS AIR emits: a signature-verify gate, a MAC gate, a hash
opening boundary, and the honest comparison gadget. -/

/-- **The DECO circuit IR** — the private witness of the authentication chain. `sessionKey`/`sig` are the
session key and Stripe's signature over it; `transcriptCommit`/`tag` the committed response transcript and
its MAC; `fieldsDigest`/`salt` the disclosed-field digest and the opening blinding; `amtBits` the boolean
decomposition of `amountCents - 1` (the range gadget for `1 ≤ amountCents`). -/
structure CircuitIR (Digest : Type u) where
  /-- The TLS session key Stripe's server key signed (authenticated by gate 1). -/
  sessionKey : Digest
  /-- Stripe's signature over the session key (the EUF-CMA leg). -/
  sig : Digest
  /-- The committed response transcript digest (MAC'd under `sessionKey`). -/
  transcriptCommit : Digest
  /-- The transcript MAC tag (the HMAC leg). -/
  tag : Digest
  /-- The disclosed-field digest the transcript opens to. -/
  fieldsDigest : Digest
  /-- The opening blinding (`salt`) for the `compress` commitment. -/
  salt : Digest
  /-- Little-endian boolean bits decomposing `amountCents - 1` (the amount range gadget). -/
  amtBits : List Int
  deriving Repr

/-! ## The DECO relation (the statement algebra) — the authentication chain the proof certifies. -/

/-- **`DecoRelation sigVerify macVerify compress encode stmt w`** — the DECO verification relation: the
four-link session-authentication chain plus the non-zero-amount comparison. `sigVerify`/`macVerify` are
the §8 signature / MAC oracles (their soundness is the EUF-CMA / HMAC carriers, surfaced in
`deco_binds_payment`); `compress` is the transcript-commitment hash (CR carrier); `encode` is Stripe's
field-encoding schema (the external floor). The conjunction: Stripe's key signed the session key, the
transcript is MAC'd under it, the transcript opens to the field digest, the field digest encodes the
disclosed facts, and the amount is non-zero. -/
def DecoRelation {Digest : Type u}
    (sigVerify : Digest → Digest → Digest → Bool)
    (macVerify : Digest → Digest → Digest → Bool)
    (compress : Digest → Digest → Digest)
    (encode : PaymentFacts → Digest)
    (stmt : Statement Digest) (w : CircuitIR Digest) : Prop :=
  -- (1) Stripe's server key signs the session key (EUF-CMA gate):
  sigVerify stmt.serverKey w.sessionKey w.sig = true ∧
  -- (2) the response transcript is MAC'd under the session key (HMAC gate):
  macVerify w.sessionKey w.transcriptCommit w.tag = true ∧
  -- (3) the transcript commitment opens to the field digest (CR opening boundary):
  w.transcriptCommit = compress w.fieldsDigest w.salt ∧
  -- (4) the field digest encodes exactly the disclosed facts (CR encode boundary):
  w.fieldsDigest = encode stmt.facts ∧
  -- (5) the disclosed amount is non-zero (payment succeeded — the range gadget):
  1 ≤ stmt.facts.amountCents

/-- **`Satisfies sigVerify macVerify compress encode circuit stmt`** — the DECO AIR check over the
disclosed statement and the witnessed trace: the four chain gates hold AND the amount range gadget is
satisfied (`amtBits` is boolean and recomposes `amountCents - 1`, so `1 ≤ amountCents` — exactly
`range_iff`). This is the conjunction the DECO AIR enforces; the amount comparison is the only gate with
combinatorial content, the rest are field equations. -/
def Satisfies {Digest : Type u}
    (sigVerify : Digest → Digest → Digest → Bool)
    (macVerify : Digest → Digest → Digest → Bool)
    (compress : Digest → Digest → Digest)
    (encode : PaymentFacts → Digest)
    (circuit : CircuitIR Digest) (stmt : Statement Digest) : Prop :=
  -- the amount range gadget: amtBits is a boolean decomposition of amountCents - 1 (⇒ 1 ≤ amountCents).
  (Boolean circuit.amtBits ∧ bitsToInt circuit.amtBits = (stmt.facts.amountCents : Int) - 1) ∧
  -- gate 1: Stripe's key signs the session key.
  sigVerify stmt.serverKey circuit.sessionKey circuit.sig = true ∧
  -- gate 2: the transcript is MAC'd under the session key.
  macVerify circuit.sessionKey circuit.transcriptCommit circuit.tag = true ∧
  -- gate 3: the transcript commitment opens to the field digest.
  circuit.transcriptCommit = compress circuit.fieldsDigest circuit.salt ∧
  -- gate 4: the field digest encodes the disclosed facts.
  circuit.fieldsDigest = encode stmt.facts

/-! ## The bridge — `Satisfies ↔ DecoRelation`, BOTH directions.

The amount gate rides the honest `range` gadget (`Exec/RecordCircuit.lean`): `→` uses `range_proves_le`,
`←` uses `range_complete`. The four chain gates are field equations / decidable checks carried through
both directions unchanged (no gate is opened — their meaning is the §8 carriers, invoked only in
`deco_binds_payment`). There is NO primitive seam inside the bridge: the comparison is pure
combinatorics, the chain gates are threaded literally. -/

/-- **`deco_sound` (the `→` half).** A satisfying trace PROVES the relation: the amount range gadget's
`range_proves_le` forces `1 ≤ amountCents`, and the four chain gates ARE the relation's first four
conjuncts. Fully proved, no crypto (the gates are threaded, never opened). -/
theorem deco_sound {Digest : Type u}
    (sigVerify macVerify : Digest → Digest → Digest → Bool)
    (compress : Digest → Digest → Digest) (encode : PaymentFacts → Digest)
    (circuit : CircuitIR Digest) (stmt : Statement Digest)
    (h : Satisfies sigVerify macVerify compress encode circuit stmt) :
    DecoRelation sigVerify macVerify compress encode stmt circuit := by
  obtain ⟨⟨hbool, hrec⟩, hsig, hmac, hopen, henc⟩ := h
  refine ⟨hsig, hmac, hopen, henc, ?_⟩
  -- range_proves_le 1 amountCents amtBits : bitsToInt amtBits = amountCents - 1 → 1 ≤ amountCents.
  have hle : (1 : Int) ≤ (stmt.facts.amountCents : Int) :=
    range_proves_le 1 (stmt.facts.amountCents : Int) circuit.amtBits hbool hrec
  exact_mod_cast hle

/-- **`deco_complete` (the `←` half).** A genuine DECO relation has a satisfying trace: from
`1 ≤ amountCents` build a boolean decomposition of `amountCents - 1` (`range_complete`), and carry the
four chain gates the relation supplies. The bit-width is the prover's canonical `Int.toNat` width. -/
theorem deco_complete {Digest : Type u}
    (sigVerify macVerify : Digest → Digest → Digest → Bool)
    (compress : Digest → Digest → Digest) (encode : PaymentFacts → Digest)
    (stmt : Statement Digest) (w : CircuitIR Digest)
    (h : DecoRelation sigVerify macVerify compress encode stmt w) :
    ∃ circuit : CircuitIR Digest, Satisfies sigVerify macVerify compress encode circuit stmt := by
  obtain ⟨hsig, hmac, hopen, henc, hamt⟩ := h
  have hd0 : (0 : Int) ≤ (stmt.facts.amountCents : Int) - 1 := by
    have : (1 : Int) ≤ (stmt.facts.amountCents : Int) := by exact_mod_cast hamt
    omega
  obtain ⟨amtBits, _, hbool, hrec⟩ :=
    range_complete ((stmt.facts.amountCents : Int) - 1).toNat ((stmt.facts.amountCents : Int) - 1) hd0 (by
      have : ((stmt.facts.amountCents : Int) - 1) = (((stmt.facts.amountCents : Int) - 1).toNat : Int) :=
        (Int.toNat_of_nonneg hd0).symm
      rw [this]; exact_mod_cast Nat.lt_two_pow_self)
  exact ⟨{ w with amtBits := amtBits }, ⟨hbool, hrec⟩, hsig, hmac, hopen, henc⟩

/-- **`deco_bridge`** — the DECO AIR's satisfiability is exactly the DECO relation. Soundness: the amount
range gadget forces `1 ≤ amountCents` (`range_proves_le`), the chain gates ARE the relation. Completeness:
a genuine relation yields a satisfying trace via `range_complete`. The comparison core is fully proved
with no primitive seam; the chain gates are threaded, their meaning carried by the §8 carriers consumed
in `deco_binds_payment`. -/
theorem deco_bridge {Digest : Type u}
    (sigVerify macVerify : Digest → Digest → Digest → Bool)
    (compress : Digest → Digest → Digest) (encode : PaymentFacts → Digest)
    (stmt : Statement Digest) :
    -- SOUNDNESS: every satisfying trace certifies the DECO relation.
    (∀ circuit : CircuitIR Digest,
        Satisfies sigVerify macVerify compress encode circuit stmt →
        DecoRelation sigVerify macVerify compress encode stmt circuit)
    ∧
    -- COMPLETENESS: a genuine DECO relation gives a satisfying trace.
    (∀ w : CircuitIR Digest,
        DecoRelation sigVerify macVerify compress encode stmt w →
        ∃ circuit : CircuitIR Digest, Satisfies sigVerify macVerify compress encode circuit stmt) :=
  ⟨fun circuit hsat => deco_sound sigVerify macVerify compress encode circuit stmt hsat,
   fun w h => deco_complete sigVerify macVerify compress encode stmt w h⟩

-- Amount comparison is fully proved via `range_iff` (no primitive seam); the chain gates are threaded
-- (their soundness is the §8 carriers, invoked in `deco_binds_payment`). Crypto residue: `extractable`.
#assert_axioms deco_sound
#assert_axioms deco_complete
#assert_axioms deco_bridge

/-! ## The trust base, NAMED — `deco_binds_payment`: lifting the relation's gates to the §8 facts.

The relation's first four conjuncts are RUNNABLE checks (`sigVerify … = true`, `macVerify … = true`, two
hash equations). This theorem lifts them to the ABSTRACT §8 relations via the primitive carriers, making
the surviving trust base explicit: an accepting DECO proof means Stripe's key GENUINELY signed the session
(`Signed`, ed25519 EUF-CMA), the transcript is GENUINELY MAC'd under it (`Tagged`, HMAC), and — via
Poseidon2 CR — the committed transcript BINDS the encoded facts (no other facts open to it). The only
assumptions are the §8 carriers + the external `serverKey`-is-Stripe / `encode`-is-the-schema floor. -/

/-- **`deco_binds_payment`** — given the §8 signature and MAC carriers, a DECO relation lifts its runnable
gates to the genuine §8 facts: Stripe's key signed the session key (`Signed`), and the response transcript
was MAC'd under it (`Tagged`). These are the real-world authentications the ed25519 EUF-CMA and HMAC
unforgeability carriers deliver; together with the opening/encode equations they bind the disclosed facts
to a Stripe-authenticated transcript. The trust base is exactly: EUF-CMA + HMAC (+ CR for uniqueness,
below) + the external floor. -/
theorem deco_binds_payment {Digest : Type u}
    [SK : SignatureKernel Digest Digest Digest] [MK : MacKernelE Digest Digest Digest]
    (compress : Digest → Digest → Digest) (encode : PaymentFacts → Digest)
    (hsig : SK.unforgeable) (hmac : MK.unforgeable)
    (stmt : Statement Digest) (w : CircuitIR Digest)
    (h : DecoRelation SK.sigVerify MK.verifyTag compress encode stmt w) :
    -- Stripe's key genuinely signed the session key (EUF-CMA):
    SK.Signed stmt.serverKey w.sessionKey ∧
    -- the transcript was genuinely MAC'd under the session key (HMAC):
    MK.Tagged w.sessionKey w.transcriptCommit w.tag ∧
    -- and the committed transcript opens to the encoding of exactly the disclosed facts:
    w.transcriptCommit = compress (encode stmt.facts) w.salt ∧
    1 ≤ stmt.facts.amountCents := by
  obtain ⟨hsigOk, hmacOk, hopen, henc, hamt⟩ := h
  refine ⟨SK.sigVerify_sound hsig _ _ _ hsigOk, MK.verifyTag_sound hmac _ _ _ hmacOk, ?_, hamt⟩
  rw [hopen, henc]

/-- **`deco_commitment_binds`** — Poseidon2 collision-resistance turns the opening into a UNIQUE binding:
two DECO witnesses whose transcript commitments and salts agree, and whose field digests encode facts,
must encode the SAME field digest — so a committed transcript cannot open to two different disclosed-field
digests. This is the CR leg of "the disclosed facts are the transcript's genuine content." -/
theorem deco_commitment_binds {Digest : Type u} [PK : Poseidon2Kernel Digest]
    (hcr : PK.collisionHard)
    (fd fd' salt salt' c : Digest)
    (ho : c = PK.compress fd salt) (ho' : c = PK.compress fd' salt') :
    fd = fd' ∧ salt = salt' := by
  have : PK.compress fd salt = PK.compress fd' salt' := by rw [← ho, ← ho']
  exact PK.noCollision hcr fd salt fd' salt' this

#assert_axioms deco_binds_payment
#assert_axioms deco_commitment_binds

/-! ## Layer B — the DECO `VerifierKernel`: `verify` + carrier + DERIVED `verify_sound`.

Mirrors `BridgeVerifierKernel`. `verify` is the §8 oracle over the disclosed statement; `extractable`
(STARK/FRI + Fiat-Shamir + the field-gate soundness folded in) gives "accept ⇒ a satisfying trace exists
for the disclosed statement"; `deco_verify_sound` is DERIVED off the bridge's soundness half. The
statement/proof live at universe 0 (the registry/dial machinery lives there). -/

/-- **Layer B — the DECO `VerifierKernel`.** The §8 `verify` oracle over the disclosed statement (Stripe's
server key + the disclosed facts), and the STARK `extractable` carrier. `extract` unpacks `extractable`:
an accepted proof witnesses a satisfying DECO trace for the disclosed statement. The `sigVerify`/`macVerify`
oracles and the `compress`/`encode` schema are fields of the kernel (the concrete DECO circuit's gates). -/
class DecoVerifierKernel (Dg : Type) (Proof : Type) where
  /-- The signature oracle of gate 1 (ed25519 verify over the session key). -/
  sigVerify : Dg → Dg → Dg → Bool
  /-- The MAC oracle of gate 2 (HMAC verify over the transcript). -/
  macVerify : Dg → Dg → Dg → Bool
  /-- The transcript-commitment hash of gate 3 (Poseidon2 compression). -/
  compress : Dg → Dg → Dg
  /-- Stripe's field-encoding schema of gate 4 (the external floor). -/
  encode : PaymentFacts → Dg
  /-- **The §8 verify oracle** (`stark::verify` for the DECO AIR): does `proof` discharge the disclosed
  statement? An opaque `Bool`; soundness is `extractable`. -/
  verify : Statement Dg → Proof → Bool
  /-- **CARRIER — STARK extractability + the field-gate soundness** (FRI + Fiat-Shamir): accept ⇒ a
  satisfying trace exists. A `Prop`; never proved. -/
  extractable : Prop
  /-- `extractable` UNPACKED: an accepted proof witnesses a satisfying DECO trace for the disclosed
  statement. The named form the bridge composes with. -/
  extract : extractable →
    ∀ (stmt : Statement Dg) (proof : Proof), verify stmt proof = true →
      ∃ circuit : CircuitIR Dg, Satisfies sigVerify macVerify compress encode circuit stmt

/-- **`deco_verify_sound`** — given `extractable`, an accepted DECO proof proves the DECO relation holds
for some witness at the disclosed statement:
`verify stmt proof = true → ∃ w, DecoRelation … stmt w`.
Derived by composing `extract` with `deco_bridge`'s soundness half; never assumed. -/
theorem deco_verify_sound {Dg Proof : Type} [K : DecoVerifierKernel Dg Proof]
    (hext : K.extractable) (stmt : Statement Dg) (proof : Proof)
    (haccept : K.verify stmt proof = true) :
    ∃ w : CircuitIR Dg, DecoRelation K.sigVerify K.macVerify K.compress K.encode stmt w := by
  obtain ⟨circuit, hsat⟩ := K.extract hext stmt proof haccept
  exact ⟨circuit, (deco_bridge K.sigVerify K.macVerify K.compress K.encode stmt).1 circuit hsat⟩

#assert_axioms deco_verify_sound

/-! ## The capstone — `deco_authenticates_payment`: the whole zkTLS soundness in one statement.

Composes `deco_verify_sound` (STARK extractability: accept ⟹ the DECO relation) with `deco_binds_payment`
(the §8 gate carriers: the runnable gates lift to the genuine `Signed`/`Tagged` facts). Given the DECO
kernel's gate oracles ARE the §8 ed25519 / HMAC oracles (`hsigEq`/`hmacEq` — definitional in a real
deployment), an accepting DECO proof PROVES a genuine Stripe-authenticated payment: Stripe's key signed
the session key, the response transcript was MAC'd under it, and the transcript opens to the encoding of
exactly the disclosed non-zero facts. Every hypothesis is a named §8 carrier or the coincidence of the
kernel's gates with the §8 oracles; the conclusion is the real payment binding. THE discharge of the
DECO/zkTLS verification, modulo the §8 floor + the external Web-PKI/Stripe floor. -/
theorem deco_authenticates_payment {Dg Proof : Type}
    [KD : DecoVerifierKernel Dg Proof] [SK : SignatureKernel Dg Dg Dg] [MK : MacKernelE Dg Dg Dg]
    (hsigEq : KD.sigVerify = SK.sigVerify) (hmacEq : KD.macVerify = MK.verifyTag)
    (hext : KD.extractable) (hsig : SK.unforgeable) (hmac : MK.unforgeable)
    (stmt : Statement Dg) (proof : Proof) (haccept : KD.verify stmt proof = true) :
    ∃ w : CircuitIR Dg,
      -- Stripe's key genuinely signed the session key (ed25519 EUF-CMA):
      SK.Signed stmt.serverKey w.sessionKey ∧
      -- the response transcript was genuinely MAC'd under it (HMAC unforgeability):
      MK.Tagged w.sessionKey w.transcriptCommit w.tag ∧
      -- and the committed transcript opens to the encoding of exactly the disclosed facts:
      w.transcriptCommit = KD.compress (KD.encode stmt.facts) w.salt ∧
      -- with a non-zero amount (the payment succeeded):
      1 ≤ stmt.facts.amountCents := by
  obtain ⟨w, hrel⟩ := deco_verify_sound hext stmt proof haccept
  rw [hsigEq, hmacEq] at hrel
  exact ⟨w, deco_binds_payment KD.compress KD.encode hsig hmac stmt w hrel⟩

#assert_axioms deco_authenticates_payment

/-! ## Layer C — the registry cascade at the open `custom (vk)` extension point.

The DECO kind is a `custom vk` registration (Stripe's DECO verification key). We install the §8 `verify`
oracle at `custom vk` and prove the cascade: an accepting proof both `Discharged`s the registry predicate
(`registry_sound`) and proves the DECO relation (`deco_verify_sound`). Single trust boundary: `extractable`
(plus the §8 gate carriers surfaced in `deco_binds_payment`). -/

open Dregg2.Authority.Predicate Dregg2.Laws

section Wiring

variable {Dg : Type} {P : Type}

/-- A `Verifier (Statement Dg) P` from the kernel's §8 `verify` oracle. -/
def decoVerifier [K : DecoVerifierKernel Dg P] : Verifier (Statement Dg) P :=
  fun stmt proof => K.verify stmt proof

/-- The DECO-kind registry: the §8 `verify` oracle installed at `custom vk` (content-addressed by
Stripe's DECO verification key `vk`). -/
def decoReg [DecoVerifierKernel Dg P] (vk : Nat)
    (base : Registry (Statement Dg) P) : Registry (Statement Dg) P :=
  fun j => if j = .custom vk then some decoVerifier else base j

/-- **`deco_registry_cascade`** — registering the DECO kind at `custom vk`, an accepting proof both
`Discharged`s the kind's predicate (`registry_sound`) and — given `extractable` — proves the DECO relation
holds for some witness (`deco_verify_sound`). Single trust boundary: `extractable`. -/
theorem deco_registry_cascade [K : DecoVerifierKernel Dg P] (vk : Nat)
    (base : Registry (Statement Dg) P)
    (stmt : Statement Dg) (proof : P) (hext : K.extractable)
    (haccept : K.verify stmt proof = true) :
    (@Discharged (Statement Dg) P
        (verifiableOfRegistry (decoReg vk base) (.custom vk)) stmt proof)
      ∧ ∃ w : CircuitIR Dg, DecoRelation K.sigVerify K.macVerify K.compress K.encode stmt w := by
  refine ⟨?_, deco_verify_sound hext stmt proof haccept⟩
  apply registry_sound (decoReg vk base) (.custom vk) stmt proof
  show registryVerify (decoReg vk base) (.custom vk) stmt proof = true
  unfold registryVerify decoReg
  simp only [↓reduceIte]
  exact haccept

end Wiring

#assert_axioms deco_registry_cascade

/-! ## `Reference` — a concrete kernel + non-vacuity witnesses over `ℤ`.

A degenerate DECO verifier kernel `def` (NOT a global `instance`) witnessing the bridge / verify-sound /
cascade end-to-end. The toy `Digest` is `ℤ`; the gate oracles echo their arguments (accept iff the parts
match a canonical trace). NOT real crypto — the real kernel is the Rust `@[extern]` DECO AIR, which leaves
`extractable` a standing obligation. -/

namespace Reference

/-- A canonical toy observation: server key `11`, session key `11` (so `sigVerify 11 11 _` accepts),
transcript `77`, tag `77` (so `macVerify 11 77 _` accepts), field digest `70`, salt `7` (so
`compress 70 7 = 77`), facts encoding `70`, amount `2500` (non-zero). -/
def refSig : Int → Int → Int → Bool := fun pk m _ => decide (pk = m)
def refMac : Int → Int → Int → Bool := fun _ _ _ => true
def refCompress : Int → Int → Int := fun a b => a + b
def refEncode : PaymentFacts → Int := fun f => (f.amountCents : Int) - 2430

/-- The canonical disclosed statement: server key `11`, a real Stripe-shaped payment. -/
def sampleStmt : Statement Int := { serverKey := 11, facts := ⟨2500, 840, 1, 999⟩ }

/-- The canonical witness: session key `11`, transcript `77 = 70 + 7`, field digest `70 = encode facts`. -/
def sampleWit : CircuitIR Int :=
  { sessionKey := 11, sig := 0, transcriptCommit := 77, tag := 0, fieldsDigest := 70, salt := 7,
    amtBits := [] }

/-- Non-vacuity of the DECO relation: all four chain gates hold and the amount is non-zero. -/
theorem sample_relation :
    DecoRelation refSig refMac refCompress refEncode sampleStmt sampleWit := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · show (70 : Int) = (2500 : Int) - 2430; norm_num
  · decide

/-- Non-vacuity of the BRIDGE completeness half: the genuine relation yields a satisfying trace. -/
example : ∃ circuit : CircuitIR Int, Satisfies refSig refMac refCompress refEncode circuit sampleStmt :=
  deco_complete refSig refMac refCompress refEncode sampleStmt sampleWit sample_relation

/-- A degenerate reference DECO verifier kernel over `ℤ` (`def`, not a global `instance`). `verify`
accepts iff the disclosed facts are non-zero and encode/open canonically against server key `11`;
`extractable := True`. `extract` rebuilds the satisfying trace from the disclosed statement. -/
@[reducible] def refKernel : DecoVerifierKernel Int Unit where
  sigVerify := refSig
  macVerify := refMac
  compress := refCompress
  encode := refEncode
  verify stmt _ := decide (stmt.serverKey = 11 ∧ 1 ≤ stmt.facts.amountCents)
  extractable := True
  extract := by
    intro _ stmt _ haccept
    simp only [decide_eq_true_eq] at haccept
    obtain ⟨hkey, hamt⟩ := haccept
    -- build the satisfying trace: session key = serverKey (= 11) so refSig accepts; open canonically.
    have hrel : DecoRelation refSig refMac refCompress refEncode stmt
        { sessionKey := stmt.serverKey, sig := 0,
          transcriptCommit := refEncode stmt.facts + 7, tag := 0,
          fieldsDigest := refEncode stmt.facts, salt := 7, amtBits := [] } := by
      refine ⟨?_, rfl, rfl, rfl, hamt⟩
      show decide (stmt.serverKey = stmt.serverKey) = true; simp
    exact deco_complete refSig refMac refCompress refEncode stmt _ hrel

/-- A toy ed25519 `SignatureKernel` over `ℤ` whose oracle IS the reference DECO sig gate (`refSig`).
`Signed pk m := pk = m`; `unforgeable` is the GENUINE EUF-CMA-shaped soundness Prop over this oracle. -/
@[reducible] def refSigKernel : SignatureKernel Int Int Int where
  Signed pk m := pk = m
  sigVerify := refSig
  unforgeable := ∀ pk m s, refSig pk m s = true → pk = m
  sigVerify_sound := fun h => h

/-- A toy HMAC `MacKernelE` over `ℤ` whose oracle IS the reference DECO mac gate (`refMac`, accept-all
toy). `Tagged` is `True` for the toy; the real kernel is the §8 HMAC extern. -/
@[reducible] def refMacKernel : MacKernelE Int Int Int where
  mac _ _ := 0
  Tagged _ _ _ := True
  verifyTag := refMac
  unforgeable := True
  verifyTag_sound := fun _ _ _ _ _ => trivial

/-- Non-vacuity of the CAPSTONE `deco_authenticates_payment`: at the reference kernels (DECO + toy
ed25519 + toy HMAC), an accepting proof yields the genuine payment binding — Stripe's key signed the
session key, the transcript is tagged, and it opens to the encoded non-zero facts. -/
theorem reference_authenticates_payment :
    ∃ w : CircuitIR Int,
      refSigKernel.Signed sampleStmt.serverKey w.sessionKey ∧
      refMacKernel.Tagged w.sessionKey w.transcriptCommit w.tag ∧
      w.transcriptCommit = refKernel.compress (refKernel.encode sampleStmt.facts) w.salt ∧
      1 ≤ sampleStmt.facts.amountCents :=
  deco_authenticates_payment (KD := refKernel) (SK := refSigKernel) (MK := refMacKernel)
    rfl rfl trivial (fun _ _ _ h => of_decide_eq_true h) trivial sampleStmt () (by decide)

#print axioms reference_authenticates_payment

/-- The empty base registry over the toy `ℤ` DECO statement / `Unit` proof. -/
def base : Registry (Statement Int) Unit := fun _ => none

/-- Non-vacuity of `deco_verify_sound`: at the reference kernel an accepted proof proves the DECO relation
holds for some witness. -/
example : ∃ w : CircuitIR Int, DecoRelation refSig refMac refCompress refEncode sampleStmt w :=
  deco_verify_sound (K := refKernel) trivial sampleStmt () (by decide)

/-- Non-vacuity of the FULL cascade: at the reference kernel an accepted proof both `Discharged`s the
registry predicate at `custom 42` AND proves the DECO relation. A NAMED witness so its axiom footprint is
checkable — the open extension point, fully lit for the DECO kind. -/
theorem reference_cascade_nonvacuous :
    (@Discharged (Statement Int) Unit
        (verifiableOfRegistry (@decoReg Int Unit refKernel 42 base) (.custom 42)) sampleStmt ())
      ∧ ∃ w : CircuitIR Int, DecoRelation refSig refMac refCompress refEncode sampleStmt w :=
  deco_registry_cascade (K := refKernel) 42 base sampleStmt () trivial (by decide)

-- Non-vacuity axiom footprint: rests only on the standard kernel axioms.
#print axioms reference_cascade_nonvacuous

end Reference

-- The amount comparison is fully proved via `range_iff` (no primitive seam); the chain gates are
-- threaded, their soundness the §8 carriers (surfaced in `deco_binds_payment`). Crypto residue:
-- `extractable` (STARK) + ed25519 EUF-CMA + HMAC + Poseidon2 CR + the external Web-PKI/Stripe floor.
#assert_axioms deco_bridge
#assert_axioms deco_verify_sound
#assert_axioms deco_binds_payment
#assert_axioms deco_registry_cascade

end Dregg2.Crypto.Deco
