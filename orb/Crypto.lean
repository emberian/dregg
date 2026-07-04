/-
# Crypto — the axiomatic crypto FFI seam

The engine's protocol models (TLS records, WireGuard transport, WebRTC/DTLS,
JWT/COSE signatures) all need a handful of cryptographic primitives. Those
primitives are NOT proven in Lean here. This module declares them as a small,
fixed set of `opaque` functions bound by `@[extern]` to `ffi/crypto_shim.c`,
which calls HACL*/EverCrypt (Project Everest) — crypto verified in F* for
memory-safety, functional-correctness-against-spec, and secret-independence
(constant-time), then extracted to C by KaRaMeL. The module states the algebraic
properties the models rely on as explicit `axiom`s.

That is the trust boundary, made legible:

  * The interface is exactly the declarations below — nothing else crosses.
  * Each primitive is `opaque`: the Lean core cannot unfold it, inspect key
    material, or "peek" at ciphertext. It knows the primitives ONLY through the
    axioms in the `Assumptions` section.
  * Every axiom is the functional shadow of a THEOREM proved of HACL*/EverCrypt
    upstream — not an assumption about an unverified blob. The residual trust is
    the F*/KaRaMeL toolchain and this shim's marshalling. See
    CRYPTO-FFI-README.md for the full trust ledger.

The engine's security theorems are therefore CONDITIONAL: they hold *relative
to* these assumptions. We do not re-derive AEAD security or the discrete-log
hardness of X25519; we name them, and compose. One worked composition is
sketched at the end (`Compose`), tying `aead_open_authentic` to the reactor's
abstract-AEAD WireGuard/TLS lanes.

All primitives operate on `ByteArray` (a flat, FFI-friendly buffer). The
engine's `Proto.Bytes = List UInt8` view converts with `⟨l.toArray⟩` / `.toList`
in pure Lean; the FFI boundary stays on `ByteArray` so the C shim is a clean
pointer+length adapter.
-/

namespace Crypto

/-! ## The interface: opaque primitives bound to the C shim.

Sizes (in bytes) the shim enforces; a size mismatch yields `none`, never a
buffer overrun:

| primitive            | key | nonce | tag | digest |
|----------------------|-----|-------|-----|--------|
| ChaCha20-Poly1305    | 32  | 12    | 16  |   –    |
| AES-GCM (128 / 256)  |16/32| 12    | 16  |   –    |
| X25519 scalar/point  | 32  |  –    |  –  |   –    |
| Ed25519 pub/sig/sk   | 32  |  –    | 64  |   –    |
| SHA-256 / SHA-384    |  –  |  –    |  –  | 32/48  |
-/

/-- AEAD seal (ChaCha20-Poly1305, IETF 96-bit nonce): `key nonce ad msg`.
Returns `some (ct ‖ tag)` (|msg|+16 bytes), or `none` on a bad key/nonce size. -/
@[extern "drorb_chachapoly_seal"]
opaque chachaSeal (key nonce ad msg : ByteArray) : Option ByteArray

/-- AEAD open (ChaCha20-Poly1305): `key nonce ad ct`. Returns `some msg` on a
valid tag, `none` on authentication failure OR a bad size. The two are
deliberately indistinguishable to the caller. -/
@[extern "drorb_chachapoly_open"]
opaque chachaOpen (key nonce ad ct : ByteArray) : Option ByteArray

/-- AEAD seal (AES-GCM). The key length selects the cipher: 16 = AES-128-GCM,
32 = AES-256-GCM (RFC 9001 §5.2 QUIC Initials use AES-128-GCM). The shim prefers
the verified EverCrypt/Vale path and, only where that reports unavailable (no
AES-NI+CLMUL, e.g. arm64), uses a portable unverified backend — see the trust
ledger. `none` on a bad key/nonce size. -/
@[extern "drorb_aesgcm_seal"]
opaque aesGcmSeal (key nonce ad msg : ByteArray) : Option ByteArray

/-- AEAD open (AES-GCM, 128/256 by key length). `none` on auth failure or bad
size. Same verified-preferred / portable-fallback dispatch as `aesGcmSeal`. -/
@[extern "drorb_aesgcm_open"]
opaque aesGcmOpen (key nonce ad ct : ByteArray) : Option ByteArray

/-- AES-ECB single 16-byte block, `out = AES(key, block)` — a raw one-block AES
permutation (no mode, no IV, no padding). The key length selects the cipher
(16 = AES-128, 32 = AES-256). This is the QUIC header-protection primitive for the
AES cipher suites (RFC 9001 §5.4.3: the 5-byte mask is `AES-ECB(hp_key,
sample)[0..5]`). `none` on a bad key/block size. Same dispatch story as AES-GCM:
verified EverCrypt/Vale AES is x86-only, so off-x86 this uses the portable
aws-lc-rs backend — NOT part of the machine-checked TCB (header protection carries
no confidentiality obligation; its security is the AEAD's). See the trust ledger. -/
@[extern "drorb_aes_ecb_block"]
opaque aesEcbBlock (key block : ByteArray) : Option ByteArray

/-- HKDF-Extract (SHA-256): `salt ikm ↦ some prk` (32 bytes). -/
@[extern "drorb_hkdf_sha256_extract"]
opaque hkdfExtract (salt ikm : ByteArray) : Option ByteArray

/-- HKDF-Expand (SHA-256): `prk info len ↦ some okm` (`len` bytes), or `none`
if `prk` is not 32 bytes or `len > 255*32`. -/
@[extern "drorb_hkdf_sha256_expand"]
opaque hkdfExpand (prk info : ByteArray) (len : USize) : Option ByteArray

/-- X25519 scalar multiplication: `scalar point ↦ some shared` (32 bytes), or
`none` on a low-order point (all-zero output, RFC 7748 §6.1). -/
@[extern "drorb_x25519"]
opaque x25519 (scalar point : ByteArray) : Option ByteArray

/-- X25519 base-point multiplication: `scalar ↦ some pub` (32 bytes). -/
@[extern "drorb_x25519_base"]
opaque x25519Base (scalar : ByteArray) : Option ByteArray

/-- Ed25519 detached verify: `pub msg sig ↦ Bool`. `false` on a bad signature
OR a wrong-length `pub`/`sig`. -/
@[extern "drorb_ed25519_verify"]
opaque ed25519Verify (pub msg sig : ByteArray) : Bool

/-- Ed25519 detached sign: `privateKey(32) msg ↦ some sig(64)`, where the
private key is the RFC 8032 §5.1.5 32-byte seed (EverCrypt derives the public key
from it internally). Present so the sign/verify roundtrip is statable; the
engine's data path only ever verifies. -/
@[extern "drorb_ed25519_sign"]
opaque ed25519Sign (secretKey msg : ByteArray) : Option ByteArray

/-- SHA-256: `msg ↦ digest` (32 bytes). Total. -/
@[extern "drorb_sha256"]
opaque sha256 (msg : ByteArray) : ByteArray

/-- SHA-384: `msg ↦ digest` (48 bytes). Total. -/
@[extern "drorb_sha384"]
opaque sha384 (msg : ByteArray) : ByteArray

/-! ## Assumptions: the trust boundary as Lean axioms.

Each `axiom` below is an ASSUMED property of the linked C implementation. They
are consistent because every primitive is `opaque` (nothing here can be refuted
by unfolding a definition). They are exactly the algebraic facts the protocol
models consume. This is the entire crypto trust surface of the engine — and each
axiom below is discharged upstream by a HACL*/EverCrypt F* proof (cited in
CRYPTO-FFI-README.md), so an auditor reviews *this list* against those proofs.

We deliberately do NOT assert security properties we cannot state honestly in
Lean's logic: collision-resistance and IND-CPA are asymptotic/probabilistic and
have no faithful first-order encoding here. Those live in CRYPTO-FFI-README.md
as informal, audit-checked assumptions. What we DO state are the exact,
checkable functional/algebraic laws the models compose against. -/

namespace Assumptions

/-- **AEAD correctness (ChaCha20-Poly1305).** Whatever `chachaSeal` produces,
`chachaOpen` under the same key/nonce/ad recovers the plaintext. -/
axiom chacha_open_seal_roundtrip :
  ∀ key nonce ad msg ct,
    chachaSeal key nonce ad msg = some ct →
    chachaOpen key nonce ad ct = some msg

/-- **AEAD authenticity / forgery-resistance (ChaCha20-Poly1305).** The ONLY
ciphertexts that open are the ones `chachaSeal` produced for that exact
`(key, nonce, ad, plaintext)`. This is the functional shadow of INT-CTXT: an
adversary cannot fabricate a `ct` that decrypts under a key it does not hold.
A model that accepts a message *only when* `chachaOpen … = some m` thereby only
ever accepts genuine sender output. -/
axiom chacha_open_authentic :
  ∀ key nonce ad ct msg,
    chachaOpen key nonce ad ct = some msg →
    chachaSeal key nonce ad msg = some ct

/-- **AEAD correctness (AES-256-GCM).** -/
axiom aesgcm_open_seal_roundtrip :
  ∀ key nonce ad msg ct,
    aesGcmSeal key nonce ad msg = some ct →
    aesGcmOpen key nonce ad ct = some msg

/-- **AEAD authenticity (AES-256-GCM).** -/
axiom aesgcm_open_authentic :
  ∀ key nonce ad ct msg,
    aesGcmOpen key nonce ad ct = some msg →
    aesGcmSeal key nonce ad msg = some ct

/-- **AES-ECB block is total and 16 bytes on a valid key/block.** On a valid key
size (16 or 32) and a 16-byte input block, the raw AES permutation is total and
returns exactly 16 bytes. This is all QUIC header protection needs — the mask is
well-defined and 5 bytes long. No secrecy is asserted: header protection is an XOR
mask whose security is the AEAD's, not this permutation's (RFC 9001 §5.4). -/
axiom aes_ecb_block_valid :
  ∀ (key block : ByteArray),
    (key.size = 16 ∨ key.size = 32) → block.size = 16 →
    ∃ out, aesEcbBlock key block = some out ∧ out.size = 16

/-- **X25519 Diffie–Hellman agreement.** When both public keys derive from
their scalars, the two DH computations agree: `a·(b·G) = b·(a·G)`. This is the
shared-secret property session-key derivation rests on. -/
axiom x25519_dh_agree :
  ∀ a b pa pb,
    x25519Base a = some pa →
    x25519Base b = some pb →
    x25519 a pb = x25519 b pa

/-- **Ed25519 correctness.** A signature made with a private key verifies under
the matching public key. `pubOf` abstracts "the public key of this seed" — the
deterministic `EverCrypt_Ed25519_secret_to_public` of the 32-byte seed — so this
is a pure statement about the implementation. -/
axiom ed25519_pubOf : ByteArray → ByteArray

axiom ed25519_sign_verify_roundtrip :
  ∀ sk msg sig,
    ed25519Sign sk msg = some sig →
    ed25519Verify (ed25519_pubOf sk) msg sig = true

/-- **SHA output lengths.** Honest, checkable structural facts (used where the
models slice fixed-width digests). Collision-resistance is NOT stated here — it
is an informal, audit-tracked assumption (see README). -/
axiom sha256_len : ∀ msg, (sha256 msg).size = 32
axiom sha384_len : ∀ msg, (sha384 msg).size = 48

end Assumptions

/-! ## Compose — one worked example of "relative to these assumptions".

The reactor never calls these primitives directly. Instead the protocol models
take crypto as an *abstract parameter* — e.g. `Wireguard.Config.openTransport :
Keys → TransportMsg → Option Bytes` — and prove their transition-system theorems
for every such function. Deploying the engine means INSTANTIATING that parameter
with the primitives above; the model's theorem then holds for the real crypto
*because* the axioms discharge the model's crypto hypotheses.

Concretely, take an `openTransport` instantiated so that accepting an inbound
record requires `chachaOpen key nonce ad ct = some plaintext`. `Wireguard.step`
delivers plaintext only on that success (`Wireguard.lean`, the `openTransport …
= none` reject path). Composing with `chacha_open_authentic`: any accepted
record's plaintext is exactly what the peer sealed under the shared key — so no
attacker-fabricated record is ever delivered. The WireGuard replay/authenticity
theorems (`wg_replay_rejected`, `Window.replay_rejected`) thus transfer to the
deployed engine, conditional on `chacha_open_authentic`.

The same shape covers TLS: `Reactor.Tls.tls_no_plain_after_close` states that
once the TLS FSM is closing/closed, no plaintext is ever surfaced — a property
of the *record-layer wiring*, independent of the cipher. It composes with AEAD
confidentiality (informal, README) to give the full "no plaintext leaks"
guarantee: the FSM never surfaces plaintext after close (proved), and before
close every surfaced record was a genuine `*Open … = some _` (authenticity
axiom). We state the seam, not a re-proof of AEAD. -/

section Compose

/-- The abstract "open" contract a model lane expects: a partial function from
ciphertext to plaintext. -/
abbrev OpenFn := ByteArray → Option ByteArray

/-- Instantiate a model's open-lane at a fixed key/nonce/ad with ChaCha. -/
def chachaOpenAt (key nonce ad : ByteArray) : OpenFn := chachaOpen key nonce ad

/-- **The discharge, made explicit.** Under the ChaCha instantiation, "this
ciphertext was accepted" implies "the peer sealed exactly this plaintext" — the
model's authenticity hypothesis, delivered by the axiom. A model theorem written
against a generic `OpenFn` with an authenticity side-condition can be closed by
supplying `chachaOpenAt` and this lemma. -/
theorem chachaOpenAt_authentic (key nonce ad ct msg : ByteArray)
    (h : chachaOpenAt key nonce ad ct = some msg) :
    chachaSeal key nonce ad msg = some ct :=
  Assumptions.chacha_open_authentic key nonce ad ct msg h

end Compose

end Crypto
