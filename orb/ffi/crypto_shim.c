/*
 * crypto_shim.c — the C side of the crypto FFI seam.
 *
 * This file is the ONLY native code behind `Crypto.lean`. Every function here
 * is a TRUSTED crossing: the Lean core cannot inspect it, and reasons about it
 * only through the axioms declared in `Crypto.lean`. Keep this shim small,
 * boring, and a thin adapter over a FORMALLY VERIFIED library — it is where the
 * formal guarantees change hands (from Lean's proofs to HACL*'s F* proofs), not
 * where they stop.
 *
 * Backend: HACL* / EverCrypt (Project Everest), the machine-checked crypto
 * verified in F* for memory-safety, functional-correctness-against-spec, and
 * secret-independence (constant-time), then extracted to C by KaRaMeL. The
 * primitives this shim calls carry those proofs upstream; the axioms in
 * Crypto.lean are their functional shadows, DISCHARGED by HACL*, not merely
 * assumed of an unverified blob. See CRYPTO-FFI-README.md for the trust ledger.
 *
 * The extracted C comes from the HACL* / EverCrypt distribution's
 * gcc-compatible build (linked as libevercrypt.a); its runtime headers ship
 * under the corresponding karamel/include directory. On non-x86_64 targets
 * the Vale assembly does not apply, so Curve25519 runs the portable
 * Curve25519_51 field arithmetic. ChaCha20-Poly1305 is verified on every
 * target and is this seam's preferred AEAD.
 *
 * AES-GCM is Vale-x86 only, so the verified path reports UnsupportedAlgorithm on
 * hosts without AES-NI+CLMUL (e.g. arm64). Because RFC 9001 §5.2 MANDATES
 * AES-128-GCM for QUIC Initial packets, the AES-GCM crossings here DISPATCH:
 * they call the verified EverCrypt path first, and only when it returns
 * UnsupportedAlgorithm do they fall back to a portable, well-audited backend
 * (aws-lc-rs / AWS-LC, linked as libaes_fallback.a). That fallback is NOT part
 * of the machine-checked TCB — a functional-usability concession so AES-only
 * clients interoperate off-x86. See CRYPTO-FFI-README.md for the trust ledger.
 *
 * ABI convention (all functions):
 *   - ByteArray arguments arrive as borrowed `b_lean_obj_arg`; read with
 *     lean_sarray_cptr / lean_sarray_size, do NOT free.
 *   - `Option ByteArray` results: `none` = lean_box(0); `some x` = a tag-1
 *     constructor with the owned ByteArray in field 0.
 *   - `Bool` results are returned as uint8_t 0/1.
 *   - Size mismatches (wrong key/nonce/tag length) return `none` — they never
 *     read out of bounds. Authentication failure also returns `none`; the two
 *     are indistinguishable to the caller by design.
 */

#include <lean/lean.h>
#include <stdint.h>
#include <string.h>

#include "EverCrypt_AEAD.h"
#include "EverCrypt_AutoConfig2.h"
#include "EverCrypt_Curve25519.h"
#include "EverCrypt_Ed25519.h"
#include "EverCrypt_HKDF.h"
#include "EverCrypt_Hash.h"
#include "EverCrypt_Error.h"
#include "Hacl_Spec.h"              /* Spec_Agile_AEAD_* algorithm ids */
#include "Hacl_Streaming_Types.h"  /* Spec_Hash_Definitions_* ids */

/* Fixed sizes (bytes) this seam enforces. */
#define DRORB_AEAD_KEY   32u
#define DRORB_AEAD_NONCE 12u
#define DRORB_AEAD_TAG   16u
#define DRORB_X25519_LEN 32u
#define DRORB_ED_PK      32u
#define DRORB_ED_SK      32u  /* RFC 8032 §5.1.5 private key = 32-byte seed */
#define DRORB_ED_SIG     64u
#define DRORB_SHA256_LEN 32u
#define DRORB_SHA384_LEN 48u
#define DRORB_HKDF_PRK   32u  /* HKDF-SHA256 PRK = HashLen */

/* EverCrypt's agile dispatch reads a CPU-feature table populated by
 * AutoConfig2_init(). Run it once, before main, while single-threaded. On this
 * arm64 host it simply records "no Vale"; it is required for the Hash/AEAD
 * agile entry points to select a valid implementation. */
__attribute__((constructor))
static void drorb_crypto_init(void) {
    EverCrypt_AutoConfig2_init();
}

/* ---- small helpers ---------------------------------------------------- */

static inline lean_object *drorb_none(void) { return lean_box(0); }

static inline lean_object *drorb_some(lean_object *ba) {
    lean_object *s = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(s, 0, ba);
    return s;
}

/* Allocate an owned ByteArray of `n` bytes; caller fills lean_sarray_cptr. */
static inline lean_object *drorb_new_ba(size_t n) {
    return lean_alloc_sarray(1, n, n);
}

/* ---- AEAD: agile seal/open over EverCrypt_AEAD_{en,de}crypt_expand -----
 *
 * The `_expand` one-shot entry points fold key expansion into the call, so no
 * `EverCrypt_AEAD_state_s` handle is allocated or freed here — the shim holds
 * no long-lived secret state. EverCrypt keeps cipher and tag in separate
 * buffers; the Lean interface hands back `ct ‖ tag`, so we place the 16-byte
 * tag immediately after the ciphertext (seal) and split it back off (open).
 */

/* ChaCha20-Poly1305 seal: key(32) nonce(12) ad msg -> Option (ct ‖ tag). */
LEAN_EXPORT lean_obj_res drorb_chachapoly_seal(
        b_lean_obj_arg key, b_lean_obj_arg nonce,
        b_lean_obj_arg ad, b_lean_obj_arg msg) {
    if (lean_sarray_size(key)   != DRORB_AEAD_KEY)   return drorb_none();
    if (lean_sarray_size(nonce) != DRORB_AEAD_NONCE) return drorb_none();
    size_t mlen = lean_sarray_size(msg);
    lean_object *out = drorb_new_ba(mlen + DRORB_AEAD_TAG);
    uint8_t *cp = lean_sarray_cptr(out);
    EverCrypt_Error_error_code rc = EverCrypt_AEAD_encrypt_expand_chacha20_poly1305(
        lean_sarray_cptr(key),
        lean_sarray_cptr(nonce), DRORB_AEAD_NONCE,
        lean_sarray_cptr(ad), (uint32_t) lean_sarray_size(ad),
        lean_sarray_cptr(msg), (uint32_t) mlen,
        cp,                 /* ciphertext: mlen bytes */
        cp + mlen);         /* tag: 16 bytes, appended */
    if (rc != EverCrypt_Error_Success) { lean_dec_ref(out); return drorb_none(); }
    return drorb_some(out);
}

/* ChaCha20-Poly1305 open: key(32) nonce(12) ad (ct ‖ tag) -> Option msg. */
LEAN_EXPORT lean_obj_res drorb_chachapoly_open(
        b_lean_obj_arg key, b_lean_obj_arg nonce,
        b_lean_obj_arg ad, b_lean_obj_arg ct) {
    if (lean_sarray_size(key)   != DRORB_AEAD_KEY)   return drorb_none();
    if (lean_sarray_size(nonce) != DRORB_AEAD_NONCE) return drorb_none();
    size_t clen = lean_sarray_size(ct);
    if (clen < DRORB_AEAD_TAG) return drorb_none();
    size_t mlen = clen - DRORB_AEAD_TAG;
    uint8_t *cp = lean_sarray_cptr(ct);
    lean_object *out = drorb_new_ba(mlen);
    EverCrypt_Error_error_code rc = EverCrypt_AEAD_decrypt_expand_chacha20_poly1305(
        lean_sarray_cptr(key),
        lean_sarray_cptr(nonce), DRORB_AEAD_NONCE,
        lean_sarray_cptr(ad), (uint32_t) lean_sarray_size(ad),
        cp, (uint32_t) mlen,   /* ciphertext without tag */
        cp + mlen,             /* tag: last 16 bytes */
        lean_sarray_cptr(out));
    if (rc != EverCrypt_Error_Success) { lean_dec_ref(out); return drorb_none(); }
    return drorb_some(out);
}

/* Portable AES-GCM fallback (crates/aes-fallback, aws-lc-rs / AWS-LC), reached
 * only when the verified EverCrypt/Vale path returns UnsupportedAlgorithm. Both
 * write/consume the `ct ‖ tag` layout the shim uses; return 0 on success,
 * nonzero on a bad size or (open) authentication failure. NOT part of the
 * verified TCB — see the header comment and CRYPTO-FFI-README.md. */
extern int32_t drorb_aes_fallback_seal(
        const uint8_t *key, size_t key_len,
        const uint8_t *nonce, size_t nonce_len,
        const uint8_t *ad, size_t ad_len,
        const uint8_t *msg, size_t msg_len,
        uint8_t *out);
extern int32_t drorb_aes_fallback_open(
        const uint8_t *key, size_t key_len,
        const uint8_t *nonce, size_t nonce_len,
        const uint8_t *ad, size_t ad_len,
        const uint8_t *ct, size_t ct_len,
        uint8_t *out);
/* AES-ECB single 16-byte block (crates/aes-fallback): the QUIC header-protection
 * primitive for the AES suites (RFC 9001 §5.4.3, `mask = AES-ECB(hp_key,
 * sample)`). Writes 16 bytes to `out`; 0 on success. NOT part of the verified TCB. */
extern int32_t drorb_aes_ecb_fallback(
        const uint8_t *key, size_t key_len,
        const uint8_t *block, size_t block_len,
        uint8_t *out);

/* AES-GCM seal. The key length selects the cipher: 16 = AES-128-GCM, 32 =
 * AES-256-GCM (RFC 9001 §5.2 QUIC Initials use AES-128-GCM). Dispatch: call the
 * verified EverCrypt/Vale path first (its checked `_expand` entry point does a
 * dynamic hardware probe); if that reports UnsupportedAlgorithm — no AES-NI+CLMUL,
 * e.g. this arm64 host — fall back to the portable aws-lc-rs backend so AES-only
 * peers still interoperate. `none` only on a bad size or a backend error. */
LEAN_EXPORT lean_obj_res drorb_aesgcm_seal(
        b_lean_obj_arg key, b_lean_obj_arg nonce,
        b_lean_obj_arg ad, b_lean_obj_arg msg) {
    size_t klen = lean_sarray_size(key);
    if (klen != 16u && klen != 32u)                  return drorb_none();
    if (lean_sarray_size(nonce) != DRORB_AEAD_NONCE) return drorb_none();
    size_t mlen = lean_sarray_size(msg);
    size_t alen = lean_sarray_size(ad);
    lean_object *out = drorb_new_ba(mlen + DRORB_AEAD_TAG);
    uint8_t *cp = lean_sarray_cptr(out);
    uint8_t *kp = lean_sarray_cptr(key);
    uint8_t *np = lean_sarray_cptr(nonce);
    uint8_t *adp = lean_sarray_cptr(ad);
    uint8_t *mp = lean_sarray_cptr(msg);

    EverCrypt_Error_error_code rc = (klen == 16u)
        ? EverCrypt_AEAD_encrypt_expand_aes128_gcm(
            kp, np, DRORB_AEAD_NONCE, adp, (uint32_t) alen, mp, (uint32_t) mlen, cp, cp + mlen)
        : EverCrypt_AEAD_encrypt_expand_aes256_gcm(
            kp, np, DRORB_AEAD_NONCE, adp, (uint32_t) alen, mp, (uint32_t) mlen, cp, cp + mlen);
    if (rc == EverCrypt_Error_Success) return drorb_some(out);
    if (rc == EverCrypt_Error_UnsupportedAlgorithm) {
        /* Portable fallback: writes `ct ‖ tag` directly into `out`. */
        if (drorb_aes_fallback_seal(kp, klen, np, DRORB_AEAD_NONCE,
                                    adp, alen, mp, mlen, cp) == 0)
            return drorb_some(out);
    }
    lean_dec_ref(out); return drorb_none();
}

/* AES-GCM open. Key length selects the cipher (16/32). Same dispatch as seal:
 * verified EverCrypt first, portable aws-lc-rs fallback on UnsupportedAlgorithm.
 * `none` on auth failure, bad size, or a backend error. */
LEAN_EXPORT lean_obj_res drorb_aesgcm_open(
        b_lean_obj_arg key, b_lean_obj_arg nonce,
        b_lean_obj_arg ad, b_lean_obj_arg ct) {
    size_t klen = lean_sarray_size(key);
    if (klen != 16u && klen != 32u)                  return drorb_none();
    if (lean_sarray_size(nonce) != DRORB_AEAD_NONCE) return drorb_none();
    size_t clen = lean_sarray_size(ct);
    if (clen < DRORB_AEAD_TAG) return drorb_none();
    size_t mlen = clen - DRORB_AEAD_TAG;
    size_t alen = lean_sarray_size(ad);
    uint8_t *cp = lean_sarray_cptr(ct);
    uint8_t *kp = lean_sarray_cptr(key);
    uint8_t *np = lean_sarray_cptr(nonce);
    uint8_t *adp = lean_sarray_cptr(ad);
    lean_object *out = drorb_new_ba(mlen);
    uint8_t *op = lean_sarray_cptr(out);

    EverCrypt_Error_error_code rc = (klen == 16u)
        ? EverCrypt_AEAD_decrypt_expand_aes128_gcm(
            kp, np, DRORB_AEAD_NONCE, adp, (uint32_t) alen, cp, (uint32_t) mlen, cp + mlen, op)
        : EverCrypt_AEAD_decrypt_expand_aes256_gcm(
            kp, np, DRORB_AEAD_NONCE, adp, (uint32_t) alen, cp, (uint32_t) mlen, cp + mlen, op);
    if (rc == EverCrypt_Error_Success) return drorb_some(out);
    if (rc == EverCrypt_Error_UnsupportedAlgorithm) {
        /* Portable fallback: verifies the tag, writes plaintext into `out`. */
        if (drorb_aes_fallback_open(kp, klen, np, DRORB_AEAD_NONCE,
                                    adp, alen, cp, clen, op) == 0)
            return drorb_some(out);
    }
    lean_dec_ref(out); return drorb_none();
}

/* AES-ECB single block — QUIC header protection for the AES cipher suites
 * (RFC 9001 §5.4.3): the 5-byte header-protection mask is the first bytes of
 * `AES-ECB(hp_key, sample)`, where `sample` is a 16-byte slice of the protected
 * payload. This is a raw one-block AES permutation (no mode, no IV, no padding).
 *
 * The verified EverCrypt/Vale AES is x86-only and exposes no agile single-block
 * ECB entry point, so — as with AES-GCM off-x86 — this crossing goes straight to
 * the portable aws-lc-rs backend (crates/aes-fallback). The key length selects
 * the cipher (16 = AES-128, 32 = AES-256; QUIC Initials use AES-128). `none` on a
 * bad key/block size or a backend error. NOT part of the machine-checked TCB —
 * header protection carries no confidentiality obligation (its security is the
 * AEAD's); see CRYPTO-FFI-README.md.
 *
 *   drorb_aes_ecb_block : key(16|32) block(16) -> Option (AES-ECB block, 16 bytes)
 */
#define DRORB_AES_BLOCK 16u
LEAN_EXPORT lean_obj_res drorb_aes_ecb_block(
        b_lean_obj_arg key, b_lean_obj_arg block) {
    size_t klen = lean_sarray_size(key);
    if (klen != 16u && klen != 32u)            return drorb_none();
    if (lean_sarray_size(block) != DRORB_AES_BLOCK) return drorb_none();
    lean_object *out = drorb_new_ba(DRORB_AES_BLOCK);
    if (drorb_aes_ecb_fallback(lean_sarray_cptr(key), klen,
                               lean_sarray_cptr(block), DRORB_AES_BLOCK,
                               lean_sarray_cptr(out)) == 0)
        return drorb_some(out);
    lean_dec_ref(out); return drorb_none();
}

/* ---- HKDF-SHA256 ------------------------------------------------------ */

/* extract: salt ikm -> prk(32) ; total (EverCrypt_HKDF_extract cannot fail). */
LEAN_EXPORT lean_obj_res drorb_hkdf_sha256_extract(
        b_lean_obj_arg salt, b_lean_obj_arg ikm) {
    lean_object *prk = drorb_new_ba(DRORB_HKDF_PRK);
    EverCrypt_HKDF_extract(
        Spec_Hash_Definitions_SHA2_256,
        lean_sarray_cptr(prk),
        lean_sarray_cptr(salt), (uint32_t) lean_sarray_size(salt),
        lean_sarray_cptr(ikm), (uint32_t) lean_sarray_size(ikm));
    return drorb_some(prk);
}

/* expand: prk(32) info len -> Option okm(len) ; none if len > 255*32. */
LEAN_EXPORT lean_obj_res drorb_hkdf_sha256_expand(
        b_lean_obj_arg prk, b_lean_obj_arg info, size_t len) {
    if (lean_sarray_size(prk) != DRORB_HKDF_PRK) return drorb_none();
    if (len > 255u * 32u) return drorb_none(); /* HKDF max = 255 * HashLen(=32) */
    lean_object *okm = drorb_new_ba(len);
    EverCrypt_HKDF_expand(
        Spec_Hash_Definitions_SHA2_256,
        lean_sarray_cptr(okm),
        lean_sarray_cptr(prk), DRORB_HKDF_PRK,
        lean_sarray_cptr(info), (uint32_t) lean_sarray_size(info),
        (uint32_t) len);
    return drorb_some(okm);
}

/* ---- X25519 (Curve25519 ECDH) ---------------------------------------- */

/* x25519: scalar(32) point(32) -> Option shared(32) ; none on the all-zero
 * low-order-point result (EverCrypt_Curve25519_ecdh returns false), per
 * RFC 7748 §6.1 contributory-behaviour check. */
LEAN_EXPORT lean_obj_res drorb_x25519(
        b_lean_obj_arg scalar, b_lean_obj_arg point) {
    if (lean_sarray_size(scalar) != DRORB_X25519_LEN) return drorb_none();
    if (lean_sarray_size(point)  != DRORB_X25519_LEN) return drorb_none();
    lean_object *out = drorb_new_ba(DRORB_X25519_LEN);
    bool ok = EverCrypt_Curve25519_ecdh(
        lean_sarray_cptr(out), lean_sarray_cptr(scalar), lean_sarray_cptr(point));
    if (!ok) { lean_dec_ref(out); return drorb_none(); }
    return drorb_some(out);
}

/* x25519Base: scalar(32) -> Option pub(32). secret_to_public is total. */
LEAN_EXPORT lean_obj_res drorb_x25519_base(b_lean_obj_arg scalar) {
    if (lean_sarray_size(scalar) != DRORB_X25519_LEN) return drorb_none();
    lean_object *out = drorb_new_ba(DRORB_X25519_LEN);
    EverCrypt_Curve25519_secret_to_public(
        lean_sarray_cptr(out), lean_sarray_cptr(scalar));
    return drorb_some(out);
}

/* ---- Ed25519 --------------------------------------------------------- */

/* verify: pub(32) msg sig(64) -> Bool. */
LEAN_EXPORT uint8_t drorb_ed25519_verify(
        b_lean_obj_arg pub, b_lean_obj_arg msg, b_lean_obj_arg sig) {
    if (lean_sarray_size(pub) != DRORB_ED_PK)  return 0;
    if (lean_sarray_size(sig) != DRORB_ED_SIG) return 0;
    bool ok = EverCrypt_Ed25519_verify(
        lean_sarray_cptr(pub),
        (uint32_t) lean_sarray_size(msg), lean_sarray_cptr(msg),
        lean_sarray_cptr(sig));
    return ok ? 1 : 0;
}

/* sign: privateKey(32, RFC 8032 seed) msg -> Option sig(64). Present so the
 * sign/verify roundtrip axiom is statable; the engine's data path only ever
 * calls verify. EverCrypt derives the public key from the seed internally. */
LEAN_EXPORT lean_obj_res drorb_ed25519_sign(
        b_lean_obj_arg sk, b_lean_obj_arg msg) {
    if (lean_sarray_size(sk) != DRORB_ED_SK) return drorb_none();
    lean_object *sig = drorb_new_ba(DRORB_ED_SIG);
    EverCrypt_Ed25519_sign(
        lean_sarray_cptr(sig),
        lean_sarray_cptr(sk),
        (uint32_t) lean_sarray_size(msg), lean_sarray_cptr(msg));
    return drorb_some(sig);
}

/* ---- Hashes ---------------------------------------------------------- */

/* sha256: msg -> digest(32). Agile one-shot; total. */
LEAN_EXPORT lean_obj_res drorb_sha256(b_lean_obj_arg msg) {
    lean_object *out = drorb_new_ba(DRORB_SHA256_LEN);
    EverCrypt_Hash_Incremental_hash(
        Spec_Hash_Definitions_SHA2_256,
        lean_sarray_cptr(out),
        lean_sarray_cptr(msg), (uint32_t) lean_sarray_size(msg));
    return out;
}

/* sha384: msg -> digest(48). Same agile one-shot, SHA2_384. */
LEAN_EXPORT lean_obj_res drorb_sha384(b_lean_obj_arg msg) {
    lean_object *out = drorb_new_ba(DRORB_SHA384_LEN);
    EverCrypt_Hash_Incremental_hash(
        Spec_Hash_Definitions_SHA2_384,
        lean_sarray_cptr(out),
        lean_sarray_cptr(msg), (uint32_t) lean_sarray_size(msg));
    return out;
}
