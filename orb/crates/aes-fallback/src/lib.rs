//! Portable AES-GCM AEAD backend for the crypto FFI seam.
//!
//! The crypto seam (`ffi/crypto_shim.c`, `Crypto.lean`) prefers the F*-verified
//! HACL*/EverCrypt AES-GCM. That path is Vale x86-64 assembly and reports
//! `UnsupportedAlgorithm` on targets without AES-NI+CLMUL (ARM, and any non-x86
//! host). RFC 9001 §5.2 nonetheless MANDATES AES-128-GCM for QUIC Initial
//! packets, so a server must still be able to seal/open AES-GCM to interoperate.
//!
//! This crate supplies that capability where the verified path cannot run. It is
//! a thin C-ABI wrapper over `aws-lc-rs` (the AWS-LC / BoringSSL-derived crypto
//! that rustls uses): well-audited, constant-time, and hardware-accelerated on
//! ARMv8. It is deliberately NOT part of the machine-checked TCB — it is a
//! functional-usability backend. See `CRYPTO-FFI-README.md` for the trust ledger.
//!
//! ## ABI
//!
//! All buffers are borrowed raw pointer+length pairs. The AEAD algorithm is
//! selected by key length: 16 → AES-128-GCM, 32 → AES-256-GCM. The nonce is the
//! 12-byte IETF GCM nonce. Output is `ciphertext ‖ tag` (tag = 16 bytes), the
//! same split-off layout the shim uses for the EverCrypt path.
//!
//! Return codes: `0` = success; any nonzero = failure (bad size, or on open, an
//! authentication failure — the two are not distinguished, matching the seam's
//! "wrong key/tag ⇒ none" contract). On failure the output buffer is untouched.

use aws_lc_rs::aead::{Aad, LessSafeKey, Nonce, UnboundKey, AES_128_GCM, AES_256_GCM, NONCE_LEN};
use aws_lc_rs::cipher::{EncryptingKey, UnboundCipherKey, AES_128, AES_256};

/// AEAD tag length (bytes) for AES-GCM as this seam uses it.
const TAG_LEN: usize = 16;

/// AES block length (bytes) — the header-protection sample/mask block size.
const AES_BLOCK_LEN: usize = 16;

const RC_OK: i32 = 0;
const RC_BAD_SIZE: i32 = 1;
const RC_AUTH_FAIL: i32 = 2;
const RC_INTERNAL: i32 = 3;

/// Pick the AEAD algorithm from the key length. `None` for any unsupported size.
fn alg_for_key(key_len: usize) -> Option<&'static aws_lc_rs::aead::Algorithm> {
    match key_len {
        16 => Some(&AES_128_GCM),
        32 => Some(&AES_256_GCM),
        _ => None,
    }
}

/// Reconstitute a borrowed slice from a raw pointer+length, tolerating the empty
/// case (a null pointer with length 0 is valid — associated data / plaintext may
/// legitimately be empty).
///
/// # Safety
/// `ptr` must be valid for `len` bytes, or `len` must be 0.
unsafe fn as_slice<'a>(ptr: *const u8, len: usize) -> &'a [u8] {
    if len == 0 {
        &[]
    } else {
        unsafe { core::slice::from_raw_parts(ptr, len) }
    }
}

/// AES-GCM seal. Selects AES-128 or AES-256 by `key_len` (16 or 32).
///
/// Writes `msg_len + 16` bytes (`ciphertext ‖ tag`) into `out`, which the caller
/// must have sized to `msg_len + 16`. Returns 0 on success.
///
/// # Safety
/// Every pointer must be valid for its stated length; `out` for `msg_len + 16`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn drorb_aes_fallback_seal(
    key: *const u8,
    key_len: usize,
    nonce: *const u8,
    nonce_len: usize,
    ad: *const u8,
    ad_len: usize,
    msg: *const u8,
    msg_len: usize,
    out: *mut u8,
) -> i32 {
    let Some(alg) = alg_for_key(key_len) else {
        return RC_BAD_SIZE;
    };
    if nonce_len != NONCE_LEN {
        return RC_BAD_SIZE;
    }

    let key_bytes = unsafe { as_slice(key, key_len) };
    let nonce_bytes = unsafe { as_slice(nonce, nonce_len) };
    let ad_bytes = unsafe { as_slice(ad, ad_len) };
    let msg_bytes = unsafe { as_slice(msg, msg_len) };

    let Ok(unbound) = UnboundKey::new(alg, key_bytes) else {
        return RC_INTERNAL;
    };
    let sealing = LessSafeKey::new(unbound);

    let mut nonce_arr = [0u8; NONCE_LEN];
    nonce_arr.copy_from_slice(nonce_bytes);
    let nonce = Nonce::assume_unique_for_key(nonce_arr);

    // in_out starts as the plaintext; seal appends the tag in place.
    let mut in_out = msg_bytes.to_vec();
    if sealing
        .seal_in_place_append_tag(nonce, Aad::from(ad_bytes), &mut in_out)
        .is_err()
    {
        return RC_INTERNAL;
    }

    debug_assert_eq!(in_out.len(), msg_len + TAG_LEN);
    let out_slice = unsafe { core::slice::from_raw_parts_mut(out, msg_len + TAG_LEN) };
    out_slice.copy_from_slice(&in_out);
    RC_OK
}

/// AES-GCM open. Selects AES-128 or AES-256 by `key_len` (16 or 32).
///
/// `ct` is `ciphertext ‖ tag` of length `ct_len` (>= 16). On a valid tag, writes
/// `ct_len - 16` plaintext bytes into `out` (caller-sized to `ct_len - 16`) and
/// returns 0. Returns nonzero on a bad size or authentication failure; `out` is
/// left untouched in that case.
///
/// # Safety
/// Every pointer must be valid for its stated length; `out` for `ct_len - 16`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn drorb_aes_fallback_open(
    key: *const u8,
    key_len: usize,
    nonce: *const u8,
    nonce_len: usize,
    ad: *const u8,
    ad_len: usize,
    ct: *const u8,
    ct_len: usize,
    out: *mut u8,
) -> i32 {
    let Some(alg) = alg_for_key(key_len) else {
        return RC_BAD_SIZE;
    };
    if nonce_len != NONCE_LEN || ct_len < TAG_LEN {
        return RC_BAD_SIZE;
    }

    let key_bytes = unsafe { as_slice(key, key_len) };
    let nonce_bytes = unsafe { as_slice(nonce, nonce_len) };
    let ad_bytes = unsafe { as_slice(ad, ad_len) };
    let ct_bytes = unsafe { as_slice(ct, ct_len) };

    let Ok(unbound) = UnboundKey::new(alg, key_bytes) else {
        return RC_INTERNAL;
    };
    let opening = LessSafeKey::new(unbound);

    let mut nonce_arr = [0u8; NONCE_LEN];
    nonce_arr.copy_from_slice(nonce_bytes);
    let nonce = Nonce::assume_unique_for_key(nonce_arr);

    // open_in_place verifies the tag and returns the plaintext prefix in place.
    let mut in_out = ct_bytes.to_vec();
    let plain = match opening.open_in_place(nonce, Aad::from(ad_bytes), &mut in_out) {
        Ok(p) => p,
        Err(_) => return RC_AUTH_FAIL,
    };

    let plain_len = ct_len - TAG_LEN;
    debug_assert_eq!(plain.len(), plain_len);
    let out_slice = unsafe { core::slice::from_raw_parts_mut(out, plain_len) };
    out_slice.copy_from_slice(plain);
    RC_OK
}

/// AES-ECB single-block encryption — the QUIC header-protection primitive for the
/// AES cipher suites (RFC 9001 §5.4.3: `mask = AES-ECB(hp_key, sample)`).
///
/// Encrypts exactly one 16-byte block in raw ECB (no padding, no IV): out =
/// AES(key, block). The key length selects the cipher (16 = AES-128, 32 =
/// AES-256; QUIC Initials use AES-128). Header protection consumes the first 5
/// bytes of the result as the mask. Same trust status as the AES-GCM fallback —
/// a portable, well-audited backend used where the verified EverCrypt/Vale AES is
/// unavailable (no AES-NI, e.g. arm64); NOT part of the machine-checked TCB.
///
/// Returns 0 on success (16 bytes written to `out`); nonzero on a bad key/block
/// size or an internal error, leaving `out` untouched.
///
/// # Safety
/// `key` valid for `key_len`; `block` and `out` each valid for 16 bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn drorb_aes_ecb_fallback(
    key: *const u8,
    key_len: usize,
    block: *const u8,
    block_len: usize,
    out: *mut u8,
) -> i32 {
    let alg = match key_len {
        16 => &AES_128,
        32 => &AES_256,
        _ => return RC_BAD_SIZE,
    };
    if block_len != AES_BLOCK_LEN {
        return RC_BAD_SIZE;
    }

    let key_bytes = unsafe { as_slice(key, key_len) };
    let block_bytes = unsafe { as_slice(block, block_len) };

    let Ok(unbound) = UnboundCipherKey::new(alg, key_bytes) else {
        return RC_INTERNAL;
    };
    let Ok(enc) = EncryptingKey::ecb(unbound) else {
        return RC_INTERNAL;
    };

    // Raw single-block ECB: no padding, no IV; encrypts the 16-byte block in place.
    let mut in_out = block_bytes.to_vec();
    if enc.encrypt(&mut in_out).is_err() {
        return RC_INTERNAL;
    }
    if in_out.len() != AES_BLOCK_LEN {
        return RC_INTERNAL;
    }

    let out_slice = unsafe { core::slice::from_raw_parts_mut(out, AES_BLOCK_LEN) };
    out_slice.copy_from_slice(&in_out);
    RC_OK
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Seal then open via the C ABI; assert the plaintext round-trips and that a
    /// single flipped ciphertext byte fails authentication.
    fn roundtrip(key: &[u8], nonce: &[u8], ad: &[u8], msg: &[u8]) {
        let mut sealed = vec![0u8; msg.len() + TAG_LEN];
        let rc = unsafe {
            drorb_aes_fallback_seal(
                key.as_ptr(),
                key.len(),
                nonce.as_ptr(),
                nonce.len(),
                ad.as_ptr(),
                ad.len(),
                msg.as_ptr(),
                msg.len(),
                sealed.as_mut_ptr(),
            )
        };
        assert_eq!(rc, RC_OK, "seal failed");

        let mut opened = vec![0u8; msg.len()];
        let rc = unsafe {
            drorb_aes_fallback_open(
                key.as_ptr(),
                key.len(),
                nonce.as_ptr(),
                nonce.len(),
                ad.as_ptr(),
                ad.len(),
                sealed.as_ptr(),
                sealed.len(),
                opened.as_mut_ptr(),
            )
        };
        assert_eq!(rc, RC_OK, "open failed");
        assert_eq!(&opened, msg, "plaintext mismatch");

        // Tamper: flip one ciphertext byte, expect an auth failure.
        let mut bad = sealed.clone();
        bad[0] ^= 0xff;
        let mut opened2 = vec![0u8; msg.len()];
        let rc = unsafe {
            drorb_aes_fallback_open(
                key.as_ptr(),
                key.len(),
                nonce.as_ptr(),
                nonce.len(),
                ad.as_ptr(),
                ad.len(),
                bad.as_ptr(),
                bad.len(),
                opened2.as_mut_ptr(),
            )
        };
        assert_ne!(rc, RC_OK, "tampered ciphertext must NOT open");
    }

    #[test]
    fn aes128_roundtrip_and_tamper() {
        let key = [0x02u8; 16];
        let nonce = [0u8; 12];
        let ad = b"quic-initial";
        roundtrip(&key, &nonce, ad, b"AES-128-GCM through aws-lc-rs");
    }

    #[test]
    fn aes256_roundtrip_and_tamper() {
        let key = [0x02u8; 32];
        let nonce = [0u8; 12];
        let ad = b"quic-initial";
        roundtrip(&key, &nonce, ad, b"AES-256-GCM through aws-lc-rs");
    }

    /// NIST GCM known-answer: AES-128, all-zero key/IV, empty plaintext, empty
    /// AAD ⇒ tag 58e2fccefa7e3061367f1d57a4e7455a (NIST GCM test case 1).
    #[test]
    fn aes128_nist_case1_tag() {
        let key = [0u8; 16];
        let nonce = [0u8; 12];
        let mut sealed = vec![0u8; TAG_LEN];
        let rc = unsafe {
            drorb_aes_fallback_seal(
                key.as_ptr(),
                16,
                nonce.as_ptr(),
                12,
                core::ptr::null(),
                0,
                core::ptr::null(),
                0,
                sealed.as_mut_ptr(),
            )
        };
        assert_eq!(rc, RC_OK);
        let expect = [
            0x58, 0xe2, 0xfc, 0xce, 0xfa, 0x7e, 0x30, 0x61, 0x36, 0x7f, 0x1d, 0x57, 0xa4, 0xe7,
            0x45, 0x5a,
        ];
        assert_eq!(sealed, expect, "NIST GCM case-1 tag mismatch");
    }

    /// FIPS-197 Appendix C.1 AES-128 ECB known-answer: key 000102…0f, plaintext
    /// 00112233…ff ⇒ ciphertext 69c4e0d86a7b0430d8cdb78070b4c55a. This is the raw
    /// AES block function QUIC header protection (RFC 9001 §5.4.3) runs on.
    #[test]
    fn aes128_ecb_fips197_c1() {
        let key = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d,
            0x0e, 0x0f,
        ];
        let block = [
            0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd,
            0xee, 0xff,
        ];
        let mut out = [0u8; 16];
        let rc = unsafe {
            drorb_aes_ecb_fallback(key.as_ptr(), 16, block.as_ptr(), 16, out.as_mut_ptr())
        };
        assert_eq!(rc, RC_OK);
        let expect = [
            0x69, 0xc4, 0xe0, 0xd8, 0x6a, 0x7b, 0x04, 0x30, 0xd8, 0xcd, 0xb7, 0x80, 0x70, 0xb4,
            0xc5, 0x5a,
        ];
        assert_eq!(out, expect, "FIPS-197 C.1 AES-128 ECB block mismatch");
    }

    /// FIPS-197 Appendix C.3 AES-256 ECB known-answer: key 000102…1f, plaintext
    /// 00112233…ff ⇒ ciphertext 8ea2b7ca516745bfeafc49904b496089.
    #[test]
    fn aes256_ecb_fips197_c3() {
        let key: [u8; 32] = core::array::from_fn(|i| i as u8);
        let block = [
            0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd,
            0xee, 0xff,
        ];
        let mut out = [0u8; 16];
        let rc = unsafe {
            drorb_aes_ecb_fallback(key.as_ptr(), 32, block.as_ptr(), 16, out.as_mut_ptr())
        };
        assert_eq!(rc, RC_OK);
        let expect = [
            0x8e, 0xa2, 0xb7, 0xca, 0x51, 0x67, 0x45, 0xbf, 0xea, 0xfc, 0x49, 0x90, 0x4b, 0x49,
            0x60, 0x89,
        ];
        assert_eq!(out, expect, "FIPS-197 C.3 AES-256 ECB block mismatch");
    }

    /// AES-256 NIST GCM known-answer: all-zero key/IV, empty plaintext/AAD ⇒ tag
    /// 530f8afbc74536b9a963b4f1c4cb738b.
    #[test]
    fn aes256_nist_tag() {
        let key = [0u8; 32];
        let nonce = [0u8; 12];
        let mut sealed = vec![0u8; TAG_LEN];
        let rc = unsafe {
            drorb_aes_fallback_seal(
                key.as_ptr(),
                32,
                nonce.as_ptr(),
                12,
                core::ptr::null(),
                0,
                core::ptr::null(),
                0,
                sealed.as_mut_ptr(),
            )
        };
        assert_eq!(rc, RC_OK);
        let expect = [
            0x53, 0x0f, 0x8a, 0xfb, 0xc7, 0x45, 0x36, 0xb9, 0xa9, 0x63, 0xb4, 0xf1, 0xc4, 0xcb,
            0x73, 0x8b,
        ];
        assert_eq!(sealed, expect, "NIST GCM AES-256 tag mismatch");
    }
}
