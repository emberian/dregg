# Crypto FFI — the trust ledger

`Crypto.lean` declares a small, fixed set of `opaque @[extern]` primitives and
states the algebraic laws the protocol models consume as Lean `axiom`s. This
file is the ledger for the one place the Lean proofs hand off to native code:
`ffi/crypto_shim.c`, and the library it calls.

**That library is HACL\*/EverCrypt (Project Everest) — formally verified crypto,
not an unverified C blob.** Every primitive below is machine-checked in F\* for
three properties and then extracted to C by KaRaMeL:

> **One documented exception: AES-GCM off x86.** EverCrypt's AES-GCM is Vale
> x86-64 assembly and reports `UnsupportedAlgorithm` on hosts without AES-NI+CLMUL
> (ARM, and any non-x86 target). Because RFC 9001 §5.2 *mandates* AES-128-GCM for
> QUIC Initial packets, the AES-GCM crossings **dispatch**: verified EverCrypt
> where it runs, and a portable **unverified** backend (`aws-lc-rs` / AWS-LC)
> elsewhere. ChaCha20-Poly1305 — the seam's preferred AEAD — stays verified
> EverCrypt on **every** platform. The AES-GCM fallback is spelled out in its own
> section below; it is the one place this seam trusts audited-but-not-verified
> code, and only on non-x86 AES-GCM.

1. **Memory safety** — no out-of-bounds access, no use-after-free (Low\* typing).
2. **Functional correctness** — the C computes exactly the pure F\* spec of the
   algorithm (which the RFC test vectors also pin down).
3. **Secret independence (constant-time)** — no secret-dependent branches or
   memory-access patterns; a proof obligation discharged by the Low\* effect
   system, closing the timing-side-channel class.

So each Lean `axiom` here is the *functional shadow* of a **theorem** proved
upstream about the exact code we link — discharged, not merely assumed.

## The delta this retarget buys

| | before | after |
|---|---|---|
| backend | libsodium + OpenSSL `libcrypto` | HACL\*/EverCrypt (`libevercrypt.a`) |
| nature of the C | **unverified** hand-written C/asm | C **extracted from F\* proofs** by KaRaMeL |
| unverified LOC pulled into the TCB | libsodium core + all of `libcrypto` (hundreds of thousands of LOC, none proven) | **none** |
| residual TCB addition | that entire unverified C corpus | the F\*/Low\*/KaRaMeL toolchain (audited, published) + **this shim's marshalling** (~250 LOC, listed below) + the CPU-feature dispatch table |
| axiom status | *assumed* of unverified code | *discharged* by a cited HACL\*/EverCrypt theorem |

The genuinely-trusted glue is now only: (a) KaRaMeL's C extraction is faithful to
the verified F\*, and (b) `crypto_shim.c` marshals Lean `ByteArray` pointers/lengths
correctly and splits/joins the `ct ‖ tag` layout. Both are small and reviewable.

## The functions (12 crossings) and the theorem behind each axiom

All sizes in bytes. AEAD output is `ciphertext ‖ tag` (tag = 16). The shim
enforces every length; a mismatch returns `none`, never an out-of-bounds read.

| # | Lean op | shim → EverCrypt call | Lean axiom | discharged by |
|---|---|---|---|---|
| 1 | `chachaSeal` | `EverCrypt_AEAD_encrypt_expand_chacha20_poly1305` | — (produces ct‖tag) | HACL\* ChaCha20-Poly1305 correctness vs RFC 8439 spec |
| 2 | `chachaOpen` | `EverCrypt_AEAD_decrypt_expand_chacha20_poly1305` | `chacha_open_seal_roundtrip`, `chacha_open_authentic` | decrypt∘encrypt = id and the AEAD authenticity lemma (INT-CTXT functional shadow: decrypt succeeds **only** on a genuinely-sealed `(k,n,ad,m)`), proved in HACL\* AEAD |
| 3 | `aesGcmSeal` | `EverCrypt_AEAD_encrypt_expand_aes{128,256}_gcm`, else aws-lc-rs fallback | — | EverCrypt/Vale AES-GCM correctness **on x86+AES-NI**; off-x86 the fallback is audited, not verified (see below) |
| 4 | `aesGcmOpen` | `EverCrypt_AEAD_decrypt_expand_aes{128,256}_gcm`, else aws-lc-rs fallback | `aesgcm_open_seal_roundtrip`, `aesgcm_open_authentic` | same — the axioms hold of the **verified** path; on the fallback they rest on aws-lc-rs's audit, not an F\* proof |
| 5 | `hkdfExtract` | `EverCrypt_HKDF_extract(SHA2_256,…)` | (used via composition) | HACL\* HMAC/HKDF correctness vs RFC 5869 spec |
| 6 | `hkdfExpand` | `EverCrypt_HKDF_expand(SHA2_256,…)` | (used via composition) | same |
| 7 | `x25519` | `EverCrypt_Curve25519_ecdh` | `x25519_dh_agree` (with #8) | verified Curve25519 field arithmetic; scalar-mult = the RFC 7748 spec ⇒ `a·(b·G)=b·(a·G)` |
| 8 | `x25519Base` | `EverCrypt_Curve25519_secret_to_public` | `x25519_dh_agree` | same |
| 9 | `ed25519Verify` | `EverCrypt_Ed25519_verify` | (accept ⇒ genuine, via #10) | HACL\* Ed25519 verify = RFC 8032 spec |
| 10 | `ed25519Sign` | `EverCrypt_Ed25519_sign` (32-byte seed) | `ed25519_sign_verify_roundtrip` | verify(secret_to_public(seed), m, sign(seed,m)) = true, from HACL\* Ed25519 correctness |
| 11 | `sha256` | `EverCrypt_Hash_Incremental_hash(SHA2_256,…)` | `sha256_len` (=32) | HACL\* SHA-2 correctness vs FIPS 180-4 spec |
| 12 | `sha384` | `EverCrypt_Hash_Incremental_hash(SHA2_384,…)` | `sha384_len` (=48) | same |

**Note on what is NOT claimed in Lean.** IND-CPA confidentiality and
collision-resistance are asymptotic/probabilistic and have no faithful
first-order encoding in Lean's logic; we do not state them as axioms. They remain
informal, audit-tracked assumptions — but even these rest on HACL\*'s functional
correctness (the C really is the standardized algorithm), so the reduction to the
underlying hardness assumptions is the *only* remaining gap, exactly as in a
paper proof. The exact functional/algebraic laws the models compose against ARE
stated (the axioms above), and those are the ones HACL\* discharges.

## AES-GCM off x86: the aws-lc-rs fallback (audited, not verified)

The AES-GCM key length selects the cipher at the seam: **16 bytes ⇒ AES-128-GCM,
32 bytes ⇒ AES-256-GCM** (RFC 9001 §5.2 QUIC Initials use AES-128-GCM). Both
`drorb_aesgcm_seal` and `drorb_aesgcm_open` in `crypto_shim.c` **dispatch**:

1. Call the verified EverCrypt path first
   (`EverCrypt_AEAD_{encrypt,decrypt}_expand_aes{128,256}_gcm`). Its checked
   `_expand` entry point does a dynamic AES-NI+CLMUL probe.
2. On `EverCrypt_Error_Success`, return the verified result — **the preferred
   path**, taken on every x86 host with AES-NI.
3. Only on `EverCrypt_Error_UnsupportedAlgorithm` (no AES-NI+CLMUL — ARM, and any
   non-x86 host), call the portable fallback (`crates/aes-fallback`, over
   `aws-lc-rs`), which writes the same `ct ‖ tag` layout.

**What the fallback is.** `aws-lc-rs` is the Rust binding to **AWS-LC**, AWS's
BoringSSL/OpenSSL-derived C crypto — the same backend `rustls` uses. Its AES-GCM
is constant-time and hardware-accelerated via the ARMv8 crypto extensions. It is
**well-audited production code, but it is NOT machine-checked** and is **NOT part
of the verified TCB**. This is a **deliberate, documented v1 concession** for
functional usability: it lets a ChaCha-preferring server still decrypt the
AES-128-GCM Initials that RFC 9001 mandates, on hardware where EverCrypt's Vale
AES cannot run.

**What this costs the trust ledger, stated plainly.** On an x86 host with AES-NI,
nothing changes: AES-GCM runs the verified EverCrypt/Vale code and the
`aesgcm_*` axioms are discharged by an F\* proof exactly as before. **On ARM (and
any non-x86 host), a build that exercises AES-GCM trusts `aws-lc-rs`/AWS-LC —
audited C, not the F\* proofs.** The `aesgcm_open_seal_roundtrip` and
`aesgcm_open_authentic` axioms then rest on that library's audit and test
coverage rather than on machine-checked verification. The `aes-fallback` crate is
a thin ~170-line C-ABI wrapper (`crates/aes-fallback/src/lib.rs`) selecting the
algorithm by key length; it adds no crypto of its own, only marshalling. It is
built by `ffi/build-aes-fallback.sh` (`cargo build --release -p aes-fallback` ⇒
`target/release/libaes_fallback.a`) and linked into the crypto/socket executables
alongside `libevercrypt.a` (see `lakefile.toml`).

**ChaCha20-Poly1305 is unaffected** — it is verified EverCrypt on *every*
platform and remains the seam's preferred AEAD. The fallback is scoped to
AES-GCM, and even there only when the verified path is genuinely unavailable.

## Citations

- HACL\*: J.-K. Zinzindohoué, K. Bhargavan, J. Protzenko, B. Beurdouche,
  *HACL\*: A Verified Modern Cryptographic Library*, ACM CCS 2017.
- EverCrypt: J. Protzenko, B. Parno, A. Fromherz, C. Hawblitzel, et al.,
  *EverCrypt: A Fast, Verified, Cross-Platform Cryptographic Provider*,
  IEEE S&P 2020. (Agile, multiplexing provider with the dynamic CPU dispatch
  this shim initialises via `EverCrypt_AutoConfig2_init`.)
- KaRaMeL / Low\*: J. Protzenko et al., *Verified Low-Level Programming Embedded
  in F\**, ICFP 2017 (the Low\*→C extraction that produces the linked code, with
  its secret-independence guarantee).
- Vale (AES-GCM/x64 asm, not exercised on arm64): B. Bond et al., *Vale:
  Verifying High-Performance Cryptographic Assembly Code*, USENIX Security 2017.
- Algorithm specs the correctness proofs target: RFC 8439 (ChaCha20-Poly1305),
  RFC 7748 (X25519), RFC 8032 (Ed25519), RFC 5869 (HKDF), FIPS 180-4 (SHA-2).

## HACL\* path convention

Two build fronts reach the EverCrypt archive, and they discover it differently:

- **`lakefile.toml` link args** (`orb`, `orb-mac`, `orb-linux`, `orb-win`,
  `crypto-selftest`, the TLS self-tests, `orb-quic`, `orb-mac-multi`) are static
  TOML — they cannot read an environment variable, so they all name the single
  documented location `-L/opt/hacl-star/dist/gcc-compatible`.
- **The `ffi/` shell scripts and the Rust `crates/dataplane` build** honor
  `HACL_DIST` (default `$HOME/src/hacl-star/dist/gcc-compatible`).

To satisfy both from one real distribution, a builder whose dist lives elsewhere
symlinks the documented location once:

```sh
sudo ln -s "$HOME/src/hacl-star" /opt/hacl-star     # or wherever your dist lives
export HACL_DIST=/opt/hacl-star/dist/gcc-compatible # scripts + Rust build
```

Alternatively, point `LIBRARY_PATH` at the real dist so `-levercrypt` resolves
even though the `-L` search dir is absent (a missing `-L` dir is ignored):

```sh
export LIBRARY_PATH="$HOME/src/hacl-star/dist/gcc-compatible:$LIBRARY_PATH"
```

The repository never hard-codes a home-directory path; `/opt/hacl-star` is the
one location the checked-in build files name.

## Build / verify

The extracted verified C is at `/opt/hacl-star/dist/gcc-compatible`; its KaRaMeL
runtime headers are at `/opt/hacl-star/dist/karamel/include`.

```sh
# 1. build the verified static library (once):
cd /opt/hacl-star/dist/gcc-compatible && ./configure && make -j libevercrypt.a

# 2. build the portable AES-GCM fallback (aws-lc-rs), used off-x86:
cd <repo> && ./ffi/build-aes-fallback.sh

# 3. compile the marshalling shim against the EverCrypt + karamel headers:
cd <repo> && ./ffi/build-crypto-shim.sh

# 4. build & run the vector check (RFC 8439 / 7748 / 8032 / 5869, FIPS-180,
#     NIST GCM):
lake exe crypto-selftest        # exit 0 = all vectors passed
```

On this **arm64 mac**: `./configure` detects ARM NEON and disables the x86_64
Vale assembly, so Curve25519 runs the portable, verified `Curve25519_51` field
arithmetic and EverCrypt's AES-GCM reports `UnsupportedAlgorithm`. AES-GCM
therefore runs through the **aws-lc-rs fallback** (AES-128 and AES-256), which is
hardware-accelerated by the ARMv8 crypto extensions — see the fallback section
above for the trust cost. ChaCha20-Poly1305 remains verified EverCrypt and is the
seam's preferred AEAD. `libevercrypt.a` builds clean; linking emits only cosmetic
`ld64.lld` DWARF `.debug_str_offsets` warnings from HACL\*'s `-g` debug info (they
do not affect the produced binary).

Last run (arm64): **all 14 crypto-FFI vectors passed** — the RFC 8439
ChaCha20-Poly1305 seal→open round-trip and tamper→`none` through the *verified*
code, plus AES-128-GCM and AES-256-GCM seal→open round-trips, tamper→`none`, and
the NIST GCM case-1 known-answer tag (`58e2fcce…455a`), all through the
**aws-lc-rs fallback** on this host (no AES-NI). The Rust crate additionally
carries its own `cargo test` vectors (AES-128/256 NIST GCM known-answers +
round-trip/tamper).

## Porting

The shim is the only platform-specific piece. On another target, rebuild
`libevercrypt.a` from the same `dist` (KaRaMeL emits `-linux`/`-mingw` asm
variants; `configure` selects by `uname`), build the fallback with
`build-aes-fallback.sh`, point `build-crypto-shim.sh` at the headers, and drop the
macOS-only `-Wl,-no_data_const` link flag on non-Mach-O linkers. There is no
insecure stub path for the verified primitives: the seam links verified code or it
does not link. The single audited-but-unverified crossing is the AES-GCM fallback,
taken only where EverCrypt's Vale AES-GCM is unavailable; on an x86 host with
AES-NI it is never invoked.
