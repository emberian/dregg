# TlsCrypto — the TLS 1.3 key schedule and record layer over verified crypto

`TlsCrypto.lean` turns the TLS state machine's crypto from an uninterpreted
parameter into an executing, verified computation. It is the missing half of the
TLS story: `Tls/` proves *what the lifecycle may do* over any crypto; this file
supplies the *real* TLS 1.3 key schedule and record layer, computed over the
EverCrypt primitives in `Crypto.lean` (HACL*/EverCrypt, verified in F*).

## The gap it closes

The record/handshake machine in `Tls/Basic.lean` + `Tls/Step.lean` takes
cryptography as function-valued fields of `Tls.Config`:

    hsFeed         : HsConn → Bytes → HsOut       -- drive the handshake
    recOpen        : RecConn → Bytes → RecOut     -- AEAD-open a record
    recSeal        : RecConn → Bytes → RecConn × Bytes  -- AEAD-seal
    recCloseNotify : RecConn → Bytes
    extractSecrets : RecConn → Secrets

Every theorem in `Tls/Theorems.lean` quantifies over all `Config`, i.e. over
every behavior of those functions — the named crypto-axiom boundary. That makes
the lifecycle theorems strong and uniform, but the machine cannot actually
complete a handshake or protect a byte: with the fields uninterpreted there are
no keys and no ciphertext. A handshake could not complete because the crypto was
a stub. This module builds the real thing and wires it in.

## What is built, and over what

Everything is computed on `ByteArray` (matching `Crypto`); the state-machine
boundary converts to/from `Tls.Bytes = List UInt8`.

### Key schedule — RFC 8446 §7.1 / §7.3, over `Crypto` HKDF + SHA-256

- `hkdfLabel` — the `HkdfLabel` structure (`length ‖ len(fullLabel) ‖
  "tls13 "+Label ‖ len(ctx) ‖ ctx`).
- `expandLabel` = HKDF-Expand-Label, over `Crypto.hkdfExpand`.
- `deriveSecret` = Derive-Secret (context = a transcript hash);
  `deriveSecretOfMessages` hashes the messages with `Crypto.sha256`.
- `earlySecret` / `handshakeSecret` / `masterSecret` — the three
  `HKDF-Extract` nodes, over `Crypto.hkdfExtract`.
- `clientHsTrafficSecret` / `serverHsTrafficSecret` /
  `clientApTrafficSecret` / `serverApTrafficSecret` — the four traffic secrets.
- `trafficKeys` — `[sender]_write_key` / `[sender]_write_iv` (§7.3): expand a
  traffic secret under `"key"` / `"iv"` (32 / 12 bytes for ChaCha20-Poly1305).
- `deriveSchedule` / `Schedule` — the whole schedule as one record, so its
  determinism is one statement.

### Record layer — RFC 8446 §5.2 / §5.3, over `Crypto` ChaCha20-Poly1305

- `recordNonce` — sequence number left-padded to the IV length, XORed with the
  static write-IV (§5.3).
- `recordAD` — `opaque_type(23) ‖ 0x0303 ‖ length` (§5.2).
- `recordSeal` / `recordOpen` — AEAD seal/open over `Crypto.chachaSeal` /
  `Crypto.chachaOpen` (TLS_CHACHA20_POLY1305_SHA256).

## Theorems

| theorem | says | rests on |
|---|---|---|
| `keyschedule_deterministic` | the derived secrets are a pure function of the shared secret and transcript hashes — no hidden input | `propext`, `Quot.sound` |
| `record_roundtrip` | seal then open under the same key/seq/AD recovers the plaintext | `Crypto.Assumptions.chacha_open_seal_roundtrip` |
| `record_open_authentic` / `record_forgery_fails` | a ciphertext that is not the genuine sealing of `m` never opens to `m` (the INT-CTXT shadow) | `Crypto.Assumptions.chacha_open_authentic` |
| `tls_no_plaintext_after_close` | `Tls.no_plain_after_close`, specialized to a `Config` whose record path is *this* live EverCrypt layer | `propext`, `Quot.sound` |

`#print axioms` on all four shows only the core subset (`propext`, `Quot.sound`)
plus, where a record theorem needs it, the *named* EverCrypt assumption axiom it
transports — each the functional shadow of a HACL*/EverCrypt F* theorem (see
`CRYPTO-FFI-README.md`). No `sorryAx`, no `Classical.choice`.

The record theorems are stated with the additional data `ad` as an explicit
parameter, exactly mirroring the `Crypto` axioms (`key nonce ad msg`). This keeps
the roundtrip unconditional: the same `ad` is passed to seal and open, so no
ciphertext-length side condition is needed to line the two AD headers up.

Spec-conformance is also `rfl`-checkable: `deriveSchedule_early` /
`_handshake` / `_master` state each schedule field *is* its RFC 8446 §7.1
expression, so an auditor reads the chain off the theorem.

## Wiring into the state machine

`realConfig dhe thHS thAP : Tls.Config` is a concrete config whose record
functions are the real layer:

- the direction keys `tx` (server-write) and `rx` (client-write) are produced by
  the key schedule from the `X25519` shared secret `dhe` and the transcript
  hashes;
- the abstract `Tls.RecConn` id doubles as the record **sequence number**, so the
  successor connection a step returns is the same keys at the next sequence —
  matching the TLS per-record sequence counter;
- `recSeal` / `recOpen` / `recCloseNotify` call `recordSeal` / `recordOpen`
  through `Crypto.chachaSeal/Open`;
- `hsFeed` completes the handshake once ciphertext arrives, establishing the
  record connection at sequence 0 — the completion the stub could never reach.

Because `Tls.no_plain_after_close` holds for every `Config`, it holds for
`realConfig`; `tls_no_plaintext_after_close` is that specialization. The safety
property is structural, so it survives replacing the crypto stub with executing
ChaCha20-Poly1305 — the composition sketched in the `Compose` note of
`Crypto.lean`, now discharged against a record layer that actually runs.

The full handshake *message parser* (the innards of a production `hsFeed`) is
not modeled here; the deliverable is the key schedule and record layer and their
composition with the proven lifecycle.

## Running it — RFC 8448 vectors on live EverCrypt

    lake build TlsCrypto                 # library elaborates; pure #evals show the label encoding
    lake exe tls-keyschedule-selftest    # runs the schedule + record layer on linked EverCrypt

The self-test checks the key schedule against the RFC 8448 §3 "Simple 1-RTT
Handshake" trace — values that are cipher-independent for any SHA-256 suite:

    [PASS] SHA-256("") empty transcript hash
    [PASS] RFC8448 early secret                       33ad0a1c...f170f92a
    [PASS] RFC8448 Derive-Secret(early,"derived","")  6f2615a1...6c3611ba
    [PASS] record seal→open roundtrip (seq 0)
    [PASS] record open at wrong seq → none            (nonce mismatch → bad tag)
    [PASS] record tamper → none

    all 6 TLS key-schedule / record vectors passed

The `ld64.lld` `.debug_str_offsets` warnings on link are debug-info noise from
the prebuilt `libevercrypt.a`, identical to `crypto-selftest`; they do not affect
the object code.

## Files

- `TlsCrypto.lean` — the library (key schedule, record layer, theorems, wiring).
- `TlsCrypto/SelfTest.lean` — the RFC 8448 runner (`tls-keyschedule-selftest`).
- Reads, does not modify: `Crypto.lean`, `Tls/Basic.lean`, `Tls/Step.lean`,
  `Tls/Theorems.lean`.
