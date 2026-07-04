# Deepening the capture-wave boundaries: StaticFile / Cache / Jwt

This pass discharges the `UNCLOSED` items the first capture wave named in the
docstrings of `StaticFile.lean`, `Cache.lean`, and `Jwt.lean`. Each was a real
boundary in the first pass (a single-range file server, an explicit-freshness
cache, a single-`sigValid` JWT gate). Each is now a total pure function with
real theorems, in the house style. No `sorry`, no honest-UNCLOSED proof gap.

Verify:

```
lake env lean Cache.lean          # single-file, no imports
lake build StaticFile             # imports Safety.Traversal
lake build Jwt                    # imports Crypto
```

`#print axioms` on every new theorem stays within `{propext, Quot.sound,
Classical.choice}` (most are `propext`-only; several depend on no axioms).

---

## StaticFile.lean — multipart ranges, If-Range, If-Modified-Since

The first pass modeled one `RangeSpec` per request and the `If-None-Match` /
entity-tag path only. Added, in a layered `serveConditional` that keeps the
original `serveResolved` (and its theorems) untouched:

- **`multipart/byteranges`** (RFC 7233 §4.1). `resolveAll` keeps every
  satisfiable spec of a range-set; `mkParts` builds one part per pair carrying
  its exact sub-slice and inclusive offsets. `serveConditional` routes a set to a
  single-range `206`, a `multipart/byteranges` `206`, or `416` by satisfiable
  count (`serveConditional_single` / `serveConditional_multipart`).
  - **`multipart_ranges_exact`** — every part is exactly `slice body start end`,
    its offsets satisfy `start ≤ end < length`, and it has the §4.1 partial
    length `end − start + 1`. (The multi-range analogue of the existing
    `range_exact`.)
- **`If-Range` weak-validator eligibility** (RFC 7233 §3.2). `ifRangeEligible`
  honors a range only on a STRONG entity-tag match (`ETag.strongMatch`: neither
  weak, opaque tags equal) or an equal `Last-Modified` date; otherwise it serves
  the full `200`.
  - **`if_range_weak_full`** — a weak tag in `If-Range` falls back to `200 OK`.
  - `ifRange_date_eligible` / `ifRange_strong_eligible` — the positive cases.
- **`Last-Modified` / `If-Modified-Since`** (RFC 7232 §2.2, §3.3). `ifModifiedSince304`
  yields `304` when the representation was not modified since the client date,
  ordered AFTER `If-None-Match` (RFC 7232 §6).
  - **`if_modified_since_304`** — status `304`, empty body on not-modified.

New uninterpreted boundary field: `Config.lastModified`. The MIME framing of a
`multipart/byteranges` body (boundary strings, per-part headers) stays a
serialization detail — the parts are kept structured and proven exact.

## Cache.lean — heuristic freshness, directive precedence, unsafe invalidation

The first pass took `freshnessLifetime` as one opaque number and modeled only
`request`/`upstream`/`notModified`. Added:

- **Heuristic freshness** (RFC 9111 §4.2.2). `heuristicLifetime num den Date
  Last-Modified = ⌊(Date − Last-Modified)·num/den⌋` (the "10% rule" at
  `num/den = 1/10`).
  - **`heuristic_freshness_bounded`** — `lifetime · den ≤ age · num` (never
    exceeds the `num/den` fraction of the document's apparent age).
  - `heuristic_le_age` — the `num ≤ den` corollary: a heuristic lifetime never
    outruns the document's own age.
- **Directive precedence** (RFC 9111 §4.2.1). `Directives` / `selectLifetime`
  model the shared-cache order `s-maxage > max-age > Expires−Date`, where the
  higher-priority directive wins outright. `select_prefers_sMaxAge`,
  `select_maxAge_over_expires`, `select_expires_last` prove the override order.
  (These feed the `freshnessLifetime` the boundary hands to `mkMeta`.)
- **Unsafe-method invalidation** (RFC 9111 §4.4). New `Input.invalidate uri` and
  `Store.invalidate` drop every entry keyed at a URI (any method/`vary`).
  - **`unsafe_method_invalidates`** — after invalidation, `get?` for any key at
    that URI misses.
  - `invalidate_preserves_other` — a key at a different URI is untouched.
  - `step_bounded` / `cache_bounded` extended to the new input; invalidation only
    removes entries, so the capacity bound is preserved.

## Jwt.lean — the full algorithm matrix + crit handling

The first pass had one uninterpreted `Config.sigValid : Alg → …`. It is now a
routed matrix, `verifyFor`, pinned to the KEY's algorithm (cross-algorithm
confusion stays structurally impossible). `Alg` gains `eddsa`; `Header` gains
`crit`; `Reason` gains `critUnknown`.

- **The alg matrix** (RFC 7518 §3.1, RFC 8037 §3.1). `algFamily` routes
  HS256/384/512 → HMAC, RS256/384/512 → RSASSA-PKCS1-v1_5, PS256 → RSASSA-PSS,
  ES256/384 → ECDSA, EdDSA → the verified primitive.
  - **`jwt_alg_matrix_total`** — every declared alg routes to a family *iff* it
    is not the unsecured `none`; the matrix has no gap.
  - `verifyFor_routes` — each non-`none` alg's `verifyFor` goes through exactly
    its family verifier; `verifyFor_none` — `none` verifies nothing.
- **EdDSA uses the real verified boundary.** `edVerify` marshals the Ed25519
  public key / signing input / signature to `ByteArray` and calls
  `Crypto.ed25519Verify` (HACL*/EverCrypt, correctness discharged upstream in
  `Crypto.Assumptions`). This is NOT a re-stub.
  - **`eddsa_uses_evercrypt`** — the EdDSA slot is definitionally
    `Crypto.ed25519Verify`.
  - HMAC / RSA / ECDSA remain named `Config` boundaries — there is no in-tree
    verified primitive for them, so they stay honest boundaries (like the
    original `sigValid`), not fake proofs.
- **Critical-header handling** (RFC 7515 §4.1.11). `critOk` rejects any token
  whose `crit` names an extension outside `Config.understoodCrit`; the gate sits
  in `afterKey` after the algorithm gates.
  - **`jwt_crit_unknown_rejected`** — an unrecognized `crit` rejects with
    `critUnknown`, never admits.
  - `jwt_crit_understood` — an admit forces every `crit` name understood.
  - `afterKey_admit` (and the four downstream inversion theorems
    `jwt_rejects_bad_sig` / `jwt_alg_confusion_safe` / `jwt_rejects_expired` /
    `jwt_claims_checked`) are re-proved through the new gate; the `alg=none`
    rejection remains, now doubled by `verifyFor_none`.
