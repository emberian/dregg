# AUDIT — `wasm/` (pyana-wasm WebAssembly bindings)

## Verdict: NEEDS-WORK

Multiple correctness and security defects across the wasm-bindgen surface, and — most importantly — **`wasm/pkg/` is severely stale relative to `wasm/src/`** (2-day-old build missing the entire `privacy.rs` module). Whatever the extension is loading today is NOT what `src/` currently says. This makes much of the file-level audit moot for production, but the *source* tree contains several issues that will surface as soon as someone rebuilds.

No `unsafe` blocks were found. No `.view()` zero-copy slice usage (so no TOCTOU). The `panic` strategy is the workspace default (`unwind`), which is the unsafer choice for WASM. No `zeroize` / `Zeroizing` is used anywhere despite the crate handling Ed25519 secret seeds, X25519 stealth view/spend privkeys, and Schnorr scalars.

## Summary

`pyana-wasm` exports ~73 `#[wasm_bindgen]` `pub fn` items across three files. The crate is reachable from any page that loads `chrome.runtime.getURL('pyana_wasm_bg.wasm')` (the extension manifest lists `pyana_wasm.js` and `pyana_wasm_bg.wasm` in `web_accessible_resources` matched to `<all_urls>`). The WASM instance loaded by a page runs in that page's sandbox, so it cannot read the extension's storage or keys — but it can still be invoked to do expensive STARK proof work, and any bindings that *return secrets from JS-provided inputs* (e.g. `derive_stealth_keys`, `derive_keypair_from_mnemonic`) leak those secrets to whichever JS context called them.

The crate mixes three trust classes without separation: (a) pure stateless calculators safe for any caller (e.g. `blake3_hash`, `verify_*`), (b) secret-derivation bindings that should be background-worker-only (`derive_stealth_keys`, `derive_keypair_from_mnemonic`), and (c) a global `thread_local!` PyanaRuntime registry whose handles are u64 indices into a shared `Vec` — anyone with the WASM instance can pass arbitrary handles to access another component's runtime, including reading and modifying it. There is no isolation between callers within one WASM instance.

## Binding inventory (abbreviated)

| Symbol | File:line | Inputs | Output | Trust class |
|---|---|---|---|---|
| `mint_token` | lib.rs:33 | `&[u8] root_key`, `&str location` | JsValue (encoded macaroon) | background-only (key in) |
| `generate_root_key` | lib.rs:62 | — | JsValue with `key_bytes` (secret!) | background-only |
| `attenuate_token` | lib.rs:86 | `&str`, `&[u8] root_key`, … | JsValue | background-only |
| `verify_token` | lib.rs:140 | `&str`, `&[u8] root_key`, … | JsValue | background-only |
| `generate_demo_stark_proof` | lib.rs:205 | u32, u32 | JsValue | page-safe (CPU DoS) |
| `verify_demo_stark_proof` | lib.rs:273 | `&str` | JsValue | page-safe |
| `tamper_demo_stark_proof` | lib.rs:315 | `&str` | String | page-safe (demo) |
| `generate_predicate_proof` | lib.rs:349 | u32, u32, u32, `&str`, u32 | JsValue | depends — leaks `private_value` to JS caller |
| `verify_predicate_proof` | lib.rs:449 | … | JsValue | page-safe |
| `compute_merkle_root` / `merkle_*` | lib.rs:480+ | JSON | JsValue | page-safe |
| `evaluate_datalog` | lib.rs:631 | JSON, JSON | JsValue | page-safe |
| `demonstrate_fold` | lib.rs:731 | JSON, JSON | JsValue | page-safe |
| `blake3_hash` | lib.rs:819 | `&str` | String | page-safe |
| `compute_intent_id` | lib.rs:845 | `&str` JSON | String | page-safe; has panic (see P1) |
| `prove_committed_threshold` | lib.rs:1116 | u32, u32, u32 | JsValue | background-only (leaks `value`) |
| `verify_committed_threshold` | lib.rs:1187 | … | JsValue | page-safe |
| `schnorr_keygen` | lib.rs:1236 | — | JsValue with `secret_key` (secret!) | background-only |
| `schnorr_sign` | lib.rs:1269 | `&str secret_key_json`, `&str msg` | JsValue | background-only (secret in) |
| `schnorr_verify` | lib.rs:1316 | … | bool | page-safe |
| `garbled_compare` | lib.rs:1426 | u32, u32 | JsValue | leaks `prover_value` to caller |
| `prove_anonymous_membership` | lib.rs:1515 | `&str`, `&str` | JsValue | page-safe but uses 32-bit blinding |
| `derive_keypair_from_mnemonic` | lib.rs:1615 | `&str mnemonic`, `&str passphrase` | `Vec<u8>` (64B) — secret seed | background-only |
| `create_runtime` / `destroy_runtime` | bindings.rs:60/78 | handle | usize | page-safe but global registry (see P1) |
| `create_cell` / `create_agent` | bindings.rs:96/208 | handle, … | JsValue | background-only — produces deterministic privkeys |
| `execute_turn` / `execute_turn_step_by_step` | bindings.rs:336/361 | handle, JSON | JsValue | background-only |
| `grant_capability` / `revoke_capability` | bindings.rs:451/498 | handle, indices | JsValue | background-only |
| `derive_stealth_keys` | privacy.rs:25 | `&str mnemonic`, `&str passphrase` | JsValue with spend/view privkeys | background-only |
| `create_stealth_address` | privacy.rs:83 | `&[u8]`, `&[u8]` | JsValue | page-safe |
| `check_stealth_ownership` | privacy.rs:142 | `&[u8] view_privkey`, … | JsValue | background-only (privkey in) |
| `scan_stealth_announcements` | privacy.rs:195 | `&[u8] view_privkey`, … | JsValue | background-only |
| `create_value_commitment` | privacy.rs:261 | u64, `&[u8] blinding` | JsValue | background-only (blinding in) |
| `seal_intent_body` | privacy.rs:434 | `&str`, `Option<Vec<u8>>` | JsValue | broken (see P0) |
| `unseal_intent_body` | privacy.rs:473 | `&[u8]`, `&[u8]`, `&[u8] privkey` | String | background-only |
| `create_bearer_cap` / `verify_bearer_cap` | privacy.rs:517/558 | … | JsValue | dubious (see P1) |
| `compose_proofs` | privacy.rs:767 | JSON, `&str` | JsValue | page-safe (but doesn't actually compose) |
| `build_facet_mask` | privacy.rs:832 | JSON | JsValue | page-safe |

(Full set: 29 in `bindings.rs`, 24 in `lib.rs`, 20 in `privacy.rs`.)

## Findings by severity

### P0 — `seal_intent_body` "broadcast mode" makes the ciphertext recoverable from plaintext (`privacy.rs:444–449`)
When no `recipient_pubkey` is provided, the code derives the recipient key as:
```rust
let hash = blake3::derive_key("pyana-broadcast-seal-key", plaintext_json.as_bytes());
```
The recipient secret is a **deterministic function of the plaintext**. Anyone who can guess (or replay) the plaintext can re-derive the key and decrypt; identical plaintexts produce identical ciphertexts (no semantic security; trivial confirmation/correlation attacks). The "broadcast mode" name suggests this was meant for an SSE-keyed ephemeral channel; what's implemented is a no-op encryption.
**Fix:** require an explicit recipient pubkey, or generate a fresh random key per call and emit it as part of the SealedBox / out-of-band drop.

### P0 — `derive_keypair_from_mnemonic` returns wrong layout / no pubkey (`lib.rs:1614–1662`)
The doc-comment says "first 32 bytes = public key, last 32 bytes = secret key". The implementation does:
```rust
result.extend_from_slice(&derived);         // 32B secret seed
result.extend_from_slice(&[0u8; 32]);       // zeros as "public key placeholder"
```
So the layout is `[secret | zeros]` — opposite of the doc. The current extension calls `wasm.derive_keypair_from_mnemonic(mnemonic, passphrase, 'pyana/0')` (3 args; Rust takes 2 — silent drop) and reads `result.public_key` / `result.secret_key` (the function returns a `Vec<u8>`, not a struct). The extension code path in `background.js:436-440` will throw or get `undefined`, falling through to the "WASM required" error. Net effect today: mnemonic-based identity derivation does not work. After the obvious fix-attempt to "return an object", whichever 32-byte half the extension picks may be all-zeros (which would silently produce a real-looking but completely insecure all-zero identity).
**Fix:** return a typed struct via `serde_wasm_bindgen` with explicit `public_key` / `secret_key` fields, and actually compute the Ed25519 pubkey (add `ed25519-dalek` to wasm deps — it builds for WASM).

### P0 — `wasm/pkg/` is 2+ days stale and missing the entire `privacy.rs` module (build artifact freshness)
- `wasm/pkg/pyana_wasm_bg.wasm` mtime: May 21 04:38
- `wasm/src/lib.rs` mtime: May 23 08:02
- `wasm/src/privacy.rs` mtime: May 23 08:58 (newest)
- `wasm/pkg/pyana_wasm.d.ts` declares 43 exports; the source has 73 `pub fn` items
- `pkg/.gitignore` is `*` — the pkg is **untracked**, so there is no reproducible record of what shipped, and no commit-pinned SHA-256.

The extension's `background.js` references functions (`derive_stealth_keys`, `seal_intent_body`, `check_stealth_ownership`, `create_value_commitment`, `generate_range_proof`, `build_committed_turn`, `derive_stealth_one_time_address`, `generate_sse_tokens`) that are **not present** in the shipped `pyana_wasm.d.ts`. All those code paths will hit the `if (!wasm.X)` guards and fall through to error or to legacy JS implementations — i.e. the stealth and committed-transfer features are silently disabled in extension builds against this pkg. Conversely, the extension also calls `wasm.generate_mnemonic` and `wasm.validate_mnemonic`, which are **not present in the source either**, indicating drift in both directions.
**Fix:** add a CI step that rebuilds `pkg/` whenever `src/` changes and either commits the result with a checksum file or rejects the PR. Stop `.gitignore`'ing `pkg/`, or move it to a build-output directory that's clearly never the deployed artifact.

### P1 — `compute_intent_id` panics on bad `stake_commitment` length (`lib.rs:979–984`)
```rust
let stake_commitment: Option<[u8; 32]> = input.stake_commitment.map(|bytes| {
    bytes.try_into()
        .map_err(|_| JsError::new("stake_commitment must be exactly 32 bytes"))
        .unwrap()   // <-- this
});
```
The `.map_err(JsError::new).unwrap()` panics if the bytes aren't 32 long, because `unwrap` is called on the `Result<JsError, ...>` whose `Err` variant is the constructed error. With workspace `panic = unwind`, a panic in WASM leaves linear memory in an undefined state; the wasm-bindgen wrapper will throw, but subsequent calls into the same instance can observe corrupted globals (`thread_local!` RUNTIMES, allocator state). Attacker-influenced.
**Fix:** `let bytes: [u8; 32] = input.stake_commitment.map(|b| b.try_into().map_err(|_| JsError::new("…"))).transpose()?;`. Also set `[profile.release] panic = "abort"` in workspace `Cargo.toml` for `cdylib`-only crates targeting wasm — turns this class of bug into a clean trap.

### P1 — Global runtime registry has no caller isolation (`bindings.rs:22–52`)
```rust
thread_local! { static RUNTIMES: RefCell<Vec<Option<PyanaRuntime>>> = … }
```
`create_runtime` returns a `usize` index; `with_runtime(handle, …)` trusts any handle the JS caller hands in. In a WASM instance shared between several components (e.g. extension background-worker + a visualizer + a test harness in the same page), one caller can pass another caller's handle and read or mutate its world. With `web_accessible_resources` allowing any page to instantiate the WASM, a malicious page that knows the extension uses handle `0` can call into that runtime. (Today this is mitigated by separate instances per page, but it is an architectural footgun.)
**Fix:** require a per-runtime opaque token, return it as a `#[wasm_bindgen]`-exposed struct (move-only handle) instead of a primitive index, and use a `HashMap<TokenId, PyanaRuntime>` where `TokenId` is a 128-bit random.

### P1 — Deterministic agent privkeys with no warning at the binding (`runtime.rs:131–145`)
`create_agent` derives the agent's private key as `blake3_derive("pyana-wasm-agent-key", name || index)`. Knowing the agent name and index lets anyone reproduce the privkey. The source comments say "NOT secure for production", but the binding is exposed unchanged in `bindings.rs:208`. Production code or a misconfigured demo could mistakenly use this for real authorization.
**Fix:** rename the binding to `create_demo_agent` and require a feature flag (`features = ["demo-runtime"]`) for `bindings.rs`. The extension does not appear to call `create_agent`, but nothing prevents page-world JS from doing so.

### P1 — `verify_conservation_proof` is a stub but returns `valid: true` (`privacy.rs:292–319`)
```rust
let valid = !inputs.is_empty() && !outputs.is_empty();
```
A caller checking "did conservation hold?" will see `valid: true` for any non-empty input. The doc-comment says "for now, verify structural validity", but the binding name promises a proof check.
**Fix:** return `valid: false` (or a `not_implemented: true` flag) until the real homomorphic check exists, and rename the function `verify_conservation_inputs_present`.

### P1 — `verify_bearer_cap` has no signature, just a BLAKE3 recomputation (`privacy.rs:558–588`)
The "bearer token" is `blake3_derive(delegator_key || target_cell || action || expiry)`. To "verify" you recompute and compare. But the delegator key here is **public** (it's a cell ID / pubkey). So anyone who knows the public parameters can forge an identical token — there is no secret material involved. This is not a bearer capability; it's a content-addressable label.
**Fix:** make `create_bearer_cap` take a *delegator signing key* (privkey) and sign the binding; verification uses the corresponding pubkey. Or drop the "bearer" framing.

### P1 — `compose_proofs` doesn't compose proofs (`privacy.rs:766–817`)
The function takes proof JSON strings, BLAKE3-hashes them together, and returns the hash as `"composed_proof"`. It never deserializes or verifies the input proofs; it always returns `valid: true`. Any caller that trusts the boolean is trusting a hash-of-garbage.
**Fix:** at minimum deserialize and verify each input proof, returning the conjunction.

### P2 — 32-bit blinding factors break unlinkability (`lib.rs:377–380`, `lib.rs:1549–1551`, `lib.rs:1558–1561`)
```rust
let mut blinding_bytes = [0u8; 4];
getrandom::fill(&mut blinding_bytes).unwrap_or_default();
let blinding = BabyBear::new(u32::from_le_bytes(blinding_bytes));
```
Only 32 bits of blinding for fact commitments and ring-membership presentation tags. An attacker who collects O(2³²) observations can brute-force the blinding by trying every BabyBear value against the published commitment. Additionally, `unwrap_or_default()` means if `getrandom::fill` fails the blinding silently becomes **zero**, which fully de-blinds every subsequent presentation (the BabyBear field is ~31 bits, so this is essentially "blinding ∈ {0, …, p−1}" but degraded).
**Fix:** use the full field (`[0u8; 8]` -> reduce mod p) for blindings, and propagate the getrandom error as `JsError`.

### P2 — Secrets returned as `Vec<u8>` with no zeroization (`privacy.rs:64-69`, `lib.rs:1244-1259`, `lib.rs:1655`)
`derive_stealth_keys`, `schnorr_keygen`, `derive_keypair_from_mnemonic`, `check_stealth_ownership`, etc. construct `Vec<u8>` holding private keys, push them through `serde_wasm_bindgen::to_value` (which copies into a JS object), then `Drop`. The underlying `Vec<u8>` is freed without zeroization, leaving the secret in linear memory until reallocated. Since the same WASM instance handles further requests, residual key bytes are searchable from any subsequent call that can read its own scratch buffers (e.g., via a deliberately oversized JSON allocation that the allocator hands back the freed pages).
**Fix:** wrap secrets in `zeroize::Zeroizing<Vec<u8>>` (add `zeroize` to `wasm/Cargo.toml`; it's already in `workspace.dependencies`). For doubly-belt-and-suspenders, also zero the temporary stack arrays before drop.

### P2 — Workspace builds with `panic = "unwind"` (workspace `Cargo.toml`)
No `panic = "abort"` profile override. Combined with the ~5 panics from `unwrap_or_default` / `unwrap` on attacker-influenced inputs (P1 above, plus `lib.rs:983`, `runtime.rs:153`, `runtime.rs:458`), this means a malicious page can deliberately panic the WASM and then re-enter it. Re-entering after panic with `unwind` is UB-adjacent in Rust + wasm-bindgen contexts.
**Fix:** add to root `Cargo.toml`:
```toml
[profile.release]
panic = "abort"
[profile.dev]
panic = "abort"
```
…or scope per-target.

### P3 — Aspirational naming
- `verify_conservation_proof` doesn't verify a conservation proof (P1).
- `compose_proofs` doesn't compose proofs (P1).
- `prove_anonymous_membership` doesn't generate a STARK; comment admits "in a real system this would be a STARK" and emits a hand-computed proof-size estimate (`lib.rs:1573`).
- `derive_stealth_one_time_address` is the same body as `create_stealth_address` — fine, but the duplication suggests neither is the canonical name.
- `generate_range_proof` returns a BLAKE3 hash as the "proof" (`privacy.rs:386-389`) — comment says "placeholder for the full Bulletproof/STARK".
- `peer_exchange_with_proof` doesn't generate a proof — just BLAKE3-hashes the inputs (`privacy.rs:712-734`).

### P3 — `serde_json::to_vec(&proof).unwrap_or_default()` masks serialization failures (`lib.rs:241, 256, 408, 430, 1158, 1461`)
On serialization failure the returned `proof_size_bytes` becomes `0` and `proof_json` becomes `""`, with no error reported to the caller. Today none of these proof types can actually fail to serialize, but a future change adding non-string map keys would silently emit empty proofs that "verify" against themselves.

## Build artifact freshness

Critical drift (see P0 #3).
- src/ HEAD-of-tree has 73 `pub fn` items (29 bindings.rs + 24 lib.rs + 20 privacy.rs).
- pkg/pyana_wasm.d.ts has **43** exported functions, missing the entire stealth/encrypted-intent/bearer/factory/sovereign/proof-composition/facet API.
- pkg/ is gitignored; the deployed extension's CI/build script is presumably responsible for regeneration but there is no obvious enforcement.
- Several functions called by `extension/background.js` (`generate_mnemonic`, `validate_mnemonic`) exist neither in `wasm/pkg/` nor in `wasm/src/` — drift in both directions.
- `site/demo/pkg/` is even older (May 20) than `wasm/pkg/`.

## Open questions for the user

1. Who is responsible for rebuilding `wasm/pkg/`? Is there a CI step or is it manual? Is there a checksum file?
2. Is the broadcast mode of `seal_intent_body` intended to be encryption (then P0 #1 is a bug) or just a structured envelope with no confidentiality?
3. Should the WASM be in `web_accessible_resources` at all? If only the background worker needs it, drop the resource so pages can't pull it.
4. The extension's `background.js` calls `derive_keypair_from_mnemonic` with 3 args and reads `.public_key` / `.secret_key`; the Rust signature is 2 args returning a flat `Vec<u8>`. Which one is canonical?
5. Is `PyanaRuntime` (bindings.rs) meant to be background-only or page-exposed for demos? If demo-only, please feature-gate.
6. Add `zeroize` and `ed25519-dalek` (WASM-compatible feature set) to `wasm/Cargo.toml`?
