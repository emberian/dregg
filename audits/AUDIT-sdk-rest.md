# SDK audit (non-wallet) — `sdk/src/{lib,runtime,embed,captp_client,discharge,privacy,client,verify,full_turn_proof,committed_turn,discovery,names,mnemonic,error}.rs` + `examples/agent_demo.rs`

## Verdict

**OK-WITH-FOLLOWUPS** — no exploitable cryptographic break is reachable from untrusted input, and the security-critical paths (turn signing, presentation verification, sub-agent delegation, sturdy-ref enlivening) all use sealed/typed constructions. However, the SDK surface has a recurring pattern of **boolean-returning verifiers** that swallow error categories, and several **`pub` mutators on authority-bearing state** that elevate operator footguns into latent bug-classes. Three live AUDIT[P2] markers were verified; one new P2 (the `LiveRef` enliven trust model) is reported below.

## Summary

The SDK at this layer is mostly thin orchestration: `AgentRuntime` ties wallet+ledger+executor, `PyanaEngine` is the no-IO embedder, `captp_client` is local bookkeeping over the captp crate, and `verify.rs` / `privacy.rs` re-expose proof-system verifiers. Where signature and STARK verification happen, they delegate to crates audited elsewhere. The security checks present in `client.rs` (digest-bound responses, pinned federation roots, domain-separated revocation sigs, refuses-HTTPS-fallback-to-plaintext in `discharge.rs`) are notably defensive and well-commented.

The pattern that worries me is **what the SDK does NOT enforce at the API boundary**: callers of `verify_membership_proof`, `verify_selective_presentation`, `verify_anonymous_presentation`, and several `verify_*` helpers get a `bool` back. If a caller writes `if !engine.verify_membership_proof(p, &root) { reject() }` they cannot distinguish "decode failure" from "valid proof against wrong root". A second class of footguns: `PyanaEngine::ledger_mut`, `set_federation_root`, `executor_mut`, and `SubAgent::federation_id` are all writable post-construction by anyone holding `&mut`. The current code documents these in AUDIT[P2] comments and they're not exploitable across a trust boundary (you already need `&mut PyanaEngine` to use them), but they are landmines for refactors.

The `agent_demo.rs` example uses the correct typed `LocalDelegation` path (via `runtime.spawn_sub_agent` → `make_local_delegation`), not the unsafe `DelegatedToken { delegator_signature: None }` pattern. The unsafe pattern is not constructible anywhere in the SDK surface — `make_local_delegation` is `pub(crate)`, and `DelegatedToken::delegator_signature` is a non-Option `Signature`.

---

## Findings by severity

### P0 — none

### P1 — none

### P2

**P2-1.  `LiveRef::enliven` accepts arbitrary `permissions` with no peer attestation** (`sdk/src/captp_client.rs:306-331`)
The `enliven` API takes `permissions: AuthRequired` as an argument and stores them on the returned `LiveRef`. The doc says "in a real deployment, this comes from the remote's response to our enliven request" but the SDK does not enforce that any handoff/swiss-table proof is checked. A caller who threads attacker-supplied `AuthRequired` into this method gets a `LiveRef` that *claims* whatever permissions the caller passed. The downstream `send` / `pipeline` calls don't re-check. *Fix*: split into `enliven_with_proof(uri, handoff_cert)` (verifies introducer signature) and `enliven_local(uri, permissions)` (clearly marked test-only). At minimum, document this as `# Safety` and stop calling the parameter "obtained from the remote's response" in the docstring when in fact it's just a caller-supplied claim.

**P2-2.  `SubAgent` `pub federation_id` (existing AUDIT marker preserved)** (`sdk/src/runtime.rs:469-498`)
Confirmed: the AUDIT[P2] comment is in place. `federation_id: [u8; 32]` is `pub` and is used in `SubAgent::execute` at line 553 as the signing-message domain separator. A holder of `&mut SubAgent` can rewrite it post-construction. Same fix as recommended in the comment: make all `SubAgent` fields private with read-only accessors. The fields `wallet`, `cell_id`, `token`, `parent`, `domain` are also `pub` and should be moved behind accessors for the same reason.

**P2-3.  `PyanaEngine::verify_membership_proof` returns `bool` (existing AUDIT marker preserved)** (`sdk/src/embed.rs:442-469`)
Confirmed: marker is in place. Same pattern reappears in:
  - `privacy::verify_anonymous_presentation` (`privacy.rs:662`) — returns `bool`, silently fails on missing `real_stark_proof`, on wrong AIR name, on missing federation root, on STARK verify failure. All four error categories collapse to `false`.
  - `verify::verify_selective_presentation` and `verify_disclosure_presentation` (`verify.rs:283,310`) — return `bool`, and the `_ => false` arm makes a non-`Selective` variant indistinguishable from a failed commitment check.
  - `embed::WireCodec::process_message` PresentToken handler (`embed.rs:737`) — `.unwrap_or(false)` swallows the verifier's error category before reporting "proof verification failed".
*Fix*: introduce a `VerifyOutcome` (Ok / DecodeError / StarkInvalid / RootMismatch / FreshnessExpired / WrongAir / NoStark) enum and return it from these methods. Keep a `bool`-returning convenience wrapper if needed.

**P2-4.  `PyanaEngine::ledger_mut`, `executor_mut`, `set_federation_root` (existing AUDIT markers preserved)** (`sdk/src/embed.rs:566-648`)
Confirmed: markers are in place. The engine exposes raw `&mut Ledger`, raw `&mut TurnExecutor`, and an unauthenticated `set_federation_root`. As noted in the in-source AUDIT comment, callers with `&mut PyanaEngine` already have full process trust, but a monotonic version on `federation_root` (and a `downgrade_federation_root` method that requires an explicit "I know this is going backwards" call) would prevent accidental rollback of the public input that every membership STARK is verified against. Severity P2 — operator-only.

**P2-5.  `EngineConfig` accepts `timestamp: 0` even outside `for_testing()`** (`sdk/src/embed.rs:153-198`)
`EngineConfig::new(timestamp: i64)` does not reject `timestamp <= 0`. The doc warns "a timestamp of 0 will cause all verification to fail silently", and `prove_presentation` does refuse to mint with timestamp 0 (line 337), but `verify_presentation_against` happily verifies with `now = 0` and `max_proof_age_secs > 0` (the freshness window then admits everything from epoch). *Fix*: `EngineConfig::new` should reject `<= 0`; the `for_testing()` constructor remains the documented escape hatch.

**P2-6.  `discharge.rs` accepts an unencrypted (HTTP) gateway for ticket+proof submission** (`sdk/src/discharge.rs:66-79`)
The TLS-required check is correct (P1 regression test on line 264 confirms HTTPS won't fall back), but HTTP is still allowed: an attacker on-path can read the ticket and (if present) the ZK proof in the request body, and read/forge the discharge in the response. This is by-design per the comment ("if plaintext is acceptable for your threat model") but the SDK should make the unsafe-by-design nature impossible to miss: rename to `obtain_discharge_insecure_http` and gate behind a feature flag, or refuse plaintext unless the caller passes an explicit `AcceptPlaintext` marker. Severity P2 because the caller is opting in by passing an `http://` URL.

### P3

**P3-1.  `discovery.rs` PIR query uses up to 50ms random delay** (`sdk/src/discovery.rs:249-254`)
The "small random delay" between metadata fetch and query is a 0–49ms uniform delay. This is far below typical network jitter and provides essentially no timing-correlation protection from a passive observer who can see both the metadata fetch and the query. Either remove the delay (it's misleading), or bring it up to a meaningful window (a few hundred ms with cover traffic) and document the actual privacy guarantee.

**P3-2.  `verify::verify_authorization_proof` infers the circuit by AIR name with a silent fallback** (`sdk/src/verify.rs:110-114`)
`circuit_for_air_name(&stark_proof.air_name).unwrap_or_else(|| ...merkle_poseidon2_circuit())` — if a future AIR name is added without updating the registry, the verifier silently dispatches to the wrong circuit and likely returns `Ok(false)`. Prefer `.ok_or(SdkError::Wire(format!("unknown AIR: {}", stark_proof.air_name)))`. Same pattern at `verify.rs:222`.

**P3-3.  `committed_turn.rs` builds with `getrandom::fill(...).expect("getrandom failed")` in three places** (`sdk/src/committed_turn.rs:121,190,192`)
Builder methods (not constructors) panic if the system RNG fails. These are called from user code paths that *might* be inside a long-lived service. Prefer propagating `SdkError`. Not exploitable from untrusted input but a crash-on-RNG-failure surface.

**P3-4.  `mnemonic.rs:274` and `mnemonic.rs:47` use `expect("...")` on cryptographic primitives**
`pbkdf2::pbkdf2::<HmacSha512>(...)` and `getrandom::fill(...)` panics in `mnemonic_to_seed_bip39_compat` and `generate_mnemonic`. The HMAC `.expect` claim is correct (HMAC accepts any key length), but `generate_mnemonic` panicking on RNG failure could be propagated as `Result<String, MnemonicError>`. Low impact.

**P3-5.  `runtime.rs` initial sub-agent cell balance hard-coded to 100k computrons; parent cell hard-coded to 1M** (`sdk/src/runtime.rs:117-118, 427`)
These are policy values baked into a library. An application that wants a different policy has to bypass `AgentRuntime::new` entirely. Promote to `RuntimeConfig` with explicit defaults.

**P3-6.  `captp_client.rs` `create_handoff` always uses `self.config.federation_id` as both introducer and target** (`captp_client.rs:386-387`)
Comment says "// target is also us (local delegation)" but the API takes no `target_federation` parameter, so a cross-federation handoff (the actual intended use case for handoff certificates) is not buildable through this API. Either document that this is local-only (rename to `create_local_handoff`), or take an explicit `target_federation: GroupId` argument.

**P3-7.  `runtime.rs:107` swallows poisoned-lock panic** (and similar at 144-147, 240-241, 267-268, 401-402, 405)
The pattern `unwrap_or_else(|e| e.into_inner())` is documented as deliberate. The trade-off (continue with possibly-inconsistent state vs. crash) is reasonable for a library, but every poisoning is also a *signal that something panicked while holding the lock*. There is no telemetry hook on the recovery path. Add a `tracing::error!` on the recovery branch.

**P3-8.  `names.rs:502, 544, 357` unwrap on TLD parsing and JSON serialization**
`segments.last().unwrap()` after a `len() < 2` check is fine, but the pattern is fragile. `serde_json::to_string(self).expect(...)` is correct for non-cyclic structures, but a future addition of a `serde(skip_serializing_if=...)` predicate that panics could surface here.

---

## API surface review (selected)

### `lib.rs` — re-exports
- All re-exports are explicit (no `pub use ...::*`). Good.
- Re-exports `pyana_bridge::present::verify_presentation` under `#[allow(deprecated)]` — flag for cleanup.
- Re-exports `LocalDelegation` at crate root — this is the right type to expose for receiver-side `receive_local_delegation` callers, but the *constructor* is `pub(crate)` so external callers cannot manufacture them. Good.
- `DelegatedToken` and `DelegationAuthority` are re-exported. `DelegationAuthority::Open` exists for backward compatibility (the wallet warns on use). The example does NOT use `Open`. Good.

### `runtime.rs`
| `pub fn` | Trust class |
|---|---|
| `AgentRuntime::new` / `new_simple` / `with_ledger` | Caller-trusted; mutates ledger |
| `AgentRuntime::execute` / `execute_turn` | Caller-trusted; signs with wallet |
| `AgentRuntime::spawn_sub_agent` | Caller-trusted; only path to construct `SubAgent` |
| `AgentRuntime::set_budget_gate` | Operator-only |
| `AgentRuntime::wallet/ledger/cell_id/domain/nonce` | Read-only accessors |
| `SubAgent::execute` | Self-trusted (sub-agent has its own wallet/key) |
| `SubAgent::can_authorize` | Pure |
| `SubAgent::public_key/nonce` | Read-only |

### `embed.rs`
| `pub fn` | Trust class |
|---|---|
| `PyanaEngine::new` / `with_ledger` | Constructor |
| `execute_turn` / `execute_turn_bytes` / `validate_turn` / `estimate_cost` | Caller-trusted; pure on input bytes |
| `prove_presentation` | Caller holds the root key |
| `verify_presentation_bytes` / `verify_presentation_against` | **Returns Result<bool> — see P2-3** |
| `verify_membership_proof` | **Returns bare bool — see P2-3** |
| `mint_token` / `attenuate_token` | Caller holds the root key |
| `state_snapshot` / `load_state` | Snapshot integrity is checked (BLAKE3 trailer); good |
| `ledger_mut` / `executor_mut` / `set_federation_root` | **Operator-only authority surface — see P2-4** |

### `captp_client.rs`
| `pub fn` | Trust class |
|---|---|
| `CapTpClient::new` | Constructor |
| `export_sturdy_ref` / `revoke_export` | Caller-trusted (allocates swiss numbers) |
| `enliven` / `enliven_uri` | **Caller supplies `permissions` claim — see P2-1** |
| `create_handoff` | Caller holds signing_key; introducer sig is valid |
| `pipeline` / `pipeline_to` | Pure on input |
| `swiss_table_mut` | Operator-only |
| `LiveRef::send` / `pipeline` / `release` | Local bookkeeping |

### `verify.rs`
| `pub fn` | Trust class |
|---|---|
| `verify_authorization_proof` | Pure; returns `Result<bool>` — correctly enforces composition commitment + action binding (regression-tested P1-1) |
| `verify_selective_disclosure` | Pure; returns `Result<bool>` — correctly compares PI commitment against recomputed (regression-tested P0) |
| `verify_selective_presentation` / `verify_disclosure_presentation` | Pure; **return bare bool — see P2-3** |
| `verify_validated_ivc_proof` | Pure; returns `Result<bool>` |
| `verify_production` | Pure; returns `Result<VerifiedProof, _>` |
| `verify_any_tier` | Gated on `cfg(any(test, feature = "dev"))` — good |
| `verify_committed_threshold` | Pure; uses only first 4 bytes of 32-byte commitment input — this is documented but a long-term footgun (first 4 bytes of a BLAKE3 hash are not a cryptographic commitment to the input; if these "commitments" come from a hash, the test is sound, but if they come from raw u32 values right-padded to 32 bytes the inputs are deceptively wide). Worth a doc-only clarification. |
| `build_federation_tree` | Pure; sorts leaves before tree construction (deterministic) |

### `discharge.rs`
| `pub fn` | Trust class |
|---|---|
| `obtain_discharge` | **Plaintext-allowed by default for HTTP URLs — see P2-6** |
| `extract_third_party_tickets` | Pure on token bytes |
| `authorize_with_discharges` | Calls `obtain_discharge` for each 3P caveat |

### `privacy.rs`
All four `AgentWallet` methods (`authorize_anonymously`, `create_private_note`, `transfer_note_privately`, `prove_predicate_unlinkable`, `prove_not_revoked`, `prove_not_revoked_accumulator`) are pure crypto on wallet-held secrets. The `verify_*` helpers are bare-bool — see P2-3.

A subtle correctness note in `prove_predicate_unlinkable` (`privacy.rs:407-411`): the blinding is `u32::from_le_bytes(buf) % BABYBEAR_P`. This is a non-uniform sample (modular bias) because `2^32` is not a multiple of `BABYBEAR_P ≈ 2^31`. The bias is small but real; for unlinkability proofs where the blinding is the *only* source of unlinkability, prefer rejection sampling. Severity P3.

---

## Cross-cutting patterns

**Aspirational naming check** — scanned for `Verified*` / `Signed*` / `Authenticated*` / `Sealed*` / `Encrypted*` / `Authorized*` types in the audited files:
- `PresentationResult { accepted: bool }` — name is honest (just "result", not "Verified")
- `RevocationStatus::NotRevoked { root, height }` vs `Unverified` — *good* distinction. The doc comment explicitly says "Callers MUST NOT treat this as equivalent to `NotRevoked`."
- `VerifiedProof` (re-exported from `pyana_circuit`) — out of scope, but the call site at `verify::verify_production` constructs one *only* after `verify_authorization_proof` returns `true`. Good.
- `AnonymousPresentation { proof, presentation_tag }` — proves anonymity only if the underlying STARK uses `BLINDED_MERKLE_AIR_NAME`. The verifier at `privacy.rs:682` correctly rejects other AIRs. Good.
- No `SignedX` types found that don't carry a `Signature` field.
- No `EncryptedX` found that holds plaintext.

**Missing documentation**: most `pub fn`s in `captp_client.rs` and `runtime.rs` lack a `# Trust` section. Given the doc-comment standard set elsewhere (e.g., `RevocationStatus::Unverified`'s `SECURITY:` block), this is achievable as a follow-up doc pass.

**`unwrap()` on attacker-controlled data**: none found. The `unwrap_or` / `unwrap_or_default` patterns I checked (`client.rs:285,373`: `proof.issuer_proof_bytes().unwrap_or_default()`) all default to empty bytes which produce a failed verification downstream, not a panic. The `unwrap_or(BabyBear::ZERO)` in `full_turn_proof.rs:537,542,579` is for cross-proof PI binding, where a zero value would fail the equality check.

**Bounded allocations**: scanned for `Vec::with_capacity` on length-prefixed deserialization:
- `discovery.rs:73` — `Vec::with_capacity(64)` for `encrypted_note` is a fixed constant. OK.
- `committed_turn.rs:208` — same, constant 64. OK.
- `verify.rs:568` — `Vec::with_capacity(current_level.len() / 2)` where `current_level` is the *caller-controlled* `member_keys`. This is `build_federation_tree`, called by trusted verifier setup with known input. OK.
- `client.rs:544` — `Vec::with_capacity(...len() + token_id.len())` where `token_id` is wallet-local. OK.
- No attacker-controlled length-prefix → `with_capacity` patterns found.

---

## Open questions for the user

1. **`PyanaEngine::ledger_mut` and `executor_mut`**: are these *required* for any external embedder, or can they be removed entirely? If embedders only need them for tests, gate behind `#[cfg(any(test, feature = "test-utils"))]`.
2. **`LiveRef::enliven` permissions**: should there be a real "verify swiss number against remote" path in the SDK, or is this expected to always be done at a higher layer (e.g., `app-framework`)? If higher, the SDK API shape should make that mandatory.
3. **`discharge.rs` plaintext HTTP**: is there any production user who relies on `http://` gateways? If not, remove the plaintext path entirely.
4. **`SubAgent` field privacy**: are any external callers (CLI, app-framework, apps/*) actually reading `SubAgent.token` / `.federation_id` directly? If they're going through accessors anyway, the `pub`s can be removed without churn.
5. **`verify_*` bool return**: which call sites depend on the bool? An eager `Result<(), VerifyError>` migration would surface failure categories into logs but breaks callers. Worth a coordinated pass.
6. **`discovery.rs:249` 50ms jitter**: was this an intentional minimum, or leftover from prototyping? If intentional, please document the threat model it addresses.
