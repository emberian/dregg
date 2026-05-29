# Bringing Biscuit & Macaroon First-Class into Object-Calling Semantics

**Status:** design / queued lane (build on Wave-2 Lane 2 + Lane 3; do NOT start until `circuit/` + `cell/predicate.rs` quiesce).
**Author:** autonomous design pass, 2026-05-29.

## Problem

dregg has **two parallel authorization systems that never touch each other**:

1. **Object-capability invocation (the live executor path).** A turn/CapTP call is authorized by `turn::action::Authorization` — `Signature`, `Proof` (ZK, bound to action+resource), `Breadstuff([u8;32])` (a capability-token *hash*), `Bearer(BearerCapProof)` (delegation-chain proof), `CapTpDelivered` (handoff cert), `Custom(WitnessedPredicate)` — plus the cell c-list / capability tree (grant/attenuate/revoke) and `StateConstraint` invariants.
2. **The credential library (`dregg-token` / `dregg-macaroon`).** A coherent, well-tested (152 + 40 `#[test]`) dual-backend `AuthToken`: **Macaroon** (HMAC, symmetric, hot-path) + **Biscuit** (Ed25519/P-256 + Datalog, *offline public-key verification*, delegated attenuation), with third-party caveats + a runnable discharge-gateway. Used by `sdk`/`bridge`/`credentials`/`wasm` for **service/RPC/guest-API auth** — and referenced **zero times** in `cell`/`turn`/`captp`.

Even `Authorization::Breadstuff` (the namesake) is only a capability *hash*, not a caveat-bearing token. So the object-capability layer **reinvents** attenuation/delegation/revocation that the macaroon/biscuit layer already does well — and the genuinely decentralized credential (Biscuit: mint, attenuate, delegate, verify offline with just a root pubkey) is **not** what authorizes object calls.

## Goal

Make a Biscuit/Macaroon token a **first-class object-calling credential**: a turn or CapTP invocation can be authorized by *presenting a token* whose caveats/Datalog are verified, **deterministically and on-chain**, against *this* call's (action, resource, effects, nonce, federation). Unify "exercise a capability" with "present a credential."

## Core design

### Split of responsibilities (honest about the crypto)
- **Biscuit = the decentralized, cross-domain object-calling credential.** Public-key verification means *any* executor/federation can verify it offline with the granting authority's root pubkey. Datalog encodes the authorization policy + the delegation chain. This is the primary first-class path.
- **Macaroon = the intra-authority / fast path.** HMAC verification needs the root *secret*, so it is only sound where the verifier legitimately holds it: **a cell minting caveated tokens against its own (deterministically derived) key, verified when a call targets that cell.** Third-party caveats + the discharge gateway give it cross-domain delegation without putting any secret in consensus.
- **Hard rule: no global/shared secret ever enters consensus.** Cross-domain ⇒ Biscuit (public). Symmetric macaroon stays cell-scoped or service-scoped.

### New first-class variant
```rust
// turn::action::Authorization
Token {
    /// Self-describing encoded credential (`eb2_` biscuit / `em2_` macaroon).
    encoded: Vec<u8>,
    /// How the verifier resolves the root key:
    ///  - Biscuit: a granting-authority pubkey (named in a capability grant or
    ///    the target cell's permissions), verified offline.
    ///  - Macaroon: the target cell's key handle (cell-derived secret).
    key_ref: TokenKeyRef,
    /// Optional discharge macaroons satisfying third-party caveats
    /// (each itself verifiable against a known gateway pubkey).
    discharges: Vec<Vec<u8>>,
}
```
First-class (a peer of `Bearer`/`CapTpDelivered`), not smuggled through `Custom` — but it **reuses** the `Custom`/`WitnessedPredicate` registry machinery for the verifier plumbing (so it builds directly on Wave-2 Lane 3's hardened registry).

### Executor verification flow (deterministic)
On a turn whose action carries `Authorization::Token`, a new `turn`-side `TokenAuthorityVerifier`:
1. **Detect format** from the prefix (`TokenFormat::detect`).
2. **Resolve the root key** via `key_ref`: biscuit → the granting pubkey (must be one the target cell's permissions/grant authorizes); macaroon → the target cell's derived key.
3. **Cryptographically verify** the token (`AuthToken::verify`) + every discharge against its gateway pubkey.
4. **Bind to THIS call.** Construct a `dregg_token::AuthRequest` from the Action — `{action: method symbol, resource: target cell id / app_id, effects: the action's effect set, nonce, federation_id, block_height}` — and evaluate the token's caveats / Datalog against it (`AuthToken::can_authorize` / `datalog_verify::verify_token_datalog`). Replay against a different call fails because the binding facts differ (mirrors `Proof`'s bound_action/bound_resource and `CapTpDelivered`'s signing message).
5. **Capability cover.** The verified token's granted authority (action set + effect mask + permissions) MUST be ≥ what the cell's `AuthRequired`/`Permissions`/`StateConstraint` require for that method. The token *is* the authority — it satisfies (or augments) the c-list check, it does not bypass it.
6. **Revocation, on-chain.** Check the token's revocation id (and each delegation-chain link) against the federation revocation accumulator — the SAME structure the `Renounced`/`NonMembership` predicates and `token::revocation::AttestedRevocationRoot` use. (Reuse Lane 3's hardened, non-forgeable membership binding.)
7. Yield the same accept/reject + granted-capability shape the other `Authorization` arms produce.

**Determinism constraints (non-negotiable for consensus):**
- No wall-clock. Expiry/temporal caveats reference **block height**, supplied as a Datalog fact by the executor (bridge to the existing `TemporalGate`/`FieldGteHeight` model).
- Verification must be a pure function of (token, discharges, action, ledger-resolvable keys/roots, block height). No network during verify (discharges are *presented*, not fetched).

### Capability operations ARE token operations (the unification)
- **Grant** (`Effect::GrantCapability`) ⇒ mint/append a Biscuit delegation block to the grantee's pubkey scoping target+method+effects+caveats (or a macaroon for the cell-local case).
- **Attenuate** (`Effect::AttenuateCapability`) ⇒ append a *narrowing* block/caveat — monotonic, which the `StateConstraint::Monotonic`/manifest already cares about; the AIR can even bind that attenuation is strictly-narrowing.
- **Revoke** ⇒ insert the token/chain id into the revocation root.
- The capability tree becomes a **view over the biscuit delegation graph**; "exercise capability X" = "present the biscuit that delegates X, as `Authorization::Token`."

### Datalog as the cell authorization policy language
A cell program's per-method authorization (its `AuthRequired`/`Permissions`/relevant `StateConstraint`s) is expressible as the Datalog policy the biscuit authorizer checks (biscuit's native model; `evaluate_datalog` + `token::datalog_verify` already exist). **Do not invent a third predicate vocabulary** — derive Datalog facts from the same `AuthRequest`/action the `StateConstraint` model consumes, so the two stay coherent.

### CapTP: decentralized remote object-calling
`CapTpDelivered` today carries a handoff certificate. Extend the CapTP path so a **Biscuit can be the delegated authority** in (or alongside) a handoff: the receiving federation verifies it offline with the introducer's root pubkey + Datalog, instead of relying solely on a per-introducer signature. This is the genuinely decentralized sturdyref-with-caveats story.

## Phasing (so it lands sound, not big-bang)
1. **P1 — read path.** `Authorization::Token` variant + `TokenAuthorityVerifier` for **Biscuit only** (public verify + Datalog + AuthRequest binding + capability cover + block-height determinism). Adversarial tests: replay against a different action rejected; insufficient-capability rejected; expired-by-height rejected; tampered token rejected.
2. **P2 — revocation + 3p discharge.** Wire the on-chain revocation check (reuse Lane 3 membership) + third-party-caveat discharge verification against gateway pubkeys. Test: revoked token rejected; missing/forged discharge rejected.
3. **P3 — macaroon (cell-scoped).** Cell-key-derived macaroon verification for the intra-authority fast path. Test: a cell-minted caveated macaroon authorizes a call on that cell; cross-cell macaroon (no held secret) rejected.
4. **P4 — capability-tree unification.** `GrantCapability`/`AttenuateCapability`/revoke emit/append/revoke real biscuit blocks; "exercise" presents the token. Differential test vs the existing c-list semantics (same allow/deny decisions).
5. **P5 — CapTP biscuit authority.** Biscuit as delegated authority in handoff.

## Honest hard parts / open questions
- **Determinism of biscuit Datalog**: must confirm the Datalog evaluator is fully deterministic + has no time/randomness facts other than executor-supplied block height. (`token::datalog_verify` has 49 tests — audit them for nondeterminism before P1.)
- **Key resolution policy**: *which* pubkeys a cell trusts as granting authorities must itself be a capability/permission decision (avoid a global trust anchor). Likely a per-cell "trusted issuer" set in the program.
- **Macaroon-in-consensus**: only ever cell-scoped (verifier holds the secret legitimately). Cross-domain macaroon authority must route through biscuit or a discharge, never a shared HMAC secret.
- **Caveat ↔ StateConstraint coherence**: P1 reuses `AuthRequest` as the bridge; longer-term, decide whether StateConstraint and biscuit caveats converge on one surface or stay two coherent layers (one for *authorization*, one for *state invariants*). Recommend: keep StateConstraint for post-effect state invariants, Token/Datalog for pre-effect authorization — clean separation, shared `AuthRequest`.
- **Revocation latency/cost**: on-chain non-membership per call is not free; reuse the accumulator + Lane 3's binding, batch where possible.

## Why this is the right shape
It makes the *existing, tested* decentralized credential (Biscuit + third-party-caveat discharge) the actual object-calling authority, instead of a parallel reinvention; it's first-class (`Authorization::Token`) yet reuses the hardened `Custom`/predicate registry and the revocation/membership work; it keeps consensus deterministic and secret-free; and it unifies grant/attenuate/revoke with biscuit delegation so there's one capability story, not two.
