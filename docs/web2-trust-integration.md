# Pyana for Web2: Incremental Trust Without Blockchain

## The Core Observation

Pyana's token layer (`pyana-token`) is macaroon/biscuit-backed capability auth. This is standard web2 technology. The ZK circuit layer, federation consensus, and on-chain interop are *optional upgrades* atop a foundation that works today with nothing more than HMAC keys and Ed25519 signatures.

## Pattern 1: Capability-First API Gateway

**Replace OAuth2/JWT with attenuable tokens. Ship this week.**

Mint a root token with `AgentCipherclerk::mint_token()`. The `Attenuation` struct lets any token holder narrow it further without contacting the issuer:

- Time-bound: `not_after` / `not_before` (session tokens that expire)
- Scope-narrow: `apps`, `services`, `features` (principle of least privilege)
- User-confine: `confine_user` (bind to identity at delegation time)
- Budget-cap: `BudgetSpec` (rate limiting baked into the token itself)

**Migration from OAuth2:** Your existing IdP mints pyana tokens instead of JWTs. Downstream services verify locally via `AuthToken::verify()` against an `AuthRequest` -- no token introspection endpoint, no shared Redis. Third-party caveats (`obtain_discharge()` in `sdk/src/discharge.rs`) replace OAuth's authorization code flow: the MFA gateway issues a discharge macaroon only after second-factor verification.

**What you gain over JWT:** Attenuation without re-issuance. A frontend can narrow its own token for a specific API call and hand that narrowed token to a third-party webhook -- the webhook cannot use it for anything beyond what it was narrowed to. JWTs cannot do this.

## Pattern 2: Verifiable Audit Trails

**Signed causal DAGs. No consensus required.**

The turn system (`pyana-turn`) already produces signed action forests with causal hash-pointers. Deploy this as an append-only audit log:

1. Each service signs its actions with Ed25519 (the cclerk identity key)
2. Each turn references its causal predecessors by hash (happened-before)
3. The `TurnReceipt` chain (`verify_receipt_chain()`) gives tamper-evidence

You get: non-repudiation (Ed25519 signatures), causal ordering (hash DAG), tamper detection (any gap breaks the chain). No blockchain -- just append-only signed logs replicated to N witnesses. The `SiloServer` already serves attested roots over TLS; point your audit consumers at it.

**Deployment:** Run one `SiloServer` per org. It maintains a BLAKE3 hash chain of events. Auditors verify the chain offline. When you later need BFT ordering, upgrade to a multi-node federation -- the wire protocol is identical.

## Pattern 3: Progressive Trust Escalation

Start at "web2 normal" and add trust properties as requirements emerge:

| Level | Infrastructure | What you get |
|-------|---------------|--------------|
| 0 | HMAC key + `pyana-token` | Attenuable bearer tokens, local verify |
| 1 | + Ed25519 identity | Signed audit trail, non-repudiation |
| 2 | + single `SiloServer` | Revocation list, non-membership proofs |
| 3 | + multi-node federation | BFT-ordered revocations, quorum attestation |
| 4 | + STARK circuit | Private presentation, selective disclosure |
| 5 | + Mina bridge | On-chain anchoring, cross-chain portability |

Each level is a separate crate dependency. Level 0-2 require zero cryptographic ceremony beyond key generation. Most production systems live at level 1-2 permanently.

## Pattern 4: Federated SSO Without Central Correlation

**The IdP issues attenuable credentials. Downstream services verify offline.**

Your enterprise IdP (`federation/src/node.rs`) issues a root token scoped to `organization(N)`. Each downstream service gets a delegated, narrowed copy. Unlike SAML/OIDC:

- The IdP is not contacted at login time (offline verification via `AuthToken::verify()`)
- No central correlation point -- the IdP cannot see which services the user accesses
- Selective disclosure (`VerificationMode::SelectiveDisclosure`) reveals only the facts the relying party needs

When the IdP needs to revoke, it submits to the federation (`SubmitRevocation` on the wire protocol). Services check non-membership against the attested root. Revocation propagates within one consensus round (~seconds), but verification never requires IdP liveness.

## Pattern 5: API Marketplace with Private Capabilities

**Capability tokens as API keys. Delegation without provider involvement.**

An API provider mints a capability token with `BudgetSpec` (rate limit baked in). The customer can:

- Subdivide their allocation: attenuate with a lower budget limit
- Delegate to subcontractors: narrow to specific services/actions
- Present privately: `VerificationMode::FullyPrivate` -- the provider verifies authorization without learning which customer entity is calling

No API key rotation dance. No "please create a sub-key in our dashboard." The token IS the delegation mechanism.

## The Trust Gradient (Summary)

```
Full trust          Semi-trust              Privacy              Trustless
   |                    |                      |                     |
bearer token    attenuable cap +         ZK presentation      on-chain verify
                signed audit trail       selective disclosure  Mina interop
   |                    |                      |                     |
 web2 normal     pyana without ZK         pyana with STARK     pyana + bridge
```

Most real deployments live between "semi-trust" and "privacy." The code in `pyana-token`, `pyana-sdk`, and `pyana-wire` covers that range today without touching the circuit crate.

## What You Can Build This Month

1. **API gateway middleware** that verifies `AuthToken` on every request, replacing JWT validation (~200 LOC, `pyana-token` + `pyana-sdk`)
2. **Delegation service** that lets users attenuate their own tokens for third-party integrations (~150 LOC, `AgentCipherclerk::attenuate()`)
3. **Audit log service** backed by signed turn receipts, serving a verifiable event stream (~400 LOC, `pyana-turn` + `pyana-wire`)
4. **Revocation server** using a single `SiloServer` with `DefaultRevocationHandler` (~100 LOC config)
5. **Third-party MFA gateway** that issues discharge macaroons after TOTP/WebAuthn verification (~300 LOC, `sdk/src/discharge.rs` pattern)

None of these require ZK proofs, federation consensus, or blockchain connectivity. They work with Ed25519 keys and HMAC secrets on commodity hardware.
