# starbridge-domains — BYO custom domains as a dregg-native cell

**A domain binding is a cell.** Point your own DNS domain (`blog.acme.io`) at a
published site, with the standard ACME-style proof-of-DNS-control before any traffic
— or any certificate — is routed. This is the dual of the sibling
[`starbridge-nameservice`](../nameservice): a *federation name* is granted inside a
federation; a *custom domain* is proven against live DNS.

```text
  REGISTER                 BIND (cap-gated)             VERIFY                 ROUTE / CERT
  ───────────              ────────────────             ──────────             ─────────────
  own the domain           point at a site +            a DnsResolver          gateway Host -> site
  (DOMAIN, OWNER)          issue a challenge nonce       proves control          site_for_host()
   WriteOnce               WriteOnce(CHALLENGE_NONCE)     Monotonic(VERIFIED_SEQ) is_verified()
```

## The four axes (the unified starbridge-app template)

1. **The verified core** — [`domain_factory_descriptor`] + [`domain_cell_program`]
   (`src/lib.rs`): a per-domain sovereign cell whose committed slots are
   `{domain, site, owner, verification_state, challenge_nonce, verified_seq}`. The
   domain / owner / challenge-nonce are sealed (`WriteOnce`) and the verification is
   one-way (`Monotonic` on `verification_state` + `verified_seq`) — so a rebind of the
   proven challenge, an owner takeover, and an un-verify are all real executor
   refusals on the born cell.
2. **The service `invoke()` front door** (`src/service.rs`) — a typed
   `InterfaceDescriptor` over `register` / `bind` / `verify` (replayable, Signature)
   and `resolve` (the serviced OFE read seam).
3. **The deos-view card** (`src/card.rs`) — the binding surface as a renderer-
   independent `deos.ui.*` view-tree (pure `serde_json`).
4. **The composed `DeosApp`** ([`domain_app`] / [`register_deos`]) — the affordances
   `register` / `bind` / gated `verify` / `resolve`, published into the web-of-cells.

## Two enforcement surfaces (both real)

- **The bind cap** (`src/cap.rs`) — WHO may bind. A `DomainCap` presents a `dregg-auth`
  credential that must verify under the registry's trusted root as granting the
  binding authority for the domain ([`cap::verify_bind_authority`]). A forged /
  wrong-root / wrong-domain credential is refused; the binding's owner is the
  credential's pinned subject (no takeover). By `Credential::attenuate`'s no-amplify
  property, a delegate confined to one domain cannot widen back to all.
- **The domain cell invariants** — the factory's `state_constraints`, re-enforced by
  the executor on every touching turn.

## The DNS seam + the gateway reads

Verification is driven through the injected [`dns::DnsResolver`] trait — a
deterministic [`dns::MockDns`] in tests, a host-wired real DNS client in prod (the
sync trait is the seam a production resolver implements over a live client; this crate
ships no live client, so it stays portable and dependency-light).
[`registry::DomainRegistry::site_for_host`] maps an inbound `Host` -> its bound site
*only when verified*, and [`registry::DomainRegistry::is_verified`] is what a gateway's
on-demand-TLS `ask` consults.

## Layout

| file | axis |
|------|------|
| `src/lib.rs` | verified core: slots, program, factory, mirror/seed, effect templates, DeosApp, mount |
| `src/cap.rs` | the bind cap: `dregg-auth` credential mint + verify |
| `src/dns.rs` | the DNS seam: `DnsResolver` + `MockDns`, domain validity, challenge nonce |
| `src/registry.rs` | the control plane: bind / verify / site_for_host / is_verified |
| `src/service.rs` | the `invoke()` front door |
| `src/card.rs` | the deos-view card |
| `tests/domain_lifecycle.rs` | end-to-end: cap-gated bind, unverified doesn't resolve, wrong nonce refused, flips once |

## Honest gaps

The routing plane's source of truth is the pure serializable `DomainBinding` record
(the plaintext `domain -> site` map a gateway needs); the cell mirrors its commitments
into scalar slots (the executor-enforced invariants) via [`mirror_binding`]. The
`WriteOnce`/`Monotonic` teeth and the cap-verify are real. A production lane threads
the DNS challenge issuance itself through a witnessed-predicate program (so an
off-challenge verify is an executor refusal, not just a registry check) — this models
the shape.

This crate supersedes a prior imperative custom-domains module.
