# starbridge-identity

The second starbridge-app — verifiable credentials, rebuilt as a thin
userspace shell over `pyana-credentials`.

See `src/lib.rs` for the in-source design notes. See
`../nameservice/README.md` for the pattern anchor.

## Stance

`apps/identity/` (audited 2026-05-24) re-invented credential primitives
badly: `Credential` had no signature field; the verifier trusted a
`verified: bool` set on the holder; selective disclosure truncated text
to 4 bytes. `PYANA-FLAWS-FROM-APPS.md` G31 promoted `bridge::present` to
the `pyana-credentials` crate. **This starbridge-app is the thin
userspace shell that survives once the credential primitive is correctly
factored out**: schemas, factory descriptor, turn-builders, inspector
wiring, web components.

All ZK heavy lifting (blinded merkle, predicate disclosure, ring proof,
non-revocation) lives in `pyana-credentials`. This app composes that
through cell-programs (`Effect::SetField` + `Effect::EmitEvent`), never
a domain-specific `Effect::IssueCredential` or
`Authorization::Unchecked` placeholder.

## What this crate exports

### Rust

- **`issuer_factory_descriptor()`** — `FactoryDescriptor` pinning the
  per-issuer sovereign cell's program VK, field constraints,
  state-constraint slot caveats, capability template, and per-epoch
  creation budget. Slot caveats:
  - `Immutable(SCHEMA_COMMITMENT_SLOT)` — schema cannot change after
    issuer-cell creation.
  - `MonotonicSequence(ISSUANCE_COUNTER_SLOT)` — issuance counter must
    increment by exactly one each issuance turn.
  - `Monotonic(REVOCATION_ROOT_SLOT)` — revocation is append-only.
  - `SenderAuthorized(PublicRoot { ISSUER_AUTH_ROOT_SLOT })` — only
    issuers in the published key-set can submit issuance turns.
- **Turn builders:**
  - `build_issue_credential_action(cclerk, issuer_cell, &credential, new_counter, revocation_root)`
  - `build_revoke_credential_action(cclerk, issuer_cell, credential_id, new_root)`
  - `build_present_credential_action(cclerk, holder_cell, &presentation)`
  - `build_verify_presentation_action(cclerk, verifier_cell, &presentation, &options)`
- **Re-exports** of the `pyana-credentials` API surface (`issue`,
  `present`, `present_anonymous`, `verify`, `revoke`, `Credential`,
  `Presentation`, `CredentialSchema`, `IssuerKeys`,
  `PresentationOptions`, `VerificationOptions`, `RevocationProof`,
  `PredicateRequest`, `Predicate`, etc.) so callers don't have to depend
  on the credentials crate directly.
- **Common schemas:** `kyc_schema()`, `gov_id_schema()`,
  `employment_schema()`.
- **`register(ctx)`** — `StarbridgeAppContext` mount that installs the
  factory descriptor and four inspector descriptors:
  - `pyana-credential` (read-only credential view)
  - `pyana-credential-issue-form` (issuer's UI)
  - `pyana-credential-present-form` (holder's selective-disclosure
    picker)
  - `pyana-credential-verifier` (verifier's UI)
- **Slot-layout constants:** `SCHEMA_COMMITMENT_SLOT`,
  `ISSUANCE_COUNTER_SLOT`, `REVOCATION_ROOT_SLOT`,
  `ISSUER_AUTH_ROOT_SLOT`.

### JavaScript

- `pages/index.html` — site fragment under `/starbridge-apps/identity/`.
- `pages/inspectors.js` — four custom elements
  (`<pyana-credential>`, `<pyana-credential-issue-form>`,
  `<pyana-credential-present-form>`, `<pyana-credential-verifier>`).
- `pages/turn-builders.js` — JS shim wrapping
  `window.pyana.signTurn(turnSpec)` with `issue_credential`,
  `revoke_credential`, `present_credential`, `verify_presentation`
  helpers that mirror the Rust turn-builders.

## How it composes with `pyana-credentials`

This crate **does not implement any cryptography**. Every credential
operation routes through `pyana-credentials` (which itself wraps
`pyana-bridge::present` per G31):

| starbridge-identity operation | pyana-credentials call |
|---|---|
| issue (`build_issue_credential_action`) | `pyana_credentials::issue(issuer, schema, holder_id, attrs, issued_at, not_after)` |
| present (`build_present_credential_action`) | `pyana_credentials::present(cred, request, options)` or `present_anonymous` for multi-show-unlinkable |
| verify (`build_verify_presentation_action`) | `pyana_credentials::verify(presentation, options)` |
| revoke (`build_revoke_credential_action`) | `pyana_credentials::revoke(registry, cred)` |

The userspace action wraps each operation in a cell-bound audit trail:

- `issue` → `SetField(ISSUANCE_COUNTER_SLOT)` + `SetField(REVOCATION_ROOT_SLOT)` +
  `EmitEvent("credential-issued", [id, holder_id, counter])`
- `revoke` → `SetField(REVOCATION_ROOT_SLOT)` +
  `EmitEvent("credential-revoked", [id, new_root])`
- `present` → `EmitEvent("credential-presented", [revealed_facts_commitment, holder_commitment, anon_flag])`
- `verify` → `EmitEvent("presentation-{accepted,rejected}", [revealed_facts_commitment, accept, predicate_count])`

No PII ever appears in cleartext on the cell — the events carry
commitments and ids only.

## Slot-caveat composition

The factory descriptor installs four state-constraints on every cell it
produces, picked from `cell/src/program.rs::StateConstraint`:

```rust
StateConstraint::Immutable          { index: SCHEMA_COMMITMENT_SLOT }
StateConstraint::MonotonicSequence  { seq_index: ISSUANCE_COUNTER_SLOT }
StateConstraint::Monotonic          { index: REVOCATION_ROOT_SLOT }
StateConstraint::SenderAuthorized   { set: AuthorizedSet::PublicRoot {
                                              set_root_index: ISSUER_AUTH_ROOT_SLOT } }
```

These are **perpetual** caveats baked into the child cell's
`CellProgram` — the executor evaluates them on every state-modifying
turn, not just at construction. Together they enforce:

- An issuer can never change which schema they issue under (schema is
  pinned at creation).
- An issuer can never replay an old issuance turn (counter
  strictly-increments).
- An issuer can never shrink their revocation set (Monotonic on the
  root slot).
- Only issuers in the published key-set can submit any state-modifying
  turn on the issuer cell.

## Compatibility with the in-browser PyanaRuntime + extension cclerk

`build_*_action` returns an `Action` carrying a real
`Authorization::Signature(..)` produced by the cclerk. That action is
what `cclerk.signTurn(turnSpec)` (the extension API surface — see
`../../extension/src/page.ts`) expects to wrap in a `Turn` for
submission. The in-browser `PyanaRuntime`
(`../../wasm/src/runtime.rs`) executes the resulting turn against the
same `pyana_turn::TurnExecutor` code-path that native CLIs use.

## Coexistence with `apps/identity/`

The legacy `apps/identity/` HTTP service stays until the audit cleans it
up (it's been flagged for removal). This crate is the canonical new
implementation. The dual-existence is documented in
`../../STARBRIDGE-APPS-PLAN.md` §2.

## Tests

```sh
cargo test -p starbridge-identity
```

Test coverage:

- **In-source unit tests** (`src/lib.rs`) — schema sanity, factory
  descriptor stability + state-constraint installation, turn-builder
  shape, signature non-emptiness, `register()` idempotence.
- **Integration tests** (`tests/credential_lifecycle.rs`):
  1. `roundtrip_issue_present_verify` — happy-path with selective
     disclosure + a predicate proof.
  2. `revoked_credential_rejected` — adversarial: revoked credentials
     fail verification, verifier action emits `presentation-rejected`.
  3. `forged_claims_rejected_at_issue` — adversarial: an attribute not
     in the schema is rejected at issuance time.
  4. `multi_show_unlinkability` — privacy: two anonymous presentations
     of the same credential produce different composition commitments
     (per `BOUNDARIES.md` §2.11).
  5. `verify_action_records_accept_event` — userspace composition:
     successful verification emits an accept event with the right
     payload shape.
  6. `verify_action_records_reject_event` — userspace composition:
     missing predicate produces a reject event.
  7. `schema_commitment_distinguishes_schemas` — schema commitments are
     well-distinguished across the three default schemas.

## Standalone check

```sh
cargo check -p starbridge-identity
cargo test  -p starbridge-identity
```

> **Note** — the workspace is currently mid-flight on the
> caveat-correctness lane in `cell/`, `turn/`, `circuit/`, `wire/`,
> `captp/`, `federation/`. Until that lane lands, `cargo check -p
> starbridge-identity` may fail upstream of this crate (e.g., in
> `pyana-turn`'s `Authorization::Custom` match coverage). The
> starbridge-identity sources are written against the **post-lane**
> shapes and the in-source unit tests + integration tests are correct
> against the documented APIs.
