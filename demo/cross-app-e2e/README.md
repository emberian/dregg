# cross-app-e2e — Composition demo for the four starbridge-apps

This demo proves that pyana's substrate **composes**: the four anchor
starbridge-apps (`identity`, `nameservice`, `governed-namespace`,
`subscription`) interoperate at the cell-program /
`WitnessedPredicate` / `AuthorizedSet::CredentialSet` level, with each
step exercising a specific kernel primitive.

## The story arc

Four agents drive a single end-to-end narrative through the four apps:

| Agent  | Role                                                       |
|--------|------------------------------------------------------------|
| Alice  | identity-issuer cell operator; issues credentials          |
| Bob    | credential holder; registers `bob.dev` and mounts a cell  |
| Carol  | bounty poster; subscribes Bob to bounty events            |
| Dan    | worker; claims and fulfills the bounty                    |

### Steps

1. **Alice creates a credential issuer cell** (`identity` factory) and
   issues a `verified-developer-v1` credential to Bob. The
   `issuer_factory_descriptor` pins the schema commitment and authorized
   issuer set; the issuance turn carries the credential id.
   - Primitives: `issuer_factory_descriptor`, `schema_commitment`,
     `MonotonicSequence(ISSUANCE_COUNTER_SLOT)`,
     `SenderAuthorized(PublicRoot { ISSUER_AUTH_ROOT_SLOT })`.

2. **Bob registers `bob.dev` in the nameservice's identity-attested
   tier**, presenting his credential. The registration carries a
   `WitnessedPredicate::BlindedSet` whose commitment is
   `AuthorizedSet::credential_set_commitment(alice_issuer_cell,
   verified_developer_schema_id)`. The cell program's
   `identity_attested_tier_constraint` rejects any registration without
   a matching credential.
   - Primitives: `AuthorizedSet::CredentialSet`,
     `build_register_with_credential_action`,
     `identity_attested_tier_constraint`,
     `WitnessedPredicateKind::BlindedSet`.

3. **Bob mounts his cell at `pyana://bob.dev`** via a governed-namespace
   `register_service` turn. The mount carries the nameservice's
   canonical resolve target (`blake3("pyana://cell/bob-cell-id")`) so
   downstream `pyana_dfa::Router` walks against the live route table
   resolve to Bob's actual cell.
   - Primitives: `register_nameservice_route_action`, the namespace's
     `register_service` case freezing every governance slot.

4. **Carol posts a bounty** ("fix CVE-2025-1234") and creates a
   subscription cell. Bob subscribes — his pubkey is added to the
   subscription's `authorized_consumers_root` via
   `build_grant_consumer_action`.
   - Primitives: subscription factory, `grant_consumer` case
     (`Monotonic(CONSUMERS_ROOT_SLOT)`).

5. **Dan claims the bounty.** Carol's bounty cell publishes a
   `BountyState::Posted → Claimed` transition into the subscription
   cell via `build_bounty_state_publish_action`. The publisher cursor
   advances (`MonotonicSequence(SEQ_HEAD_SLOT)`); the message root
   advances (`Monotonic(MESSAGE_ROOT_SLOT)`).
   - Primitives: `bounty_state_payload_hash`,
     `build_bounty_state_publish_action`, subscription `publish` case.

6. **Dan submits a fulfillment proof.** Another publish:
   `Claimed → Fulfilled`. Bob's cell consumes the message and learns
   "Dan claimed your bounty".
   - Primitives: `BountyState::Fulfilled`, subscription `consume` case
     (`MonotonicSequence(SEQ_TAIL_SLOT)`).

7. **Carol settles the bounty after dispute window.** Subscription
   publishes `Fulfilled → Settled`. The receipt chain across all four
   apps composes: identity issuance receipt → nameservice register
   receipt → namespace mount receipt → subscription publish receipts →
   bounty settle receipt.

## What this demo verifies (positive cases in `expected.json`)

- All cross-app commitments derive deterministically:
  `AuthorizedSet::credential_set_commitment(issuer, schema)` matches
  what the witnessed predicate carries; the bounty payload hashes
  reproduce across re-runs; the nameservice resolve target maps the
  same way on every walk.
- The four kernel primitives are exercised:
  - `AuthorizedSet::CredentialSet` (cell program substrate)
  - `WitnessedPredicate::BlindedSet` (witness/predicate dispatch)
  - `MonotonicSequence` slot caveats (subscription head/tail, identity
    counter)
  - `Monotonic` slot caveats (revocation roots, message roots,
    consumer/publisher roots)
- Cross-app composition is *data-only*: no app crate imports another
  app's internals. The agreement points are the canonical commitments
  (`AuthorizedSet::credential_set_commitment`,
  `bounty_state_payload_hash`).

## What this demo rejects (negative cases in `expected.json`)

- **Forged credential**: a registration whose
  `WitnessedPredicate::BlindedSet` commitment does NOT match the
  expected `credential_set_commitment(alice_issuer, schema)` is rejected
  because the executor's `WitnessedPredicateRegistry` cannot dispatch
  to a verifier under a commitment the cell program does not
  recognize.
- **Wrong-tier registration without credential**: a registration that
  tries to use the attested method symbol but carries no witness blob
  fails the cell program's
  `identity_attested_tier_constraint`-bearing case.
- **Bounty fulfillment with wrong actor**: a publish carrying a
  payload hash whose `actor_pk_hash` field doesn't match Dan's pubkey
  hash produces a different payload commitment, so subscribers
  watching for Dan's claim see no match.
- **Subscription publish without grant**: a publish from a pubkey not
  in `authorized_publishers_root` fails the `publish` case's
  `SenderAuthorized { PublicRoot { set_root_index: PUBLISHERS_ROOT_SLOT } }`
  constraint.

## How it runs

This demo is *substrate-shape*, not *executor-bound*. The Python
orchestrator reproduces the canonical commitments and payload hashes
the Rust crates produce, walks the seven-step composition story, and
verifies each step against the documented primitive contract.

`./run.sh` orchestrates the four agent scripts (alice.py, bob.py,
carol.py, dan.py); each emits a JSON receipt to `state/`. The harness
then asserts every entry in `expected.json` holds.

**Why no cargo / no executor?** The integration patterns landed in
this lane (`AuthorizedSet::CredentialSet`, the four cross-app helpers)
are pre-recursion substrate shape — they're the *commitments* the
executor will dispatch against once the witnessed-predicate registry
wiring is complete. Verifying the shape *now* gates the integration
contract: the cross-app composition cannot be broken by any later
executor change without also breaking the same commitment derivation
the demo checks.

## Files

- `run.sh` — orchestrator
- `alice.py` — issuer cell + credential issuance
- `bob.py` — credential holder, nameservice tier registration, mount
- `carol.py` — bounty poster, subscription cell, settlement
- `dan.py` — bounty claimer + fulfillment
- `expected.json` — must_pass + must_not_pass assertions
- `state/` — per-run JSON artifacts (created by `run.sh`)
