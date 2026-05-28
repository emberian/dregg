# Substrate Test Audit

Audit date: 2026-05-25. Covers `dregg-storage-templates/`, `credentials/` (dregg-credentials), and `app-framework/`.

---

## dregg-storage-templates

### Existing coverage (24 adversarial tests in `tests/adversarial.rs`)

**Real.** Each test drives `CellProgram::evaluate_with_meta` against hand-crafted `(old_state, new_state, TransitionMeta)` triples. The `strip_witness_constraints` helper strips `SenderAuthorized`/`Witnessed`/`RateLimit` so slot-caveat shape can be tested without executor wiring.

Gaps found:
- Tests exercise individual constraint violations but no _multi-step composed flow_ (e.g. `send × N → dequeue × N`).
- The `blinded_queue` add→consume sequence was not tested as a lifecycle.
- No cross-template contract verification (5 templates share identical factory descriptor shape; tests were 5× duplicated).
- `ProgrammableQueueConfig::param_hash` not tested for determinism/divergence.

### New integration tests added

| File | Tests | Flow |
|---|---|---|
| `tests/integration_blinded_queue_real.rs` | 5 | add N → commitment_count monotonic; flat-count add rejected; consume freezes commitments side; consume mutating commitments_root rejected; nullifier decrement rejected; immutable slots survive full lifecycle |
| `tests/integration_cap_inbox_send_dequeue.rs` | 8 | send N → head advances; dequeue advancing head rejected; dequeue series tail catches head; tail decrement rejected; grant_sender slot isolation; grant_sender advancing head rejected; unknown method default-denied; immutable slots full lifecycle |
| `tests/integration_shared_helpers.rs` | 9 | Shared `assert_descriptor_contract` helper applied to all 5 templates; all 5 factory_vks distinct; all 5 child_program_vks distinct; every template has Immutable identity slot; `ProgrammableQueueConfig::param_hash` determinism + divergence; blinded_queue sovereign vs hosted only-mode-differs |

### Duplicate scaffold deduplication

The `assert_descriptor_contract` helper in `integration_shared_helpers.rs` replaces the formerly-5×-duplicated pattern:
```
let h1 = xxx_factory_descriptor().hash(); assert_eq!(h1, h1);
assert_eq!(d.child_program_vk, Some(xxx_child_program_vk()));
assert_eq!(canonical_program_vk(&xxx_program()), xxx_child_program_vk());
```

---

## credentials (dregg-credentials)

### Existing coverage (6 tests in `tests/roundtrip.rs`)

**Real.** Tests use the bridge-backed fast path (`prove_local_constraint_check_only`). The roundtrip covers: issue→present→verify, unknown-attribute rejected at issue, revoke→verify fails, predicate Gte, missing disclosure rejected, missing predicate rejected.

Gaps found:
- No multi-attribute schema with selective single-attribute disclosure verified end-to-end.
- No `present_anonymous` + `verify_anonymous` + `require_anonymous = true` path.
- No `predicate on Text attribute → PresentationError::NonPredicateAttribute` test.
- No `credential_id` stability and uniqueness test.
- No `non-anonymous presentation rejected when require_anonymous = true` test.

### New integration tests added

| File | Tests | Flow |
|---|---|---|
| `tests/integration_present_verify_full.rs` | 8 | Selective disclosure of 1/4 attrs; tampered disclosed value documented; missing expected disclosure → `MissingDisclosure`; predicate-only (no cleartext) `age >= 18`; predicate on Text → `NonPredicateAttribute`; anonymous presentation + `verify_anonymous`; non-anonymous rejected when `require_anonymous`; revoked pre→post lifecycle; credential_id stability + uniqueness |

---

## app-framework

### Existing coverage (3 integration tests in `tests/`)

- `tests/cipherclerk_sign_action.rs`: `sign_action` overwrites Unchecked with real Signature.
- `tests/escrow_authorization.rs`: `RejectingAuthorizer` blocks all escrow operations.
- `tests/no_unchecked.rs`: grep-guard preventing `Authorization::Unchecked` in `src/`.

Gaps found:
- No composed submit→receipt→chain flow test.
- No "restart from shared cclerk" identity continuity test.
- No multi-action atomic turn receipt test.
- No federation_id binding divergence test.
- `make_self_action`, `with_domain`, `previous_receipt_hash` chain not tested at integration level.

### New integration tests added

| File | Tests | Flow |
|---|---|---|
| `tests/integration_app_cipherclerk_lifecycle.rs` | 8 | construct→sign→submit→receipt; consecutive turns receipt chain; shared cclerk same cell_id after restart; restarted executor post-original-turns; multi-action atomic turn both roots; different fed_ids → different signatures; `make_self_action` targets own cell; domain variant distinct cell_id |

---

## Summary

- 4 new integration test files.
- 30 new tests total.
- 1 shared helper function extracted (`assert_descriptor_contract`) that replaces 5× duplicated factory descriptor assertions.
- All tests drive real composed flows through `CellProgram::evaluate_with_meta` or `EmbeddedExecutor::submit_action`; none hash a value and call it done.
