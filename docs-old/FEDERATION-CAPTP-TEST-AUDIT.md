# Federation + CapTP Test Audit

## Audit Date
2026-05-25

---

## Existing Tests — Categorization

### `captp/src/handoff.rs` (inline `#[cfg(test)]`)
| Test | Category |
|------|----------|
| `create_and_verify_signature` | Real/happy-path — verifies Ed25519 on cert |
| `present_to_target_success` | Real/composed — full validate_handoff flow |
| `expired_certificate_rejected` | Real/negative |
| `wrong_recipient_rejected` | Real/negative |
| `untrusted_introducer_rejected` | Real/negative |
| `max_uses_exhausted` | Real/negative — two-use cap correctly exhausted |
| `compact_string_roundtrip` | Real/structural — postcard+bs58 serde |
| `bytes_roundtrip` | Structural-only |
| `invalid_compact_string_prefix` | Structural/negative |
| `certificate_validity_check` | Structural/happy-path |
| `out_of_band_scenario` | **Real/composed** — OOB transport simulation (full flow) |

**Assessment:** handoff module has good unit coverage. No test of cross-federation introducer != target (i.e. `cert.introducer != cert.target_federation`). No GC integration.

### `captp/src/sturdy.rs` (inline `#[cfg(test)]`)
| Test | Category |
|------|----------|
| `export_and_enliven` | Real/happy-path |
| `enliven_not_found` | Real/negative |
| `enliven_expired` | Real/negative (boundary) |
| `enliven_exhausted_uses` | Real/negative |
| `one_time_use` | Real/negative |
| `revoke_then_enliven_fails` | Real/negative |
| `export_uri_format` | Real/structural — URI round-trip |
| `contains_and_len` | Structural |
| `effect_mask_attenuation` | Real/happy-path |

**Assessment:** good coverage. Missing: delegate-revoked-cap through the handoff layer; no integration with GC.

### `captp/src/gc.rs` (inline `#[cfg(test)]`)
| Test | Category |
|------|----------|
| `export_single_holder_drop_to_zero` | Real/composed |
| `export_multiple_holders_drop_one_still_held` | Real/composed |
| `export_multiple_refs_same_holder` | Real/composed |
| `export_drop_invalid_*` | Real/negative |
| `stale_export_detection` | Real/composed |
| `gc_sweep_*` | Real/composed |
| `import_*` | Real/composed |
| `export_drop_rejected_from_wrong_session` | **Real/security** — session isolation |
| `byzantine_node_different_session_cannot_drop_others_refs` | **Real/adversarial** |
| `export_session_superseded_by_reexport` | Real/security |

**Assessment:** strong. Session isolation tests are real adversarial tests. No Swiss table integration.

### `captp/src/uri.rs` (inline `#[cfg(test)]`)
| Test | Category |
|------|----------|
| `roundtrip` | Structural |
| `parse_invalid_scheme` | Structural/negative |
| `parse_wrong_segments` | Structural/negative |
| `parse_invalid_base58` | Structural/negative |
| `parse_wrong_length` | Structural/negative |
| `display_impl` | Structural |

**Assessment:** complete parser coverage. No enliven-after-parse tests.

### `captp/src/session.rs` (inline `#[cfg(test)]`)
| Test | Category |
|------|----------|
| `session_export_import` | Real/happy-path |
| `session_promises` | Real/composed |
| `session_active_tracking` | Real/composed |
| `session_epoch_tracks_generation` | Real/structural |
| `session_epoch_prevents_stale_message_processing` | **Real/security** — GC integration |

### `captp/tests/integration.rs`
| Test | Category |
|------|----------|
| `pipeline_register_pipeline_resolve_deliver` | Real/composed — pipeline lifecycle |
| `pipeline_chain_and_cascading_break` | Real/composed — cascade failure |
| `store_forward_ttl_expiry_and_priority` | Real/composed — TTL + priority |
| `session_gc_integration` | Real/composed — session+GC lifecycle |
| `cross_federation_bridge_full_flow` | Real/composed — bridge pipeline |
| `cross_federation_bridge_incoming_and_local_resolve` | Real/composed |
| `pipeline_to_nonexistent_promise_from_bridge` | Real/negative |
| `multi_federation_gc_independence` | Real/adversarial — 3-fed independence |
| `three_party_handoff_alice_introduces_bob_to_carol` | **Real/composed** — three-party handoff |

**Assessment of the three-party handoff test:** the test at line 351 of `integration.rs` DOES exercise a three-party handoff. The introducer (`alice_fed`) is distinct from the target (`carol_fed`, `fed(0xCA)`). The cert is signed by Alice, Bob presents it, Carol validates with `validate_handoff`. However: no forged-signature negative case, no GC lifecycle after acceptance, no compact-string transport simulation.

### `federation/tests/cross_federation_bridge_receipt.rs`
| Test | Category |
|------|----------|
| `cross_federation_lock_witness_finalize_roundtrip` | **Real/composed** — 3-phase bridge |
| `cross_federation_replay_rejected_after_finalize` | **Real/adversarial** — replay prevention |

**Assessment:** excellent. Real BLS threshold, real bridge phase log, adversarial replay. Missing: sub-threshold tamper test; committee identity rotation.

### `federation/src/threshold.rs` (inline `#[cfg(test)]`)
| Test | Category |
|------|----------|
| `test_threshold_sign_and_verify` | Real/happy-path |
| `test_threshold_not_met` | Real/negative |
| `test_threshold_wrong_message_fails_verification` | Real/negative |
| `test_threshold_qc_serialization` | Real/structural |
| `test_constant_size_regardless_of_committee` | Real/property |
| `test_all_members_sign` | Real/happy-path |

### `federation/src/receipt.rs` (inline `#[cfg(test)]`)
| Test | Category |
|------|----------|
| `body_hash_is_domain_separated` | Structural |
| `threshold_receipt_verifies_under_committee` | Real/happy-path |
| `threshold_receipt_rejected_when_federation_id_mismatches` | **Real/security** — F1 |
| `threshold_receipt_rejected_when_epoch_mismatches` | **Real/security** — F4 |
| `threshold_receipt_fails_under_below_threshold` | Real/negative |
| `threshold_receipt_fails_on_wrong_body` | Real/negative |
| `votes_receipt_verifies_above_threshold` | Real/happy-path |
| `votes_receipt_fails_when_signer_unknown` | Real/negative |
| `votes_receipt_rejects_duplicate_signer` | **Real/adversarial** |

### `federation/src/identity.rs` (inline `#[cfg(test)]`)
All tests are structural property checks (determinism, order-independence, rekey distinguishability).

---

## Coverage Gaps Filled by New Tests

| Gap | New Test File | Tests Added |
|-----|---------------|-------------|
| Three-party handoff with cross-federation introducer — no forged-sig negative | `captp/tests/integration_three_party_handoff.rs` | 5 tests |
| Revoke-then-delegate (swiss post-revoke rejected by handoff layer) | `captp/tests/integration_swiss_table_revoke.rs` | 5 tests |
| Sturdy-ref URI round-trip into enliven at receiver | `captp/tests/integration_sturdy_ref_serde.rs` | 6 tests |
| Full GC: export→import→drop→sweep→stale-ref fails | `captp/tests/integration_gc_collection.rs` | 6 tests |
| Committee threshold sign/tamper/cross-committee confusion | `federation/tests/integration_threshold_attestation.rs` | 7 tests |
| Committee rotation: id changes; old receipt still verifies under old VK | `federation/tests/integration_committee_rotation.rs` | 7 tests |

**Total new tests: 36**

---

## Does `dregg` Actually Test the CapTP Three-Party Handoff End-to-End?

**Answer: YES, but with gaps.**

The test `three_party_handoff_alice_introduces_bob_to_carol` in `captp/tests/integration.rs` (line 351) is a genuine end-to-end test. It uses real Ed25519 keypairs via `generate_keypair`, creates a `HandoffCertificate` with Alice's signing key, has Bob produce a `HandoffPresentation`, and calls `validate_handoff` against Carol's `SwissTable`. The introducer (`alice_fed`) is explicitly distinct from the target (`carol_fed = fed(0xCA)`), satisfying the cross-federation property.

**What was missing (now added):**
1. No negative case for a forged introducer signature → added in `integration_three_party_handoff.rs`
2. No impostor (wrong recipient key) negative case → added
3. No GC lifecycle following the handoff acceptance → added
4. No compact-string OOB transport round-trip into `validate_handoff` → added
5. No test of presenting a cert whose swiss was revoked post-issuance → added in `integration_swiss_table_revoke.rs`

The existing test is real and passes. The gaps were adversarial and integration cases, not the basic flow.
