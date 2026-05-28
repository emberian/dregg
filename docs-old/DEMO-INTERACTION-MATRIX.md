# Demo Interaction-Pattern Matrix

This file enumerates **every protocol interaction pattern** dregg supports
and records which demo scenario (today) exercises it. The matrix is a
working document for the "demo complexity upgrade" lane.

A separate "cross-app integration + E2E demo" lane is building
`demo/cross-app-e2e/` (composing nameservice + identity + subscription +
governed-namespace end-to-end). **This document covers the complementary
layer**: protocol-primitive coverage at the demo layer, regardless of
which app surfaces the primitive.

Convention: each row is a primitive. Coverage is one of:

| symbol | meaning |
| --- | --- |
| `OK` | covered end-to-end with real cryptographic artifacts in a current demo |
| `PART` | partially covered (e.g. only happy path; only construction, not verification) |
| `MISS` | not yet covered by any demo |
| `XAPP` | being added by the cross-app-e2e lane (do NOT duplicate) |

The four scenario columns are:

- **silver** — `demo/two-ai-handoff/` (the existing Silver-Vision demo; real
  STARK proofs through `dregg-node` + `dregg-verifier`)
- **multi** — `demo/multi-node-devnet/scenarios/*` (devnet-shape scenarios)
- **xapp** — `demo/cross-app-e2e/` (in-flight, parallel lane)
- **imatrix** — `demo/two-ai-handoff/` + new `silver-helper` subcommands
  this lane adds

## 1. Capability operations

| Primitive | silver | multi | xapp | imatrix | Notes |
| --- | --- | --- | --- | --- | --- |
| Capability issue (`Effect::GrantCapability`) | OK | OK | XAPP | — | step 3 grant-turn |
| Three-party handoff (introducer→recipient→target) — `HandoffCertificate` | OK | OK | — | — | `make-handoff` |
| Bearer cap (`Authorization::Bearer`) | OK | OK | — | — | step 7 exercise-bearer |
| CapTP-delivered (`Authorization::CapTpDelivered`) | OK | — | — | — | `make-captp-delivered` |
| `Effect::Introduce` (three-party-introduce as an Effect) | MISS | MISS | MISS | NEW | imatrix adds `make-introduce` |
| Sturdy-ref export (`Effect::ExportSturdyRef`) | PART | — | — | — | constructed but not enliven-roundtripped |
| Sturdy-ref enliven (`Effect::EnlivenRef`) | MISS | MISS | — | — | needs MCP tool or helper |
| Drop ref (`Effect::DropRef`) | MISS | — | — | — | low-priority |
| Validate handoff (`Effect::ValidateHandoff`) | OK | — | — | — | implicit via CapTpDelivered path |
| Capability revoke (`Effect::RevokeCapability`) | PART | OK | XAPP | — | covered in devnet scenarios |
| Capability attenuate (caveats / `BearerCapProof.allowed_effects`) | OK | — | — | — | bearer-cap proof carries the mask |
| Sealer / Unsealer (`Effect::CreateSealPair`, `Seal`, `Unseal`) | MISS | MISS | MISS | MISS | partition-tolerant cap transfer; no demo |

## 2. Effect categories

| Primitive | silver | multi | xapp | imatrix | Notes |
| --- | --- | --- | --- | --- | --- |
| `Effect::SetField` | OK | OK | XAPP | NEW | imatrix slot-suite drives explicit SetField transitions |
| `Effect::Transfer` | OK | OK | XAPP | — | step 7 |
| `Effect::GrantCapability` / `RevokeCapability` | OK | OK | XAPP | — | |
| `Effect::EmitEvent` | OK | OK | XAPP | — | implicit in turns |
| `Effect::IncrementNonce` | OK | OK | OK | — | trivial |
| `Effect::CreateCell` | OK | OK | XAPP | — | |
| `Effect::SetPermissions` / `SetVerificationKey` | PART | — | — | — | applied last-in-action; needs adversarial test |
| `Effect::NoteSpend` / `NoteCreate` (private notes) | PART | OK | — | — | `bilateral_transfer.sh` |
| `Effect::CreateSealPair` / `Seal` / `Unseal` | MISS | MISS | MISS | MISS | priority-low |
| `Effect::SpawnWithDelegation` / `RefreshDelegation` / `RevokeDelegation` | MISS | MISS | XAPP? | MISS | |
| `Effect::BridgeLock` / `BridgeMint` / `BridgeFinalize` / `BridgeCancel` | OK | OK | — | — | `cross_fed_handoff.sh`, `intent_match_cross_fed.sh` |
| `Effect::Introduce` (three-party) | MISS | MISS | MISS | NEW | imatrix adds |
| `Effect::PipelinedSend` (eventual-resolve) | MISS | MISS | — | MISS | |
| `Effect::CreateObligation` / `FulfillObligation` / `SlashObligation` | MISS | MISS | — | MISS | proof-bonds |
| `Effect::CreateEscrow` / `ReleaseEscrow` / `RefundEscrow` | MISS | MISS | — | MISS | conditional escrow |
| `Effect::CreateCommittedEscrow` / `ReleaseCommittedEscrow` / `RefundCommittedEscrow` | MISS | MISS | — | MISS | privacy escrow + range proofs |
| `Effect::ExerciseViaCapability` (atomic eval) | MISS | MISS | XAPP? | MISS | |
| `Effect::MakeSovereign` | OK | — | — | — | |
| `Effect::CreateCellFromFactory` | PART | — | XAPP | — | factory tests use this |
| `Effect::QueueAllocate` / `Enqueue` / `Dequeue` / `Resize` / `AtomicTx` / `PipelineStep` | PART | — | — | MISS | covered in cell crate tests; not in demo |
| `Effect::ExportSturdyRef` / `EnlivenRef` / `DropRef` / `ValidateHandoff` | PART | — | — | — | CapTP-delivered covers the verify side |

## 3. Authorization variants

| Primitive | silver | multi | xapp | imatrix | Notes |
| --- | --- | --- | --- | --- | --- |
| `Authorization::Signature` | OK | OK | XAPP | — | every turn that isn't bearer/captp |
| `Authorization::Proof` | PART | — | — | — | structured but not deeply exercised |
| `Authorization::Breadstuff` (cap-token) | PART | OK | — | — | older path |
| `Authorization::Bearer` (proof-carrying delegation) | OK | OK | — | — | step 7 |
| `Authorization::Unchecked` | OK | OK | OK | — | (only valid where permissions allow) |
| `Authorization::CapTpDelivered` | OK | — | — | — | `make-captp-delivered` |
| `Authorization::Custom { WitnessedPredicate }` | MISS | MISS | XAPP? | MISS | depends on `AUTHORIZATION-CUSTOM-DESIGN.md` |
| And / Or / OneOf / Threshold (composite auth via custom predicate) | MISS | MISS | XAPP? | MISS | |
| Slot caveats (`StateConstraint::*`) as caveat | OK (WriteOnce, Monotonic) | — | XAPP (governed-namespace voting) | NEW (Immutable, StrictMonotonic, BoundedBy, FieldDelta, FieldDeltaInRange) | imatrix adds the missing variants |
| DFA-as-caveat | PART | — | — | MISS | DFA crate exists; not threaded into a demo |
| `BearerCapProof.allowed_effects` (facet mask attenuation) | OK | — | — | — | |

## 4. Cross-cell

| Primitive | silver | multi | xapp | imatrix | Notes |
| --- | --- | --- | --- | --- | --- |
| γ.2 bilateral (Transfer / Grant / Introduce) | OK (Transfer) | OK | XAPP (Grant) | NEW (Introduce) | |
| γ.2 unilateral (incoming Effect) | PART | — | — | NEW | imatrix adds the Introduce-recipient side |
| Ring-closure (multi-hop incoming) | MISS | MISS | MISS | MISS | requires N≥3 cells, no demo yet |
| `BilateralBundle` pair-verify | OK | OK | XAPP | — | `dregg-verifier bilateral-pair` |
| Aggregated bundle (γ.2 Phase 2) | PART | — | — | NEW | imatrix exercises `aggregated-bundle` subcmd |

## 5. Federation

| Primitive | silver | multi | xapp | imatrix | Notes |
| --- | --- | --- | --- | --- | --- |
| Attested-root advancement | OK | OK | — | — | per-turn AttestedRoot v2 |
| Threshold sign | PART | OK | — | — | `federation_attestation.sh` |
| Peer exchange | PART | OK | — | — | `peer_exchange_bypass.sh` |
| Cross-federation handoff | OK | OK | — | — | `cross_fed_handoff.sh` |
| Intent match cross-fed | OK | OK | — | — | `intent_match_cross_fed.sh` |
| BFT consensus (>1 node) | MISS | OK | — | — | multi-node-devnet only |

## 6. Proof / verifier

| Primitive | silver | multi | xapp | imatrix | Notes |
| --- | --- | --- | --- | --- | --- |
| STARK Effect-AIR (`Transfer`, `Grant`, `SetField`, etc.) | OK | OK | XAPP | — | per-turn proofs |
| WitnessedReceipt v1 replay chain (Silver Vision) | OK | OK | XAPP | — | `dregg-verifier replay-chain` |
| WitnessedReceipt scope-2 (recursive proof) | PART | — | — | NEW | imatrix exercises `scope-recursive` subcmd against a chain that has compressed proofs |
| Aggregated bundle (`aggregated-bundle` subcmd) | PART | — | — | NEW | imatrix invokes the verifier subcommand |
| VK v2 layered registry | PART | — | — | — | |
| Custom effect registry | MISS | — | — | MISS | |
| Adversarial proof rejection (tampered byte/felt) | OK (captp, sovereign, bilateral) | — | — | NEW (slot-suite, introduce-bilateral) | |

## 7. Predicate / witness

| Primitive | silver | multi | xapp | imatrix | Notes |
| --- | --- | --- | --- | --- | --- |
| `WitnessedPredicate` (`Dfa`, `MerkleMembership`, `BlindedSet`, `Custom`) | MISS | MISS | XAPP (BlindedSet via identity) | MISS | |
| `AuthorizedSet::PublicRoot` | PART | — | — | — | construction-only |
| `AuthorizedSet::BlindedSet` | PART | — | — | — | |
| `AuthorizedSet::CredentialSet` (identity-issuer × schema) | MISS | MISS | XAPP | NEW | imatrix adds `make-credential-set-auth` |
| Predicate proof (`Gte`, `Lte`, `InRange`, etc., over private attrs) | PART | — | — | — | `bridge::present` tests cover this; not in demo |
| Non-revocation against blinded set | MISS | — | XAPP | MISS | |

## 8. App-level (starbridge-apps)

| Primitive | silver | multi | xapp | imatrix | Notes |
| --- | --- | --- | --- | --- | --- |
| **nameservice** register / resolve / renew / transfer / revoke | MISS | MISS | XAPP | — | xapp lane |
| **identity** issue / present / verify / revoke credential | MISS | MISS | XAPP | — | xapp lane |
| **subscription** start / renew / cancel / publish / consume | MISS | MISS | XAPP | — | xapp lane |
| **governed-namespace** propose / vote / commit / register-service | MISS | MISS | XAPP | — | xapp lane |
| Cross-app: identity-credential-gated nameservice tier | MISS | MISS | XAPP | NEW (primitive only) | imatrix exercises the underlying `AuthorizedSet::CredentialSet` constraint |

## 9. Storage (cell programs)

| Primitive | silver | multi | xapp | imatrix | Notes |
| --- | --- | --- | --- | --- | --- |
| `CellProgram::Predicate` (slot caveats) | OK (WriteOnce + Monotonic) | — | XAPP | NEW (all variants) | imatrix `slot-caveat-suite` |
| Programmable queue cell-programs | PART | — | — | MISS | cell crate has them; not in demo |
| Indexed lookup in storage | PART | — | — | MISS | |
| `CellProgram::evaluate` adversarial paths | OK (one variant) | — | — | NEW (every variant) | |

## 10. Recursive proofs

| Primitive | silver | multi | xapp | imatrix | Notes |
| --- | --- | --- | --- | --- | --- |
| `WitnessedReceipt::from_components_with_compression` (recursive scope-2) | PART | — | — | NEW | imatrix builds a WR with `recursive_compress: true` and runs `dregg-verifier scope-recursive` |
| `WitnessedReceipt::from_components_strict_recursive` | MISS | — | — | NEW | imatrix triggers the strict path |
| Adversarial: scope-recursive rejects tampered recursive proof | MISS | — | — | NEW | |

---

## Prioritized additions for this lane

Implementing in order of "biggest coverage gain per LOC":

1. **`slot-caveat-suite`** — extend `silver-helper slot-caveat-demo` to walk
   through `Immutable`, `StrictMonotonic`, `BoundedBy`, `FieldDelta`,
   `FieldDeltaInRange` against `CellProgram::evaluate`. Each variant gets
   a positive and a negative case. Adds slot-caveat coverage from 2/13
   variants to 7/13.
   - **Adds rows:** §3 slot caveats (Immutable, StrictMonotonic,
     BoundedBy, FieldDelta, FieldDeltaInRange) — all `NEW`.

2. **`make-credential-set-auth`** — build the substrate-shape
   `AuthorizedSet::CredentialSet { issuer_cell, credential_schema_id }`
   and demonstrate the deterministic commitment
   (`AuthorizedSet::credential_set_commitment`) matches what
   `starbridge-identity::credential_set_commitment` produces. This is the
   primitive the cross-app lane uses for credential-gated voting.
   - **Adds rows:** §7 `CredentialSet`.

3. **`make-introduce`** — assemble an `Effect::Introduce` turn with
   introducer/recipient/target, sign it as Alice, build the γ.2 bilateral
   bundle whose `IntroduceEdge` columns are the introducer side and the
   recipient side, and pair-verify. Tampered variant must reject.
   - **Adds rows:** §1 `Effect::Introduce`, §4 γ.2 Introduce edges.

4. **`make-recursive-witness`** — build a Turn, produce its
   `WitnessedReceipt`, recompress to a scope-2 recursive proof, then shell
   to `dregg-verifier scope-recursive`. Tampered proof must reject.
   - **Adds rows:** §10 all three rows.

5. **`make-sealer-unsealer`** (stretch) — exercise the
   `Effect::CreateSealPair` / `Seal` / `Unseal` triad. Partition-tolerant
   cap-transfer that no current demo touches.
   - **Adds row:** §1 sealer/unsealer.

Items 1-4 land this session. Item 5 is stretch.

## Non-goals (defer to cross-app lane)

- App-level scenarios (nameservice register / identity issue / subscription
  publish / governed-namespace vote) — that lane owns app composition.
- Multi-cell devnet driver — `multi-node-devnet/` already covers this.
- Web UI integration — orthogonal.
- Brand-new effect categories (note ZK proofs, Pedersen commitments) —
  out of scope unless trivially reachable.
