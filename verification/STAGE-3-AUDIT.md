# Stage 3 Effect VM AIR — Composition Audit

**Date:** 2026-05-24
**Auditor:** typed-composition checker (`pyana-verification`)
**Subject:** Stage 3 Effect VM AIR expansion (commits `ec9b2469..f2b84cb7`)
**Result:** `CONDITIONALLY SOUND (gaps exist)` — same verdict as pre-Stage-3,
**but** three new trust requirements have been surfaced and discharged.

---

## Scope of Stage 3

22 new VM `Effect` variants landed between commits `ec9b2469` and `f2b84cb7`,
growing `NUM_EFFECTS` from 24 to 46 and `EFFECT_VM_WIDTH` from 83 to 105.

Categorized by constraint shape:

| Category | Count | Variants |
|---|---|---|
| Pure passthrough | 11 | `EmitEvent`, `SetPermissions`, `SetVerificationKey`, `CreateSealPair`, `RefreshDelegation`, `RevokeDelegation`, `CreateCell`, `SpawnWithDelegation`, `BridgeCancel`, `ExerciseViaCapability`, `Introduce`, `PipelinedSend` |
| cap_root Merkle update | 1 | `RevokeCapability` |
| Balance debit (real) | 2 | `CreateEscrow`, `BridgeLock` |
| Balance credit (real) | 1 | `BridgeMint` |
| Off-trace balance shim | 6 | `CreateCommittedEscrow`, `BridgeFinalize`, `ReleaseEscrow`, `RefundEscrow`, `ReleaseCommittedEscrow`, `RefundCommittedEscrow` |

The **public input shape of `EffectVmProof` is UNCHANGED** (still 5 inputs:
`old_state_commitment`, `new_state_commitment`, `net_delta`, `effects_hash`,
`custom_effect_count`). Therefore the composition graph topology — bindings
between `EffectVmProof`, `IvcFoldChain`, `DerivationProof`, `IssuerMembership`,
`PresentationProof` — required **no new edges**. Stage 3 lives entirely
"inside" the AIR.

## Composition gaps introduced by Stage 3

None at the graph-binding level. The model is single-statement for the Effect
VM, so adding selectors doesn't shift any binding indexes.

The `find_gaps()` heuristic still reports 12 unbound inputs — these are all
**pre-existing** (mostly externally-provided values like `federation_root`,
`presentation_tag`, `revealed_facts_commitment`) and unchanged from the
pre-Stage-3 baseline. The checker's heuristic in `lib.rs::is_likely_external_input`
just doesn't classify `StateCommitment` / `MerkleRoot` / `EffectsHash` as
"external-by-default," which is a checker-tuning issue, not a Stage 3 issue.

## Passthrough variants — are their effects_hash bindings consistent?

**Yes, for the 12 truly-passthrough variants.** Each binds a variant-specific
hash (event_hash, vk_hash, pair_hash, child_hash, create_hash, spawn_hash,
nullifier-cancel hash, exercise_hash, introduce_hash, pipelined_send_hash)
into `effects_hash`. This means the verifier can distinguish which variant
was emitted on each row, even though the state columns don't change. The
new `EffectsHashBindingCompleteness` custom guarantee in the model captures
this.

**Caveat for 6 of them** (`CreateCommittedEscrow`, `BridgeFinalize`,
`Release/RefundEscrow`, `Release/RefundCommittedEscrow`): these are
passthrough in the AIR but represent **real off-trace balance movement**.
The AIR proves only that the row is a state passthrough and binds
`escrow_id` / `receipt_hash` into `effects_hash`. The actual balance
reconciliation (e.g., escrowed funds flowing to a recipient on
`ReleaseEscrow`) lives in the executor's off-trace escrow/bridge ledger.
This is a **new trust requirement** Stage 3 introduces, now recorded as the
`OffTraceBalanceReconciliation` custom assumption.

## Concrete soundness gaps flagged for follow-up

The model now records three Stage 3-specific trust requirements (all
discharged as `RequiresTrust { … }`):

1. **`OffTraceBalanceReconciliation`** — escrow/bridge passthrough variants
   bind ledger keys but not ledger transitions. A malicious executor could
   replay or skip the off-trace reconciliation without the AIR detecting it.
   **Suggested follow-up:** add `EscrowLedgerProof` / `BridgeLedgerProof`
   nodes to the composition graph whose `escrow_root` / `bridge_ledger_root`
   transitions are bound by `effects_hash` to the Effect VM's variant
   bindings.

2. **`CommittedValueRangeProof`** — `CreateCommittedEscrow` hides value in a
   Pedersen commitment; the AIR cannot enforce the debit amount. The
   existing `Conservation` guarantee therefore only covers the cleartext
   (cell balance) ledger, **not** the committed-value escrow ledger.
   **Suggested follow-up:** require a `CommittedValueProof` (range proof +
   Pedersen opening) wherever `CREATE_COMMITTED_ESCROW` appears in a turn;
   add it as a sibling proof in the composition graph, bound by `effects_hash`.

3. **`CapabilitySlotPresence`** — `RevokeCapability` enforces the cap_root
   Merkle update but does **not** prove the slot was previously present in
   the c-list. This is symmetric with the pre-existing `GrantCapability`
   weakness; cap-set honesty depends on the executor's c-list snapshot.
   **Suggested follow-up:** either add an explicit Merkle-membership
   sub-proof on the pre-state c-list (would require a new public input
   exposing the pre-image slot), or accept this as a permanent
   executor-trust requirement (consistent with how `GrantCapability` is
   handled today).

## Existing claims under Stage 3

| Claim | Still holds? | Notes |
|---|---|---|
| `EffectVmProof.ValidTransition` | YES | Covers passthrough (no-op) and real-state-change variants alike |
| `EffectVmProof.Conservation(net_delta)` | YES, with caveat | The 3 real-balance variants (CreateEscrow, BridgeLock debit; BridgeMint credit) are properly summed into `net_delta`. The 6 off-trace variants don't touch on-trace balance, so they don't violate this — but they represent value movement that's **outside** what `Conservation` covers. |
| `IvcFoldChain.MonotonicNarrowing` | Unchanged | Operates on cap_root commitments; Stage 3's cap_root variants (`RevokeCapability`) narrow the set, consistent with monotonicity. |
| `IssuerMembership.Membership` | Unchanged | Not affected by Stage 3. |
| `DerivationProof.Authorization` | Unchanged | Not affected by Stage 3. |
| `PresentationProof.*` | Unchanged | Not affected by Stage 3. |

## Verdict line from `cargo run -p pyana-verification`

```
Overall:                  CONDITIONALLY SOUND (gaps exist)
  Cryptographic guarantees: 12
  Trust requirements:       10
  Composition gaps:         12
  Type errors:              0
  Acyclic:                  YES
```

(Pre-Stage-3 baseline was 11 guarantees / 7 trust requirements. The new
guarantee is `EffectsHashBindingCompleteness`; the 3 new trust requirements
are listed above. The 12 "composition gaps" are pre-existing and unrelated
to Stage 3.)

## Recommendation

Stage 3 does **not** weaken any existing cryptographic guarantee. It
**does** introduce a new attack surface concentrated in the executor's
off-trace bookkeeping (escrow/bridge ledgers, c-list snapshot). The three
new trust requirements should be tracked as follow-up work for Stage 5
(escrow) and Stage 6 (bridge), where the corresponding ledger proofs were
already anticipated in `STAGE-3-AIR-PLAN.md`'s "not in scope" section.
