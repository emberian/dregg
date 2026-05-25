# demo/silver-vision-e2e — Status: Spec Stub

## What this directory is

`expected.json` is the **forward-looking specification** for a full Silver
Vision end-to-end harness. It documents 51 `must_pass` assertions and 35
`must_not_pass` assertions covering:

- Sovereign cell initialization + SovereignCellWitness signing
- Trilateral Effect::Introduce across three cells (Alice@F_A, Bob@F_B, Carol@F_B)
- Bilateral Effect::Transfer + γ.2 PI binding across two cells
- Slot caveats: rate-limit + monotonic balance
- Auth::Custom predicate with DFA proof, federation-bound signing message
- CapTP delivery signatures (introducer + recipient)
- Receipt-chain linking: grant → exercise → receive
- Dave (fourth-party verifier with no chain access) verifying all of the above
- Bridge four-phase (happy path + refund alt path)
- BLS threshold aggregation (4-of-3 and 7-of-5 scenarios)
- Predicate composition (16 StateConstraint variants in one CellProgram)
- Ring of 3 cells bilateral-pair binding

## What does NOT exist

- No harness binary or script.
- No runner shell script.
- No agent scripts.

The `expected.json` is the **spec before the binary exists**, as documented in
its own `documented_gaps` field.

## Relationship to existing demos

- `demo/two-ai-handoff/` covers a subset: sovereign witness, slot caveats
  (WriteOnce + 5 other variants), CapTpDelivered turns, γ.2 bilateral binding,
  and recursive proof compression. It has a real harness (`run.sh` + real binaries).
- `demo/cross-app-e2e/` covers a different subset: credential-gated nameservice
  registration, subscription bounty flow, cross-app commitment composition. It has
  a real harness but structural-only verification (see `REAL-VERSION.md`).

## Blocked on

From `expected.json`:

```
caveat-correctness lane: WitnessedPredicateRegistry dispatch from cell-program path
caveat-correctness lane: executor wires sender_epoch_count + revealed_preimage into EvalContext
γ.2 Phase 1: PI fields {transfer_id, grant_id, intro_id} + off-AIR pair/triple verifier
sovereign-witness AIR teeth (AUDIT-sovereign-witness-teeth.md)
AUTHORIZATION-CUSTOM-DESIGN: Auth::Custom executor dispatch through registry with InputRef::SigningMessage binding
```

## What to do when unblocked

When the above lanes land:

1. Write `run.sh` following the same pattern as `demo/two-ai-handoff/run.sh`:
   - Build pyana-node + pyana-verifier + silver-helper (or new harness binary).
   - Spin up two in-process federations (F_A, F_B) via the node CLI.
   - Drive Alice's sovereign cell init, introduce, bilateral transfer, slot caveat
     exercises, Auth::Custom dispatch, CapTP delivery, Dave's offline verification.
   - Shell to `pyana-verifier` for each proof check.
   - Compare results against `expected.json` must_pass / must_not_pass.

2. Follow the `improve_dont_degrade` principle: as each blocked lane lands,
   expand `expected.json` must_pass rather than weakening or removing checks.

3. Do NOT add `|| true` or hardcoded-constant assertions. Every must_pass
   assertion must reflect real system behavior, not Python arithmetic on
   shell variables.
