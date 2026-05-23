# Verification Policy Architecture: Recommendation

## Diagnosis

The current architecture has ONE canonical verifier (`verify_proof_complete`) that already does the right thing. The problem is not that policy is in multiple places -- it is that OTHER code paths ALSO perform partial verification, creating the illusion of scattered policy when in fact they are redundant checks that should be deleted or made explicit pass-throughs.

Concretely:
- `StarkVerifier` (wire) re-checks action binding and composition commitment that `verify_proof_complete` already checks. This is defense-in-depth at the TCP boundary but encodes its OWN idea of what "valid" means.
- `StrictPresentation` (middleware) calls `verify_presentation_bytes` (which delegates to `verify_proof_complete`) then ALSO checks tier separately -- a check that `verify_proof_complete` already performs internally by returning `ProofTier::Production` only on success.
- App qualification modules call circuit verification directly, bypassing action binding and freshness.

## Decision: Option C with a Dead Tier System

**Backend is invisible to the verifier.** All proofs serialize to `WirePresentationProof`. The verifier calls `verify_proof_complete`. Period.

**Remove `ProofTier` as an architectural concept.** Replace it with a compile-time distinction:

- **Sound proof** = produced by a backend whose feature flag is enabled AND whose `prove_*` function returns `Ok`. These go on the wire.
- **Structural stub** = produced when a backend's feature flag is OFF. These MUST NOT serialize to `WirePresentationProof`. Enforce at the type level: stubs return `StructuralProof` (not `WirePresentationProof`), which has no `Serialize` impl.

The tier system currently exists to prevent a structural stub from accidentally satisfying a verifier. That is a type-system problem, not a runtime-check problem. If stubs cannot serialize, they cannot reach a verifier. Runtime tier checks become dead code.

## Architecture

```
                     +-----------------------+
                     | verify_proof_complete |  <-- THE policy function
                     +-----------------------+
                       checks:
                       1. federation root binding
                       2. STARK validity (dispatches on air_name)
                       3. action binding (4-element commitment)
                       4. timestamp freshness
                       5. composition commitment (sub-proof binding)
                       returns: VerifiedPresentation | VerifyError

    Wire layer:        calls verify_proof_complete, nothing else
    Middleware:         calls verify_proof_complete via engine, nothing else
    SDK:               calls verify_proof_complete, nothing else
    App framework:     receives VerifiedPresentation, inspects .action/.resource
```

Everything else is DELETED:
- `StarkVerifier::verify` action binding check: redundant, remove.
- `StrictPresentation` tier check after verify: redundant, remove.
- `verify_authorization_proof` in SDK: replace with re-export of `verify_proof_complete`.
- Direct `stark::verify` calls in app qualification: replace with `verify_proof_complete`.

## Backend Multiplicity: Answer is C (backend-invisible)

Different backends for different sub-proofs is FINE. The `WirePresentationProof` already contains typed sub-proof slots (`real_stark_proof`, `ivc_proof`, `validated_ivc_proof`). The verifier dispatches on what is present. This means:

- Membership can be Plonky3 (native Poseidon2 AIR).
- Fold chain can be custom STARK (IVC hash-chain) or validated IVC with per-step STARKs.
- Derivation can be custom STARK today, Kimchi tomorrow.

The verifier does not care which backend produced each sub-proof. It checks: (a) the sub-proof is cryptographically valid for its declared AIR, and (b) the composition commitment binds them together. This is already how `verify_proof_complete` works -- it dispatches on `air_name`.

## Composition Rule

Sub-proofs from DIFFERENT backends are composable IFF they share the same field for composition commitment computation (currently BabyBear/Poseidon2). Cross-field backends (Kimchi/Pasta) require a translation layer (field-emulation gadget or wrap-then-compose). This is the STARK-in-Pickles path described in `recursive-proof-architecture.md`.

## Devnet

Devnet should NOT enforce Production tier. Any cryptographically-sound backend (custom STARK included) is sufficient. The distinction is:

- **Mainnet**: `verify_proof_complete` accepts only Poseidon2 STARKs (the `MerklePoseidon2StarkAir` / `BlindedMerklePoseidon2StarkAir` dispatch that already exists).
- **Devnet**: `verify_proof_complete` accepts any AIR that passes `stark::verify`. This is a one-line config change: accept all `air_name` values rather than filtering to Poseidon2-only.

Implement as a `VerifierConfig { accepted_airs: Vec<&str> }` parameter on `verify_proof_complete`, defaulting to Poseidon2-only.

## Migration Steps

1. Add `VerifierConfig` to `verify_proof_complete` (accepted AIRs, max proof age, composition required).
2. Delete the redundant action-binding check in `StarkVerifier::verify` -- make it a thin wrapper around `verify_proof_complete`.
3. Delete the tier check in `StrictPresentation` -- `verify_proof_complete` already rejects non-production proofs.
4. Make `StructuralProof` a non-serializable type so stubs cannot reach the wire. Delete `ProofTier` runtime checks.
5. Expose `VerifiedPresentation` (the return type of `verify_proof_complete`) as the ONLY type that callers receive after verification. App code pattern-matches on this, never on raw proof bytes.

## What App Developers See

```rust
// In their axum handler:
async fn handler(verified: StrictPresentation) -> impl IntoResponse {
    // `verified.action` and `verified.resource` are already checked.
    // No need to think about backends, tiers, or proof formats.
}
```

They never import `pyana_circuit`. They never see `ProofTier`. They get a `StrictPresentation` or they get a 403. That is the entire API surface.
