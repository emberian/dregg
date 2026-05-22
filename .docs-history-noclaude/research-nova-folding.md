# Nova/Folding Research Summary (2026-05-20)

## Decision: Use plain Nova (Microsoft `nova-snark`) for IVC fold chains

Our fold step is ~1000 R1CS constraints, folded ~5-20 times. Plain Nova is the right choice:
- O(1) verifier cost in number of folds (truly constant, not log N)
- ~10,000 multiplication gates for the recursion circuit
- Microsoft's crate: 3 curve cycles, 3 commitment schemes, EVM feature, MicroNova compression

## Key findings:

### Nova (RECOMMENDED):
- Verifier cost O(1) in N (number of folds), O(C) in step circuit size
- Pallas/Vesta for transparent, BN254/Grumpkin + HyperKZG for EVM-friendly
- MicroNova/MicroSpartan: verifier runtime doesn't depend on step circuit size either

### HyperNova:
- Supports CCS (which captures AIR directly without overhead)
- Only worth it if we need direct AIR folding (we don't — our step is small R1CS)
- Implementations are experimental (Sonobe: unaudited, no releases)

### ProtoStar:
- For Plonkish + high-degree gates + lookups
- Not relevant for our small uniform step relation

### SuperNova (Arecibo):
- Multiple different step circuits per fold
- Useful if attenuation steps are heterogeneous (they're not currently)

## Implementation plan:
- Use Microsoft `nova-snark` with Pallas/Vesta (already in our workspace)
- For EVM: switch to BN254/Grumpkin + HyperKZG + MicroSpartan compression
- Our existing `circuit/src/backends/nova.rs` already implements this correctly
- The fold step (old_root → new_root with removal membership proofs) is natural R1CS

## When to reconsider:
- If we redesign the fold step to use AIR/Plonkish → consider HyperNova
- If we need on-chain verification → switch to BN254 + MicroSpartan
