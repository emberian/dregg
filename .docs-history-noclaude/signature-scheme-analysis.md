# Signature Scheme Analysis for Pyana QC

## Decision Summary

For pyana's quorum certificates, the signature situation has three distinct layers with different requirements:

### Layer 1: Consensus Protocol Signatures (gossip, voting, view-change)
**Recommendation: Ed25519 (keep current)**
- Fast (50μs), well-understood, small (64 bytes)
- Used by every BFT system in production
- Not the bottleneck, not worth changing

### Layer 2: Quorum Certificates (attesting finalized blocks)
**Recommendation: Ed25519 aggregate-by-proof OR BLS (design decision needed)**

Options in order of implementation complexity:
1. **Ed25519 + STARK batch proof** — Keep Ed25519, prove N signatures in a STARK. Certificate = STARK proof. Works today-ish but Ed25519 is expensive non-native (~1.7M constraints per sig in BabyBear).
2. **BLS12-381 aggregate** — One 48-byte QC regardless of signer count. NOT post-quantum, NOT STARK-provable cheaply. But simple and proven (Ethereum beacon chain).
3. **Poseidon2-Schnorr over BabyBear^8** — ~85K constraints per sig, STARK-native, FROST-threshold-friendly. Our current `babybear8.rs` implementation direction. ~248-bit security (near but below 256-bit conservative target).
4. **leanSig/XMSS over Poseidon2** — Post-quantum, STARK-native (~154K constraints). Stateful (key reuse = catastrophic). Ethereum's current PQ direction.

### Layer 3: Proof-Carrying QCs (proving consensus happened inside a STARK)
**Recommendation: Poseidon2-based, either Schnorr^8 or XMSS**

This is only needed for:
- Cross-federation bridges (proving to federation B that federation A finalized something)
- Light clients that verify via STARK rather than trusting majority

## Key Insight: The Current WOTS+ QC AIR Is Unsound

The kimi review found:
- QC AIR only checks witness bits (`sig_valid = 1`), not actual signatures
- WOTS+ in 31-bit BabyBear gives only ~19-31 bit security
- The STARK framework's transition constraints are broken (cyclic domain issue)

**This means we currently have NO working proof-carrying QC.** The infrastructure exists but is non-functional.

## What Actually Matters for Pyana Right Now

Given federation size 4-50 nodes and the "home for AI" use case:

1. **Don't over-engineer the QC signature** — Ed25519 with O(n) sigs is fine for n≤50
2. **BLS is worth adding IF** we need light client proofs or bridge interop soon
3. **Poseidon2-Schnorr^8 is the long-term play** — STARK-native, threshold-friendly, already partially implemented
4. **Post-quantum can wait** — PQ is important but not urgent for a 4-50 node federation that can upgrade

## Cost Comparison (BabyBear STARK verification)

| Scheme | Constraints per verification | QC size (n=10) | QC size (n=50) | PQ? |
|--------|---------------------------:|----------------|----------------|-----|
| Ed25519 (non-native) | ~1,700,000 | 640 B | 3,200 B | No |
| BLS aggregate | N/A (pairing too expensive) | 48 B | 48 B | No |
| Poseidon2-Schnorr BabyBear^8 | ~85,000 | 640 B (or 1 threshold sig) | 3,200 B (or 1 threshold sig) | No |
| Poseidon2-XMSS (leanSig-style) | ~154,000 | ~30 KB | ~150 KB | Yes |
| RPO-Falcon512 | ~50,000 | ~7 KB | ~35 KB | Yes |

## Architectural Decision Points

1. **Do we need proof-carrying QCs at all right now?** If not, just use Ed25519 and move on.
2. **When we do need them**, Poseidon2-Schnorr^8 with FROST threshold is the best fit (native field, compact, threshold-friendly).
3. **For post-quantum future**, leanSig/XMSS over Poseidon2 is the Ethereum-aligned direction.
4. **BLS is orthogonal** — useful for compact wire-format QCs that DON'T need STARK verification.

## Open Questions

- Is BabyBear^8 (~248 bits) secure enough, or do we need degree-11 (~341 bits)?
- Should we pursue FROST threshold signing (complex DKG) or just aggregate-by-proof (simpler)?
- Is the monoculture risk of Poseidon2-everywhere acceptable?
- Do we actually need cross-federation bridges soon enough to justify proof-carrying QCs?
