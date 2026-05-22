# Post-Quantum Roadmap

## Current State (May 2026)

| Layer | Scheme | PQ? | Notes |
|-------|--------|-----|-------|
| ZK proofs (STARKs) | BabyBear + Poseidon2 + FRI | **Yes** | Hash-based, no curves |
| Federation QCs | BLS12-381 via `hints` | **No** | Pairing-based; broken by Shor |
| Individual node identity | Ed25519 | **No** | Broken by Shor |
| Sealed secrets | X25519 + ChaCha20-Poly1305 | **No** | X25519 broken by Shor |
| Macaroon HMAC chain | HMAC-SHA256 | **Yes** | Symmetric; Grover halves security (still 128-bit) |
| Merkle commitments | BLAKE3 / Poseidon2 | **Yes** | Hash-based |

**Summary:** The proof system and commitment layer are PQ. The signature/key-agreement layers are not.

## Why This Is Acceptable for v1

The PQ-vulnerable layers (BLS, Ed25519, X25519) are all **within trust boundaries**:
- Federation members trust each other by definition (they joined the federation)
- Sealed secrets are between the tokenizer daemon and its own key
- Ed25519 node identity is within the consensus cluster

The layer that goes **over the wire to untrusted verifiers** — the STARK presentation proof — is fully hash-based and PQ-secure. An external verifier never sees BLS signatures or Ed25519; they see a STARK proof bound to public inputs.

## Migration Path

### Phase 1: Scheme Agility (now)

Abstract signature operations behind traits:
```rust
pub trait ThresholdScheme {
    type PublicKey;
    type SecretShare;
    type Signature;
    type Committee;
    
    fn setup(members: &[PublicKey], threshold: usize) -> Committee;
    fn sign_share(committee: &Committee, share: &SecretShare, msg: &[u8]) -> PartialSig;
    fn aggregate(committee: &Committee, shares: &[PartialSig]) -> Option<Signature>;
    fn verify(committee: &Committee, msg: &[u8], sig: &Signature) -> bool;
}
```

### Phase 2: Lattice Threshold Sigs (when mature)

Target schemes for federation QCs (4-64 node committees):
- **Hermine**: FROST-like, 2-round, identifiable aborts, DKG, proactive refresh. Up to 64 signers.
- **Oriole**: Partially non-interactive (one message-dependent round). Adaptively secure.
- **TalonG**: Best bandwidth at large thresholds (26.9 KB at t=1024).

Timeline: When NIST threshold call produces final packages (late 2026 / 2027).

### Phase 3: ML-DSA Individual Identity

Replace Ed25519 node identity with ML-DSA (FIPS 204) once threshold ML-DSA is standardized:
- **Mithril/2026/013**: ML-DSA-compatible threshold, <20ms signing, up to 8 parties
- **Quorus/2025/1163**: Honest-majority MPC, up to 64 signers, UC-secure

### Phase 4: PQ Key Agreement (if needed)

Replace X25519 in tokenizer with ML-KEM (FIPS 203) for sealed secrets. This is straightforward since the sealed-secret protocol is simple (one ephemeral + one static key).

## What We Cannot Do PQ (Yet)

**Dynamic arbitrary-subset threshold signing without per-committee DKG.**

The Dyna-hinTS model (give every agent one long-term key, choose any threshold subset later, no committee-specific setup) has no PQ equivalent. The lattice line assumes fixed committees.

For pyana this is acceptable because:
- Federations are relatively stable (nodes don't change per-request)
- Cross-silo presentation uses STARK proofs (PQ), not threshold sigs
- The "dynamic subset" need is at the authorization layer, handled by the ZK proof

## Key Insight

The architecture separates concerns correctly:
- **Trust layer** (federation consensus): classical threshold sigs are fine here because you already trust the committee members
- **Verification layer** (cross-silo presentation): STARKs are PQ — this is what untrusted parties see
- **The PQ gap is inside the trust boundary**, not at the untrusted-verifier interface
