# Midnight Integration Insights & Action Plan

## What's Least Zcash/Midnight-Like About Pyana

### Critical Gaps (ordered by severity)

1. **No encrypted note ciphertexts on-chain.** Recipients can't passively scan to discover notes. Requires out-of-band communication. Midnight publishes encrypted CoinInfo under the recipient's encryption key alongside every commitment.

2. **No incremental commitment tree.** Nullifier set rebuilds Merkle tree from scratch every proof generation — O(N). No root history means proofs invalidated by ANY new note creation between generation and submission.

3. **Asset type is PUBLIC on committed notes.** `pub asset_type: u64` on `CommittedNote` defeats multi-asset privacy. Midnight hides type inside the commitment preimage, uses per-type generators.

4. **No transient notes.** Can't create-and-spend within one transaction without hitting the global tree. Adds latency and unnecessary tree growth. Midnight's ZswapTransient allows intra-tx spends.

5. **No "indistinguishable pool" property.** Cells and notes are structurally different on-chain. Observers can distinguish value transfers from state transitions. Midnight's shielded pool makes all operations look identical.

## Midnight Architecture Summary (from code review)

- **Proof system**: PLONK (Halo2 fork) over BLS12-381 with KZG commitments
- **Circuit IR**: ZKIR v3 (SSA-based, typed wires, gate references). Compiled from Compact (TypeScript-like DSL)
- **Privacy**: Zerocash-style Zswap (commitment tree + nullifier set + encrypted ciphertexts)
- **Settlement**: Substrate-based node, bridges to Cardano via Partner Chains (observation-based)
- **Token model**: NIGHT (unshielded UTXO) + shielded coins (Zswap) + user-defined types
- **Curves**: BLS12-381 + JubJub embedded curve (for in-circuit ECC)

## What We Should Learn From Midnight

### Immediate (low effort, high impact)

1. **Commitment tree root history with TTL** — Accept proofs against recent roots (not just current). Pattern: `Vec<(root, height)>` with configurable depth (Midnight uses 30). Without this, the system is unusable under any real concurrency.

2. **Hide asset_type in committed preimage** — Remove `pub asset_type: u64` from `CommittedNote`. It's already committed via the per-type Pedersen generator. Public field is redundant and privacy-breaking.

3. **Binding randomness on transaction bundles** — Single scalar that ties all Pedersen commitments to the full transaction context. Prevents proof-stripping. Our conservation proof has `excess_blinding` but no explicit transaction binding.

### Medium-term (medium effort, high impact)

4. **Incremental append-only note tree** — Replace rebuild-from-scratch with persistent tree using `first_free_index`. Enable witness-diff subscriptions for note holders. Copy Midnight's `MerkleTreeCollapsedUpdate` pattern.

5. **Encrypted note ciphertexts** — On note creation, encrypt `(value, asset_type, randomness)` under recipient's view key (X25519 DH + BLAKE3 CTR). Publish alongside commitment. Enables passive scanning.

6. **Transient notes** — Allow intra-transaction create+spend without global tree. Reduces latency, prevents unnecessary tree growth.

7. **Define Midnight bridge message format** — `MidnightBridgeMessage { nullifier, amount_stars, recipient_zswap_pk, federation_attestation }`. Mirror c2m-bridge's governance-approval pattern.

### Longer-term (high effort, high impact)

8. **BLS12-381 value commitment wrapper** — For bridge-facing operations, produce Pedersen commitments on JubJub matching Midnight's `value_commitment` format. Verifiable within Midnight's circuit infrastructure.

9. **Observation-based Midnight bridge** — Federation node watches Midnight blocks via Substrate RPC, detects bridge contract events, mirrors into pyana. Same trust model as Midnight's own Cardano bridge.

10. **In-circuit Keccak-256** — For EVM signature/state proof verification inside circuits. Midnight has this. Substantial work for STARK (many rows per hash) but existing implementations exist.

## Proof System Interop

### Directions

| Direction | Feasibility | Approach |
|-----------|-------------|----------|
| STARK inside Pickles | Medium | `stark_in_pickles.rs` scaffold exists. BabyBear embeds trivially in Pasta (31-bit in 255-bit). ~29K gates per poseidon_stark.rs |
| Pickles inside STARK | Impractical | 256-bit curve ops in 31-bit field = millions of constraints. Would need SP1/zkVM approach |
| STARK inside Midnight (Plonk/KZG) | Medium | Write STARK verifier as ZKIR program (their stdlib has arbitrary hash gadgets). Or use SP1→Groth16→BN254 precompile if Midnight adds one |
| Midnight inside STARK | Impractical | Same problem as Pickles (BLS12-381 curve ops in BabyBear) |
| Application-level composition | Easy | Pyana proves authorization (STARK), Midnight proves value transfer (Plonk). They share a public commitment hash. No cross-proof-system verification |

### Recommended: Application-Level Composition

Pyana handles authorization privacy. Midnight handles value privacy. They compose at the application level:
- Shared: a Pedersen commitment to the value being transferred
- Pyana's proof: "I am authorized to transfer this commitment" (STARK)
- Midnight's proof: "This commitment's value is conserved in the shielded pool" (Plonk)
- Bridge: the commitment is the interop atom. Same bytes on both sides.

## DSL → Kimchi Gap (Must Fix)

The DSL currently ONLY produces BabyBear STARKs. `gen_kimchi.rs` outputs a descriptor nobody consumes. The kimchi_native backend hand-writes everything. This is a regression — the DSL should make Kimchi proofs EASIER, not ignore them.

### Bridge needed:
1. `KimchiCircuitDescriptor` → `Vec<CircuitGate<Fp>>` converter (coefficient cast + wiring)
2. DSL witness → Kimchi witness matrix `[Vec<Fp>; COLUMNS]` translator
3. Integration with `prove_recursive_step` for Pickles recursion
4. Tests proving DSL-generated circuits through the full Kimchi→Pickles path

## Priority Order

1. Fix DSL→Kimchi bridge (regression from old system)
2. Commitment tree root history (blocks real usage)
3. Hide asset_type (trivial privacy win)
4. Incremental note tree (scalability)
5. Encrypted ciphertexts (UX for recipients)
6. Midnight bridge message format (interop foundation)
7. STARK-in-Pickles completion (enables recursive composition across proof systems)
