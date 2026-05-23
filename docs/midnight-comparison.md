# Midnight vs Pyana: Architecture Comparison

Based on code review of midnightntwrk repos (midnight-zk, midnight-ledger, midnight-node, midnight-architecture) and pyana source.

## Architecture Comparison

| Aspect | Midnight | Pyana |
|--------|----------|-------|
| Proof system | Plonk (Halo2 fork) over Pluto/Eris with KZG commitments | STARK (BabyBear, FRI-based) + Kimchi/Pickles for recursion |
| Privacy model | Zerocash-style shielded pool (Zswap) + unshielded UTXO | Credential privacy: prove authorization without revealing delegation chain |
| Smart contracts | Compact (custom DSL) compiled to ZKIR, run on onchain VM (Impact) | Cell programs (Rust predicates + ZK circuits), Datalog policy |
| Consensus | Substrate-based: AURA block production + GRANDPA finality | Morpheus adaptive BFT (Lewis-Pye & Shapiro, 2-QC finality) |
| Token model | NIGHT (native unshielded), DUST (fee token), Zswap shielded coins, user-defined types | Macaroon/Biscuit capability tokens, attenuate-only delegation |
| Settlement | Cardano L1 (partner chain architecture, observes Cardano state) | Federation + optional EVM bridge (SP1 wraps STARK in Groth16) |
| State model | Global ledger: commitment Merkle tree + nullifier set + contract state | Sovereign cells: agents own state, can exit federation with full history |
| Curves | BLS12-381, JubJub (embedded), Pluto/Eris (proof system) | BabyBear field (STARK), BLS12-381 (hints/threshold), Ed25519 (signing) |

## What Midnight Does That Pyana Doesn't

- **Native shielded value transfer.** Zswap is a full Zerocash implementation with commitment trees, nullifier sets, encrypted coin ciphertexts, and atomic swaps. Production-grade fungible token privacy for arbitrary user-defined token types.
- **Cardano UTXO integration.** System transactions observe Cardano state (cNIGHT holdings, wallet registrations) and mirror them into the Midnight ledger. Enables cross-chain DUST generation from staked NIGHT on Cardano.
- **General-purpose programmable shielded contracts.** Compact compiles to a ZKIR that runs in a custom onchain VM. Contract calls produce ZK proofs that verify state transitions without revealing private inputs. This is "private smart contracts" in the Ethereum sense.
- **Proof aggregation.** The midnight-zk repo has a dedicated `aggregation` crate for batching multiple proofs.
- **Regulatory compliance angle.** Midnight markets itself as "rational privacy" -- selective disclosure by design. The contract model lets DApps enforce compliance rules (KYC gating, audit trails) while still using shielded state underneath.

## What Pyana Does That Midnight Doesn't

- **Capability-based authorization (not just value transfer).** Pyana's core primitive is attenuated delegation. You can grant a sub-agent read-only access to one service with a 1000-call budget expiring in an hour. Midnight has no equivalent -- it is a blockchain for value and contract state.
- **Sovereign cells / agent-owned state.** Cells can exit a federation carrying their full receipt chain. No global state lock-in. Midnight state lives exclusively on the Midnight chain.
- **Peer-to-peer without chain.** Two pyana agents can verify each other offline using STARK proofs and attested Merkle roots. Midnight requires the network for all verification (commitment tree roots, nullifier sets).
- **Intent-based discovery.** Private intent matching via commit-reveal and IT-PIR. Midnight has "intents" in the transaction-composition sense (grouping offers) but no discovery protocol.
- **Federation-as-notary (not blockchain).** Pyana's federation is an ordering/attestation service. Agents hold their own state. Midnight is a full blockchain with global state consensus.
- **Object-capability confinement.** C-lists, three-party introduction, sealer/unsealer patterns. The authorization structure IS the computation structure. Midnight separates authorization (signatures/proofs) from computation (contract VM).

## Integration Possibilities

**Could pyana use Midnight for settlement/stablecoins?** Plausible. Midnight's user-defined token types mean a stablecoin issuer could deploy on Midnight with shielded transfer. Pyana could observe Midnight state (the way Midnight observes Cardano) and treat Midnight coin commitments as backing for pyana notes. The bridge direction is: pyana cell locks a note -> federation attests -> Midnight contract mints shielded coin (or vice versa).

**Could proofs cross-verify?** Difficult. Different proof systems (Plonk/KZG vs STARK/FRI) with different fields (Pluto/Eris vs BabyBear). Neither can natively verify the other cheaply. A STARK-in-Plonk wrapper or Plonk-in-STARK wrapper would be needed -- roughly the same cost as pyana's existing SP1->Groth16 EVM path. Not free, but not impossible.

**Bridge architecture?** The cleanest path is the same pattern Midnight uses with Cardano: a system-transaction observer. A pyana federation node watches Midnight blocks, mirrors relevant events (coin movements to a designated contract address) into pyana state. This avoids needing cross-system proof verification entirely -- it is trust-in-observation, same as Midnight's own Cardano bridge.

**Could pyana's capability model layer ON TOP of Midnight's privacy?** Yes, and this is arguably the most natural integration. Midnight handles value privacy (who has how much of what). Pyana handles authorization privacy (who is allowed to do what, and who delegated it). A DApp could store assets on Midnight (shielded) and use pyana tokens to gate access to contract entry points. The pyana STARK proves "I hold authority to call this function" and the Midnight Plonk proof proves "this state transition is valid." They compose at the application level, not the proof-system level.

## The Cardano UTXO Angle

Midnight's unshielded token model (Night) is standard UTXO: value + owner + type + intent_hash + output_no. Pyana's notes (private cells with committed conservation) are also UTXO-style. The structural similarity is real -- both track unspent outputs with nullifier-like spending mechanisms. However, Midnight's shielded side (Zswap) uses commitment trees and nullifier sets directly modeled on Zcash/Sapling, while pyana's note model is lighter (4-ary Merkle, BLAKE3/Poseidon2).

The "near native BTC treasury on Cardano" angle is about Cardano's extended UTXO model enabling multi-asset custody without wrapping. Midnight inherits this via the partner chain bridge. Pyana could potentially observe the same Cardano state that Midnight does, but has no Cardano relationship currently. The natural path is: Cardano -> Midnight (existing bridge) -> Pyana (new bridge), not Cardano -> Pyana directly.

## The EVM Bridge Comparison

Pyana has `./chain` (SP1 wraps STARK in Groth16, ~200K gas verification on Base/EVM). Midnight settles to Cardano, not EVM. These are orthogonal settlement layers. Both could be supported simultaneously -- a pyana deployment could bridge to EVM via SP1 AND observe Midnight state for Cardano-side settlement. The question is which ecosystem has the liquidity and stablecoin access you need. Today: EVM (by far). Tomorrow: unclear whether Midnight/Cardano achieves significant DeFi liquidity.

**Should we care about one more than the other?** EVM bridge is more immediately useful (USDC, existing DeFi). Midnight bridge is more architecturally aligned (both are privacy-preserving, both use ZK proofs, both have UTXO models). If Midnight achieves meaningful adoption, the pyana<->Midnight bridge would be technically cleaner than pyana<->EVM because both systems already understand shielded state. But EVM has the network effects today.

## Confidence Levels

- Midnight proof system (Plonk/Halo2, KZG, Pluto/Eris): **confirmed from code** (ADR-0013, midnight-zk repo)
- Midnight consensus (Substrate AURA/GRANDPA): **confirmed from code** (midnight-node README, chain specs)
- Midnight Cardano relationship (partner chain, system transactions): **confirmed from spec** (cardano-system-transactions.md)
- Midnight shielded model (Zerocash-style Zswap): **confirmed from spec** (zswap.md, coin-structure code)
- Compact language details: **limited visibility** (repo only hosts releases, source at LFDT-Minokawa/compact)
- Midnight's "data protection regulation" compliance story: **speculative** (marketing claim, not visible in architecture docs beyond standard selective-disclosure patterns)
- Integration feasibility: **architectural assessment**, not tested
