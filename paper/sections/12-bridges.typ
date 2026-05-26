// =============================================================================
// Section 12: Cross-Chain Bridges
// =============================================================================

= Cross-Chain Bridges <sec-bridges>

== Bridge Architecture

Dragon's Egg connects to external chains via _proof translation_---not consensus bridging. Each bridge converts a Dregg STARK proof into a format the remote chain can verify natively. No relay committee, no multi-sig, no trusted oracle. The remote chain verifies a mathematical proof of Dregg state validity.

The bridge's portable note proof `PortableNoteProof` has public inputs `(nullifier, attested_source_root, destination_federation, value, asset_type)`. The `destination_federation` field is now both surfaced in PI *and algebraically bound* by the AIR (closes threat T6 from the executor-honesty audit and `AUDIT-nullifiers.md §5`). A proof addressed to federation A cannot be replayed at federation B.

The cross-federation trust path requires the destination federation to have an entry in its `KnownFederations` registry for the source federation (see @sec-federation). Without registry presence, the destination cannot verify the source's `AttestedRoot`---the source `federation_id` in the attestation is bound algebraically (Lane D unification: `federation_id = BLAKE3(committee_pubkeys || epoch)`), so an attacker cannot mint attestations for a federation it doesn't control.

Bridges are classified by trust level:

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Level*], [*Property*], [*Mechanism*]),
    [Level 1 (observational)], [Remote chain observes Dregg state roots], [Attestation posting],
    [Level 1.5 (optimistic)], [State accepted with dispute window], [Bond + fraud proof],
    [Level 2 (proof-verified)], [Remote chain verifies STARK natively], [Proof translation],
  ),
  caption: [Bridge trust levels. Level 2 provides the strongest guarantee: the remote chain independently verifies correctness.],
)

== EVM Bridge (Level 2 via SP1/Groth16) <sec-evm-bridge>

=== Architecture

The EVM bridge achieves Level 2 trust by wrapping Dregg STARK proofs in Groth16---the only proof system with mature EVM verification contracts at reasonable gas cost ($approx 200"K"$ gas).

The pipeline:

+ *STARK generation* (off-chain): The Effect VM proves the state transition over BabyBear/FRI.
+ *SP1 guest program* (off-chain): A RISC-V zkVM program verifies the STARK inside SP1. The guest reads the STARK proof, runs the FRI verifier, checks Poseidon2 commitments, and outputs a boolean verdict plus the state commitment.
+ *Groth16 extraction* (off-chain): SP1's prover converts the RISC-V execution trace into a Groth16 proof (BN254 curve, compatible with EVM precompiles).
+ *On-chain verification* (EVM): The Groth16 proof is verified by Succinct's deployed SP1 Verifier Gateway contract on Ethereum/Base.
+ *State update* (EVM): The Dregg bridge contract updates the sovereign cell's commitment on-chain.

=== On-Chain Components

The EVM deployment consists of:

- *Bridge contract*: Stores cell state commitments (32 bytes each), accepts verified state updates, manages deposit/withdrawal logic.
- *VK registry*: Stores verification keys for different circuit versions. Governance-controlled updates via multisig.
- *Incremental Merkle tree*: For EVM-to-Dregg deposits. $O(log n)$ insertions, provable membership for withdrawal on Dregg side.
- *Commit-reveal frontrunning protection*: Deposits use commit-reveal to prevent sandwich attacks.

=== Gas Analysis

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, right, left),
    table.header([*Operation*], [*Gas Cost*], [*Notes*]),
    [Groth16 verification], [$approx 200"K"$], [Via ecPairing precompile (EIP-197)],
    [State commitment update], [$approx 22"K"$], [Single SSTORE (cold)],
    [Deposit (commit phase)], [$approx 45"K"$], [Merkle tree insertion + commitment],
    [Deposit (reveal phase)], [$approx 35"K"$], [Reveal + balance credit],
    [Withdrawal], [$approx 220"K"$], [Proof verification + ETH/token transfer],
  ),
  caption: [EVM bridge gas costs. Groth16 verification dominates at $approx 200"K"$ gas (approximately \$0.50 at 10 gwei on L2).],
)

=== Sovereign Cells on EVM

A Dregg sovereign cell can exist as an on-chain entity:

- The bridge contract stores the cell's 32-byte state commitment.
- The cell operates off-chain (generating turns, proofs).
- Periodically (or on demand), the cell posts a state update with a Groth16 proof.
- EVM contracts can condition execution on the cell's proven state (e.g., "execute this DeFi operation only if Dregg cell X has authorized it").

This enables hybrid applications: Dregg for privacy and authorization, EVM for DeFi composability.

== Mina Bridge (Level 2, Pickles Recursion) <sec-mina-bridge>

=== Architecture

The Mina bridge achieves Level 2 trust natively: Mina's proof system and Dregg's Kimchi backend share the same Pasta curve cycle (Pallas/Vesta). No wrapping tax beyond the Kimchi circuit overhead.

The pipeline:

+ *STARK generation* (Dregg): BabyBear/FRI proof of the state transition.
+ *Kimchi wrapping* (Dregg): The STARK verifier is encoded as a Kimchi circuit ($approx 30"K"$ gates) over Pasta curves. The Kimchi circuit takes the STARK proof as witness and outputs accept/reject.
+ *Pickles recursion* (Dregg): The Kimchi proof is accumulated into a Pickles recursive proof---constant size ($approx 10$ KiB), independent of the underlying STARK complexity.
+ *Mina verification* (Mina): The Pickles proof is natively verifiable by Mina validators and zkApps. No custom verifier needed---standard Mina infrastructure.

=== STARK-in-Pickles Pipeline

The critical component is the Kimchi circuit that verifies a BabyBear STARK:

*Inputs (public)*: Pre-state commitment, post-state commitment, nullifier.

*Witness (private)*: The full STARK proof (FRI layers, Merkle paths, evaluation points).

*Circuit structure*:
- FRI proximity check: Verify that committed polynomials are close to low-degree ($approx 15"K"$ gates).
- Poseidon2 evaluation: Recompute hash commitments for proof binding ($approx 8"K"$ gates).
- Constraint check: Verify AIR constraints at evaluation points ($approx 7"K"$ gates).

The Kimchi proof over Pallas is then accumulated into the Pickles IPA recursive structure. This is _assisted recursion_: the Dregg prover does the expensive work (STARK generation + Kimchi wrapping), and the Mina side simply verifies a standard Pickles proof.

=== Integration with Mina zkApps

A Dregg cell can appear as a Mina zkApp account:

- The cell's state commitment maps to the zkApp's on-chain state field.
- State updates are authorized by Pickles proofs (generated by the Dregg STARK-in-Pickles pipeline).
- Mina validators verify the Pickles proof as part of normal block validation.
- No special infrastructure on Mina---just a standard zkApp with a Dregg-generated proof method.

=== Curve Compatibility

The Pasta cycle (Pallas: $y^2 = x^3 + 5$ over $FF_p$, Vesta: $y^2 = x^3 + 5$ over $FF_q$ where $p = |"Vesta"|$ and $q = |"Pallas"|$) enables efficient recursive composition. The base field of one curve equals the scalar field of the other---eliminating non-native arithmetic overhead that plagues cross-curve recursion.

== Midnight/Cardano Bridge (Level 1.5, Optimistic) <sec-midnight-bridge>

=== Architecture

The Midnight bridge uses optimistic acceptance with dispute: state transitions are posted with a bond and accepted after a dispute window unless challenged.

=== Level 1 (Implemented): Attestation Bridge

Dregg state roots are attested on Midnight as observation-based data, following the same pattern as Midnight's Cardano bridge:

+ A relay posts Dregg's latest attested root (from the reference group's $tau_"unified"$).
+ Midnight validators record the attestation.
+ Any Midnight contract can read the attested root and condition logic on it.

This provides read-only observation: "Dregg state $S$ existed at height $H$." No proof of _validity_---just existence.

=== Level 1.5 (Implemented): Optimistic Acceptance

A stronger guarantee with economic backing:

+ A Dregg state transition is posted to Midnight with a bond ($B_"submit"$).
+ During the dispute window ($W_"dispute"$, default 24 hours):
  - Any party can challenge by presenting evidence of invalidity.
  - Challenge requires a counter-bond ($B_"challenge" >= B_"submit" \/ 2$).
+ If challenged: the submitter must produce a full STARK proof within the response window ($W_"response"$, default 12 hours).
+ *Proof valid*: Challenger's bond slashed. Submitter's bond returned.
+ *Proof invalid or absent*: Submitter's bond slashed. Transition rejected. Challenger compensated.

=== Level 2 (Designed): ZKIR Native Verification

The DSL's ZKIR v3 backend compiles Dregg constraint programs directly into Midnight-compatible contracts:

+ Dregg's circuit descriptors compile to ZKIR v3 bytecode.
+ A FRI verifier written in ZKIR executes on Midnight's proof system.
+ The verifier checks the Dregg STARK proof natively within Midnight's execution environment.
+ Result: Level 2 trust without optimistic assumptions.

Implementation awaits ZKIR v3 stabilization on Midnight's side. The Dregg DSL backend is complete; the integration requires Midnight's runtime to expose the necessary primitives.

=== Midnight-Cardano Synergy

Since Midnight itself bridges to Cardano, the Dregg-Midnight bridge transitively provides Dregg-Cardano connectivity:

$ "Dregg" arrow.r^("L1.5") "Midnight" arrow.r^("native") "Cardano" $

A Dregg cell's state can influence Cardano smart contracts (via Midnight as intermediary) without Dregg directly interacting with Cardano's UTXO model.

== Bridge Comparison

#figure(
  table(
    columns: (auto, auto, auto, auto, auto),
    align: (left, center, left, left, left),
    table.header([*Bridge*], [*Level*], [*Proof System*], [*Cost*], [*Finality*]),
    [EVM], [2], [SP1/Groth16], [$approx 200"K"$ gas], [$approx 12$ min (L1)],
    [Mina], [2], [Kimchi/Pickles], [Native], [$approx 3$ min],
    [Midnight], [1.5], [Optimistic], [Bond], [24h dispute window],
  ),
  caption: [Bridge comparison. EVM and Mina achieve full proof verification; Midnight uses economic security with a path to Level 2.],
)

== Security Analysis

=== EVM Bridge Safety

The EVM bridge is safe if:
- SP1's RISC-V execution is correct (zkVM soundness).
- The Groth16 proof system is sound (BN254 discrete log is hard).
- The bridge contract correctly checks the verification result.

An invalid Dregg state transition cannot produce a valid Groth16 proof (with overwhelming probability). The on-chain verifier rejects all invalid proofs.

=== Mina Bridge Safety

The Mina bridge is safe if:
- Kimchi/IPA over Pasta curves is sound.
- Pickles recursion is sound.
- The Dregg STARK is sound (BabyBear/FRI).

The proof chain (STARK $->$ Kimchi $->$ Pickles) composes soundness: each layer is independently sound, and the composition preserves soundness.

=== Midnight Bridge Safety

The Level 1.5 bridge is safe if:
- The dispute window is long enough for honest challengers to respond.
- At least one honest party monitors submissions (liveness assumption).
- Bond amounts are sufficient to incentivize monitoring.

The economic security parameter: an attacker must post $B_"submit"$ and hope no one challenges within $W_"dispute"$. If any honest monitor exists, the attack fails and the attacker loses their bond.
