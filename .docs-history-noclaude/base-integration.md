# Base EVM Integration: Anonymous Credentials + Private Value Transfer

## Overview

This document describes pyana's flagship integration with Base (Coinbase's L2): a system
where users can hold private value (USDC/ETH notes) and present anonymous credentials
on-chain, with all privacy guarantees backed by STARK proofs wrapped in SP1 for EVM
verification.

The integration demonstrates what makes pyana unique: not just private transfers (which
Tornado Cash/Railgun do), but **anonymous credential presentation on-chain** -- proving
facts about yourself to smart contracts without revealing your identity.

## Architecture

```
                         BASE (L2)
    ┌─────────────────────────────────────────────────────┐
    │                                                     │
    │  PyanaVault.sol         PyanaCredentialGate.sol      │
    │  ┌──────────────┐      ┌────────────────────────┐   │
    │  │ deposit()    │      │ verifyCredential()     │   │
    │  │ withdraw()   │      │ mintWithCredential()   │   │
    │  └──────┬───────┘      └────────────┬───────────┘   │
    │         │                           │               │
    │         │     SP1 Verifier Gateway  │               │
    │         │     ┌─────────────────┐   │               │
    │         └────>│ verifyProof()   │<──┘               │
    │               └────────┬────────┘                   │
    └────────────────────────┼────────────────────────────┘
                             │
                    Groth16 proof (32 bytes vkey + ~260 bytes proof)
                             │
                    ┌────────┴────────┐
                    │  SP1 Prover     │
                    │  (host-side)    │
                    │                 │
                    │  Wraps STARK    │
                    │  in Groth16     │
                    └────────┬────────┘
                             │
                    STARK proof (~20-50 KiB)
                             │
              ┌──────────────┴──────────────┐
              │                             │
    ┌─────────┴─────────┐       ┌──────────┴──────────┐
    │  Note Spending     │       │  Credential         │
    │  Circuit           │       │  Presentation       │
    │                    │       │  Circuit             │
    │  Proves:           │       │  Proves:            │
    │  - Note ownership  │       │  - Ring membership  │
    │  - Nullifier valid │       │  - Predicate holds  │
    │  - Conservation    │       │  - Credential valid │
    └────────────────────┘       └─────────────────────┘
              │                             │
              │         PYANA LAYER         │
    ┌─────────┴─────────────────────────────┴─────────┐
    │                                                  │
    │  Notes (private value)    Credentials (facts)    │
    │  ┌─────────────────┐     ┌───────────────────┐   │
    │  │ commitment      │     │ federation root   │   │
    │  │ nullifier set   │     │ predicate proofs  │   │
    │  │ note tree       │     │ ring membership   │   │
    │  └─────────────────┘     └───────────────────┘   │
    │                                                  │
    │  Federation consensus (attested roots)           │
    └──────────────────────────────────────────────────┘
```

## Use Cases

### 1. Private USDC Transfers (Bridge In -> Transfer -> Bridge Out)

**Flow:**
1. Alice calls `PyanaVault.deposit(USDC, 100, noteCommitment)` on Base
2. The vault locks 100 USDC and emits `Deposit(token, amount, noteCommitment)`
3. Pyana federation observes the deposit event and adds `noteCommitment` to the note tree
4. Alice can now transfer privately inside pyana (nullifier + new note, standard UTXO model)
5. Bob wants to withdraw: burns his note (reveals nullifier), generates STARK proof of valid spend
6. SP1 wraps the STARK proof into a Groth16 proof
7. Bob calls `PyanaVault.withdraw(USDC, 30, bobAddress, sp1Proof)` on Base
8. The vault verifies the proof via the SP1 Verifier Gateway, then releases 30 USDC to Bob

**What's hidden:**
- Alice's identity (she deposited, but deposits are common -- many people deposit)
- The transfer from Alice to Bob (happens entirely inside pyana, invisible on-chain)
- Bob's connection to Alice (he withdraws with a proof, no link to the deposit)
- The intermediate transfers (could be 1 hop or 100 hops)

### 2. Anonymous Age Verification for On-Chain Gating

**Flow:**
1. Alice obtains an "age >= 18" credential from a federation issuer (e.g., identity provider)
2. Alice generates an anonymous presentation:
   - Ring membership: proves she's IN the federation without revealing WHICH member
   - Predicate: proves `age >= 18` via committed-threshold circuit (exact age hidden)
   - Blinding: presentation is unlinkable to her credential serial
3. The presentation STARK is wrapped in SP1 -> Groth16
4. Alice calls `CredentialGate.verifyCredential(federationRoot, predicateHash, sp1Proof)` on Base
5. The contract verifies via SP1 Verifier and returns `true`
6. A downstream contract (e.g., NFT mint) gates on this verification

**What's hidden from the contract:**
- Alice's identity (ring membership hides which federation member she is)
- Alice's actual age (only "age >= 18" is proven, not the exact value)
- Alice's credential serial number (blinded in the presentation)
- Whether Alice has used this gate before (unlinkable presentations)

### 3. Anonymous Credential-Gated NFT Mints

**Flow:**
1. An NFT project requires "verified human" credentials from a specific federation
2. Alice holds a "verified human" credential from that federation
3. Alice generates an anonymous presentation proving membership
4. Calls `CredentialGate.mintWithCredential(tokenId, federationRoot, predicateHash, sp1Proof)`
5. The contract verifies the credential, then mints the NFT to a fresh address

**What's hidden:**
- Which federation member Alice is (ring membership)
- Any other attributes of Alice's credential
- Link between multiple mints (each presentation is unlinkable)

### 4. Private Voting (Token-Weighted)

**Flow:**
1. Governance contract wants to gate voting on "holds >= 1000 USDC in pyana"
2. Alice generates an anonymous presentation:
   - Proves she has a note with value >= 1000 (committed-threshold on note value)
   - Proves the note is in the current note tree (Merkle membership)
   - Does NOT reveal which note, or the exact balance
3. SP1 wraps the proof; Alice submits her vote with the proof
4. The contract verifies the credential and records the vote

**Double-vote prevention:**
- The presentation includes a deterministic "vote nullifier" derived from (note_commitment, proposal_id)
- The contract stores used vote-nullifiers; same note cannot vote twice on same proposal
- But the vote nullifier is unlinkable to the spend nullifier (different derivation domain)

## Contract Interfaces

### IPyanaVault.sol

The vault holds bridged assets. Deposits create note commitments; withdrawals require
SP1-wrapped STARK proofs of valid note spending.

```solidity
interface IPyanaVault {
    event Deposit(address indexed token, uint256 amount, bytes32 noteCommitment, uint256 leafIndex);
    event Withdrawal(address indexed token, uint256 amount, address indexed recipient, bytes32 nullifier);

    function deposit(address token, uint256 amount, bytes32 noteCommitment) external;
    function withdraw(address token, uint256 amount, address recipient, bytes calldata sp1Proof) external;
    function isNullifierUsed(bytes32 nullifier) external view returns (bool);
}
```

### IPyanaCredentialGate.sol

Anonymous credential verification. The SP1 proof wraps a STARK proving:
- Ring membership in a federation (prover is a member but identity hidden)
- A predicate holds (e.g., age >= 18, balance >= X, membership in set Y)

```solidity
interface IPyanaCredentialGate {
    event CredentialVerified(bytes32 indexed federationRoot, bytes32 indexed predicateHash, bytes32 nullifier);

    function verifyCredential(
        bytes32 federationRoot,
        bytes32 predicateHash,
        bytes calldata sp1Proof
    ) external view returns (bool);

    function mintWithCredential(
        uint256 tokenId,
        bytes32 federationRoot,
        bytes32 predicateHash,
        bytes calldata sp1Proof
    ) external;
}
```

## Proof Flow Detail

### Note Withdrawal Proof

The SP1 guest program verifies:
1. **Nullifier derivation**: `nullifier = H(commitment, spending_key, nonce)` -- prover knows the key
2. **Note tree membership**: `commitment` is in the attested note tree (Merkle path)
3. **Value correctness**: The note's value field matches the withdrawal amount
4. **Conservation**: Input value == output value (no inflation)

Public inputs (visible to the contract):
- `nullifier` (for double-spend prevention)
- `note_tree_root` (which state snapshot the proof is against)
- `withdrawal_amount`
- `recipient_address` (bound into the proof to prevent front-running)

### Credential Presentation Proof

The SP1 guest program verifies:
1. **Ring membership**: Prover's key is in a Merkle tree of federation members
2. **Credential binding**: The credential is validly issued (signature chain or fact commitment)
3. **Predicate satisfaction**: The private attribute satisfies the public predicate
   - For threshold: `value >= threshold` via bit decomposition (committed-threshold AIR)
   - For set membership: `value IN set` via Merkle membership
   - For equality: `H(value) == published_hash`

Public inputs (visible to the contract):
- `federation_root` (which federation's membership tree)
- `predicate_hash` (what's being proven, e.g., `keccak256("age >= 18")`)
- `presentation_nullifier` (optional, for sybil resistance per-action)

## Security Properties

| Property | Mechanism |
|----------|-----------|
| No double-spend | Nullifier set (on-chain for withdrawals, federation for transfers) |
| No inflation | Conservation constraint in the note spending circuit |
| Sender privacy | Nullifiers are unlinkable to commitments |
| Receiver privacy | New commitments reveal nothing about recipient |
| Amount privacy | Values are hidden inside commitments |
| Credential anonymity | Ring membership proof (log-size in ring) |
| Predicate privacy | Only the predicate type is revealed, not the value |
| Unlinkability | Each presentation uses fresh randomness |
| Front-running resistance | Recipient address bound into the proof |

## Gas Costs (Estimated)

| Operation | Gas |
|-----------|-----|
| SP1 Groth16 verification | ~200k |
| Deposit (ERC-20 transfer + event) | ~80k |
| Withdrawal (verify + transfer + nullifier store) | ~300k |
| Credential verification (verify only) | ~200k |
| Mint with credential (verify + mint) | ~350k |

## Implementation Status

- [x] SP1 guest program (STARK verifier in RISC-V zkVM): `chain/program/`
- [x] Host-side proof wrapping (mock + real): `chain/src/prove.rs`
- [x] On-chain verification via alloy: `chain/src/verify.rs`
- [x] Note privacy system (commitments, nullifiers, STARK proofs): `cell/`, `circuit/`
- [x] Anonymous credential presentation (ring membership, predicates): `bridge/src/present.rs`
- [x] Committed-threshold proofs: `circuit/src/committed_threshold.rs`
- [ ] Credential-specific SP1 wrapping: `chain/src/credential.rs` (this PR)
- [ ] Solidity contract interfaces: `chain/contracts/` (this PR)
- [ ] Vault implementation (full Solidity)
- [ ] Deposit event watcher (federation integration)
- [ ] Production deployment on Base Sepolia
