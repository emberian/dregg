# apps/

Real applications built on pyana. Not demos — working systems.

## Planned

### `bounty-board/`
Federated bounty system where:
- Issuers post bounties with attenuated capability tokens as payment
- Workers claim bounties by presenting credentials (standing proof)
- Completion verified via receipt chain (proof of work done)
- Payment released atomically via conditional turn
- Privacy: workers can prove qualifications without revealing identity

### `review-gateway/`
Pyana-backed verifier for the Castalia/Zenith Review SDK:
- Replaces runtime access codes with attenuated capabilities
- secS verifier checks Datalog policy before granting session
- Receipt chain makes review submissions auditable
- Progressive path: access code → signed credential → wallet credential → full pyana proof

### `passport/`
Anonymous credential gate (inspired by Midnight Passport):
- Prove attributes (age, membership, standing) without revealing identity
- On-chain verification via SP1/Base for token-gated access
- Federation-issued credentials, privately presented
- Sybil resistance via nullifier-based presentation tracking

### `private-transfer/`
Private value transfer on Base:
- Bridge USDC/ETH in via PyanaVault
- Transfer privately inside pyana (notes + nullifiers)
- Bridge out with SP1-wrapped spending proof
- No observer learns sender, receiver, or amount
