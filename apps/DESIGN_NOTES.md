# Apps Design Notes

## Bounty Board: Fully Anonymous Workers

The issuer should NEVER learn the worker's identity. Not at claim, not at delivery, not at payment.

### The Anonymous Delivery Scheme

1. **Claim**: Worker posts `worker_commitment = Poseidon2(worker_key, bounty_id, randomness)`. Issuer sees an opaque 32-byte commitment. Cannot correlate across bounties (fresh randomness each time).

2. **Deliver**: Worker posts completion evidence + STARK proof that work satisfies the bounty spec. The proof binds to `worker_commitment` (proving it's the same entity that claimed). Issuer verifies the proof, NOT the identity.

3. **Payment**: Worker included a `payment_note_commitment` at claim time (encrypted to themselves). Reward is minted as a private note to that commitment. Worker spends the note later via nullifier. Issuer never sees the spending.

4. **Reputation**: Worker accumulates "completed bounty" receipts in their private receipt chain. When claiming future bounties with `StandingProof`, they prove "I have N completed bounties" via IVC chain WITHOUT revealing WHICH bounties or linking to their blinded commitments.

### What Each Party Learns

| Party | Learns | Does NOT Learn |
|-------|--------|----------------|
| Issuer | Work is done (STARK proof), qualification met | Who did it, their other work, their identity |
| Worker | Bounty details, payment received | Nothing about issuer beyond public bounty |
| Observers | A bounty was posted and completed | Who claimed, who delivered, payment amount |
| Federation nodes | Turn executed, note created | Worker identity (blinded), completion details (in proof witness) |

### Sybil Resistance

Without identity, how do we prevent one worker from claiming all bounties?

Options:
- **Stake**: Worker locks a note as bond when claiming. Forfeited if they don't deliver by deadline. Can only claim as many bounties as they can bond.
- **Rate limit by commitment**: Each `worker_commitment` can only claim N bounties per epoch. Since commitments are unlinkable, a worker generating many commitments would need many stake bonds.
- **Issuer-set qualification**: Higher-value bounties require higher standing proofs (more completed bounties in history).

### Comparison to Traditional Bounty Systems

| Feature | GitHub Bounties | Gitcoin | Pyana Bounty Board |
|---------|----------------|---------|-------------------|
| Worker identity | Public (GitHub profile) | Public (wallet address) | Private (blinded commitment) |
| Payment | Manual transfer | On-chain, public | Private notes |
| Qualification | Trust/reputation | On-chain history | ZK predicate proof |
| Completion verification | Human review | Human review | STARK proof + optional human review |
| Cross-platform | No | ETH only | Any federation |
| Replay protection | N/A | Transaction nonce | Nullifier-based |
