# Binius Research Summary (2026-05-20)

## Decision: R&D branch only, not primary backend

Binius64 is promising for binary-heavy workloads but NOT ready for production authorization:
- No ZK guarantee yet (roadmap item)
- No recursion/IVC (roadmap item)
- No succinct verifier (roadmap item)
- Proof sizes ~180-300 KiB (not the "1-5 KiB" we hoped)
- No stable releases (git dep only)

## Key findings:
- Binius V0 (tower-field M3 tables) is archived/deprecated
- Binius64 (current) is a 64-bit word circuit system, NOT an AIR-style system
- Best hash: Vision (official roadmap), Poseidon2b (research, fastest verify), or Blake2s/Keccak (today)
- 32-byte equality: 4 AND constraints (excellent)
- Comparison/range: 1 AND + 1 linear (good)
- Our current stub implementation with channel boundaries is correct architecture

## When to revisit:
- When recursion lands on the Binius64 roadmap
- When ZK is confirmed working
- When proof sizes improve via succinct verifier work
