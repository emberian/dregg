# Encrypted Intents and Blind Order Matching

## Problem

MatchSpecs broadcast in cleartext over gossip expose transaction semantics to all observers. The intent-privacy-assessment identifies this as critical: behavioral profiling from public intents de-anonymizes participants in small marketplaces within weeks.

## Approach Evaluation

### 1. Functional Encryption (FE) over MatchSpecs

Pyana's constraint language (actions, resources, budget ranges, globs, Datalog predicates) maps to inner-product predicates for equality checks and range proofs for budgets. The CiFEr library (Rust: `cife-rs` wrapping the C library) implements IPFE (inner-product functional encryption) under DDH. Key sizes are O(n) in the vector dimension; ciphertexts are 2 group elements per dimension.

Problem: glob matching and Datalog evaluation are NOT expressible as inner products. Attribute-based encryption (CP-ABE via `rabe` crate) handles AND/OR policy trees over attributes, which maps to constraint conjunctions but not glob patterns. No practical FE scheme handles `documents/*` matching against `documents/reports/q4.pdf` without enumerating all possible matches.

Performance: IPFE decryption is ~1ms for small vectors. CP-ABE decryption is ~5-20ms depending on policy complexity. Key sizes are reasonable (< 1KB per attribute). Feasible for exact-match constraints; infeasible for glob/prefix matching.

### 2. Searchable Symmetric Encryption (SSE)

Map each MatchSpec to a set of keyword tokens: `action:read`, `service:http`, `pattern:documents/*`, `budget:500-1000` (discretized into buckets). The intent poster encrypts using deterministic trapdoors derived from each keyword. A matcher holding the trapdoor for `action:read` can test whether an encrypted intent contains that token.

Libraries: `rust-crypto` primitives suffice (HMAC-based trapdoor generation, AES-encrypted index). The `opaque-ke` crate provides OPRF primitives for trapdoor derivation without revealing the keyword to the server.

Limitations: Leaks access patterns over time (a matcher seeing the same trapdoor hit repeatedly learns frequency). Keyword tokens are linkable across intents. Does NOT hide budget amounts (only discretized bucket membership).

Performance: <1ms per keyword test. Scales linearly with keyword count per intent. Practical for real-time matching.

### 3. Homomorphic Encryption for Matching

TFHE (`tfhe-rs` crate) supports boolean circuit evaluation on encrypted bits. Encoding a MatchSpec as a boolean circuit (action equality, resource prefix check, budget comparison) and evaluating it homomorphically produces an encrypted match/no-match bit.

Performance: A single homomorphic comparison of two 64-bit values takes ~50ms on modern hardware. A full MatchSpec evaluation (3-5 comparisons + string equality) would take 200-500ms. Budget range checks are feasible; glob matching requires encoding the glob automaton as a boolean circuit (~2-5s for typical patterns).

Trust: None beyond math. The poster decrypts the result bit. But latency makes this impractical for real-time gossip matching with thousands of intents per second.

### 4. Private Set Intersection (PSI)

Model: poster's requirements = `{action:read, resource:documents/*, service:http}`. Fulfiller's capabilities = `{action:read, action:write, resource:*, service:http}`. PSI reveals only the intersection without exposing non-matching elements.

Libraries: `oprf` crate (Ristretto-based OPRF) for the OPRF-based PSI protocol. Two-round protocol: parties exchange OPRF-encrypted sets, compute intersection locally. Also: `psi` crate wraps Google's PSI library.

Mapping to MatchSpec: Works for exact-match actions and services. Fails for budget ranges (would need range-to-set expansion) and glob patterns (would need pattern enumeration). Partial match: PSI tells you WHAT matched but not whether the match is SUFFICIENT (e.g., all required actions present vs. just one).

Performance: OPRF-PSI is ~0.1ms per element for sets of size < 100. Two network rounds required. Practical for interactive matching between two known parties; impractical for broadcast matching against unknown fulfillers.

### 5. Trusted Execution Environment (TEE)

Intents encrypted to the TEE's attestation key (Intel SGX via `fortanix-sgx` or ARM TrustZone). The TEE decrypts, evaluates `satisfies_spec()` on cleartext, returns only match/no-match + a shared session key for the matched pair.

Performance: Near-native (~1us overhead for enclave entry/exit). The existing `matcher.rs` logic runs unmodified inside the enclave.

Trust: Hardware vendor (Intel/ARM) + TCB (enclave code). Side-channel attacks (Spectre, LVI, AEPIC) have repeatedly broken SGX confidentiality. Acceptable as a bridge while cryptographic approaches mature, NOT as a long-term solution.

Integration: Moderate. The IntentPool moves into an enclave; gossip carries encrypted blobs; the enclave outputs encrypted match notifications.

### 6. Commit-Match-Reveal Protocol

Already partially implemented in `commit_reveal_fulfillment.rs`. Extend to cover the matching phase:

1. Poster commits to encrypted intent (BLAKE3 hash of intent body + nonce).
2. Poster encrypts intent body to a designated matching enclave OR to a threshold key shared among K matchers.
3. Matching oracle (TEE or K-of-N MPC) evaluates matches, outputs only: `(intent_id, fulfiller_commitment, shared_session_key)` to the matched pair.
4. Neither party learns unmatched intents' contents.

This combines TEE (phase 1) with threshold decryption (long-term) and builds on the existing commit-reveal infrastructure.

## Staged Plan

### Phase 1: SSE + Commit-Match-Reveal (ship in 4-6 weeks)

Use SSE keyword tokens for coarse filtering (action, service, feature tags -- the same tags already extracted by `extract_capability_tags()` in `pir.rs`). Encrypt the full MatchSpec body with `x25519-dalek` sealed boxes. Gossip carries: `(encrypted_body, keyword_tokens[], commitment_hash)`.

Matching nodes hold trapdoors for their capability keywords. They test tokens without decrypting the body. On token match, they request the full decryption key from the poster via the existing direct fulfillment channel.

Protocol flow:
1. Poster: `tokens = HMAC(master_secret, tag)` for each tag in MatchSpec
2. Poster: `sealed = crypto_box_seal(matchspec_bytes, poster_ephemeral_pk)`
3. Gossip: broadcast `(sealed, tokens, commitment_hash, expiry)`
4. Matcher: for each held capability tag, compute `HMAC(trapdoor_key, tag)`, compare to tokens
5. On match: matcher requests decryption via direct channel (existing fulfillment path)
6. Poster reveals MatchSpec body only to matched fulfiller

Libraries: `x25519-dalek`, `chacha20poly1305`, `blake3` (all already in the dependency tree or trivial to add).

Limitation: Keyword tokens are deterministic, so repeated use of the same tags is linkable. Mitigate with epoch-rotation of the HMAC key (same pattern as stake nullifiers).

### Phase 2: PSI for Interactive Matching (3-6 months)

Replace SSE keyword matching with OPRF-based PSI for fulfillers who are online and interactive. The fulfiller's capability set and the poster's requirement set undergo a 2-round PSI protocol. Only the intersection is revealed.

This eliminates keyword linkability (each PSI session uses fresh random OPRF keys) but requires interactive fulfillers (not passive gossip observers). Combine with Phase 1 SSE for the broadcast layer; PSI activates only after coarse SSE filtering identifies candidate matches.

Libraries: `voprf` (Ristretto VOPRF), custom 2-round protocol built on the existing gossip direct-message channel.

### Phase 3: FHE Matching for Budget/Range Constraints (12+ months)

Use `tfhe-rs` for homomorphic evaluation of budget range checks and numeric constraints (the `PredicateRequirement` fields). Actions and services stay with PSI (faster); budgets and ranges go through FHE.

Target: <500ms per intent evaluation for intents with 1-2 predicate requirements. Batch evaluations amortize setup cost. This is viable for a matching oracle that processes a queue (not real-time gossip), processing 100-200 intents per minute.

Long-term vision: a decentralized matching network where K nodes each hold a share of the FHE evaluation key (threshold FHE). No single node sees cleartext. The STARK proof infrastructure already in `circuit/` can verify correct FHE evaluation without trusting the evaluator. This is active research (threshold TFHE is not production-ready as of 2025) and represents the end-state, not a near-term deliverable.
