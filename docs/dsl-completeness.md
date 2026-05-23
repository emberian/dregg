# Pyana DSL Completeness Assessment

## Verdict: Complete

The DSL handles all 16 caveats and all effect types. Nothing is impossible; some things cost more columns. The five "punted" cases each reduce to witness + constraints, which is exactly what the DSL already compiles.

## Resolution of Each "Impossible" Case

**Non-membership (`!set.contains(x)`)** — Compile-time dispatch. The DSL already recognizes `Set<T>` types. `contains` emits a Merkle membership AIR; `!contains` emits an accumulator polynomial evaluation AIR (Horner chain over the set's characteristic polynomial, then a non-zero check via multiplicative inverse). The compiler knows which pattern to use from the negation operator. No runtime branching. Cost: ~2N+3 columns for a set of size N encoded as polynomial coefficients, or constant-width if we commit the polynomial and verify evaluation via an auxiliary lookup.

**Bitwise operations (`ip & mask == prefix`)** — Bit decomposition is already the mechanism behind range checks. AND/XOR/OR over decomposed bits are trivially degree-1 per-bit constraints (`a_i * b_i` for AND). The DSL recognizes `&`, `|`, `^` on integer types and emits decompose-operate-recompose. Kimchi has native `GateType::Xor16`; for AIR the cost is 32 additional columns (for 32-bit values) plus one constraint per bit. This is cheaper than a single Poseidon invocation.

**Third-party discharge** — The "interaction" is witness acquisition, not circuit execution. The prover obtains the discharge out-of-band, then the circuit verifies `HMAC(key, token) == expected`. The DSL provides `hmac_verify!` (compiling to Poseidon2-HMAC for STARK, native Poseidon for Kimchi) as a built-in. The discharge token is a private witness column; the expected HMAC is a public input. No interaction at proof time. Cost: one hash invocation (~200 constraints for Poseidon2).

**Complex effects (NoteSpend)** — Composition of primitives the DSL already handles: `hash!` (Poseidon2), `merkle_path.verify` (iterated hashing), `publish!` (boundary constraint / public output), `emit_value!` (conservation accounting). The `#[pyana_effect]` macro recognizes these built-ins and emits the corresponding sub-AIRs composed vertically within a single trace. Each primitive maps to a known column-width; the total is their sum. Conservation checking becomes a separate constraint that sums `emit_value!` calls across all effects in a transaction.

**Struct field access / indexing** — Array indexing with a runtime index compiles to a one-hot selector pattern: prover provides the selector vector, circuit enforces `sum(sel) == 1`, and per-element constraints gate updates through `sel[i] * (new[i] - value) == 0`. Struct field access with a compile-time-known field is trivial (direct column reference). Cost: N additional columns for the selector on an array of size N, plus 2N degree-2 constraints.

## Required Built-in Functions

| Built-in | AIR emission | Kimchi emission |
|---|---|---|
| `hash!(a, b, ...)` | Poseidon2 permutation AIR (width-16 sponge) | Poseidon gates |
| `merkle_verify!(leaf, root, path)` | Iterated `hash!` with path selectors | Iterated Poseidon gadgets |
| `hmac_verify!(key, msg, tag)` | Keyed Poseidon2 (hash(key ∥ hash(key ∥ msg))) | Same via Poseidon |
| `publish!(x)` | Boundary constraint: `public_output[i] = x` | Public input wire |
| `emit_value!(v, t)` | Conservation accumulator (sumcheck across transaction) | Same |
| `bit_decompose!(x, N)` | N boolean columns + recomposition equality | Kimchi range-check gates |

Plus the existing `require!` and `mutate!`.

## The Actual Limitation

It is not expressiveness. The DSL can express everything because all operations decompose to field arithmetic over witnesses. The real constraints are:

1. **Trace width budget.** Each built-in adds columns. A NoteSpend effect with Poseidon2 Merkle verification (depth 32) needs ~600 columns per step. BabyBear STARKs handle this fine (Plonky3 supports wide traces), but it affects prover memory: trace_width * num_rows * 4 bytes.

2. **Proving time, not expressibility.** HMAC-SHA256 in a STARK costs ~30k constraints. Poseidon2-HMAC costs ~400. The DSL must pick SNARK-friendly primitives (it does: Poseidon2 for STARK, Mina Poseidon for Kimchi). The compile-time cost is choosing which hash to emit per backend.

3. **Witness generation complexity.** The prover must compute witnesses for all built-ins. For `!set.contains`, this means polynomial division. For Merkle paths, fetching the authentication path. The DSL generates witness-gen code alongside constraints, but the prover needs access to the relevant state (the set's polynomial representation, the Merkle tree). This is a data-availability concern, not a DSL limitation — the runtime must provide a `WitnessOracle` trait implementation.

4. **No unbounded iteration.** The DSL remains bounded (no while-loops, no recursion). This is fundamental to static trace sizing. Unbounded computation requires IVC/folding (which the codebase already has via `circuit/src/ivc.rs`). The DSL can emit fold-steps but cannot express "loop until done" in a single proof.

## Coverage of All 16 Caveats

The full caveat set (not_after, not_before, budget, service_scope, rate_limit, delegation_depth, source_ip, audience, revocation, third_party_discharge, body_membership, attenuation_only, channel_binding, max_amount, require_mfa, geo_restrict) maps as follows: temporal caveats use range checks; set caveats use membership/non-membership; budgets use mutation; bitwise (ip/geo) uses decomposition; discharge uses HMAC verification; body_membership uses Merkle proofs. Every one compiles to the six built-ins above plus `require!` and `mutate!`.

The DSL is not a toy. It is a complete constraint language for this domain.
