# rbg/ — Robigalia Design Heritage

Exploring how Robigalia's capability-secure OS designs map to pyana's distributed runtime.

## Key Mappings

| Robigalia Concept | Pyana Equivalent | Gap/Opportunity |
|-------------------|-----------------|-----------------|
| Transaction Protocol (Submit/Execute/Retrieve/Reap) | Turn (submit/execute/receipt/advance) | Our turns ARE this protocol. The generation counter fix maps to our nonce. |
| Promise Pipelining (dependency bitmask, Consuming state) | CapTP pipeline.rs (just built) | We now have this! Cross-federation too. |
| Concurrent Executor (indexed slots) | Effect VM (14 effects per turn, parallel-provable) | Slot = effect row. Maximum concurrency = trace height. |
| Nameless Writes (content-addressed storage) | Note commitments (hash = address) | Notes ARE nameless writes. Extend to general blob storage? |
| Capability-Secure VFS (Volume/Blob/Directory) | Cell model (cells as objects, c-list as directory) | Missing: explicit Volume (resource accounting), blob abstraction |
| DFA Message Routing | Gossip topic matching / intent MatchSpec | MatchSpec is already pattern matching. DFA formalization would make it faster + provable |
| SturdyRefs (from VFS notes) | pyana:// URIs (just built in captp/) | Direct lineage. Swiss numbers = same concept. |
| Automata-based packet classification | Could enhance wire protocol routing | Constant-space, linear-time filtering of blocklace messages |

## Papers to Read
- `~/Desktop/zhang2-7-12.pdf` — Nameless Writes (storage without naming, capability-secure allocation)

## From the Transaction Protocol (formal spec)

The key insight: the protocol PROVES liveness and correctness of async RPC over unreliable transport.
Our equivalent: the blocklace's causal ordering + CapTP's promise resolution gives us the same guarantees
but over a DAG rather than a linear sequence.

The "Consuming" state (between Executing and Completed) = our "Tentative" finality.
The generation counter = our nonce + block height binding.
Promise pipelining with dependency bitmask = our ConditionalTurn with depends_on.

## From the VFS Design

```
Volume → resource quota (maps to: Stingray budget / computron allowance)
Blob → raw storage (maps to: Note/cell state, content-addressed)  
Directory → naming (maps to: c-list + cell hierarchy + factory provenance)
```

The VFS's `swap()` operation (atomic compare-and-swap on directory entries) maps to
our `Effect::SetField` with version/nonce checking. The Version field on every entry
maps to our cell nonce (monotonically incrementing on mutation).

## From DFA Message Routing

The idea: use DFA-based pattern matching to route messages to handlers in constant space
and linear time. Applied to pyana:

- Intent matching (MatchSpec) could compile to DFA for O(n) matching of intents against capabilities
- Gossip topic filtering could use DFA for efficient multi-topic routing
- Wire protocol message dispatch could be DFA-optimized
- The "revocation = recompile DFA without the revoked filter" maps to our revocation tree approach

## Design Principles Inherited

1. **Stateless interactions** (carry state explicitly, no implicit offset/cursor)
   → Our effects carry all parameters explicitly. No hidden executor state.

2. **Capability-secure by construction** (reference = authority, no ambient)
   → Our c-list + bearer cap model. ResolvedCapability enforces uniformly.

3. **Constant-space hot path** (DFA routing, no allocation during dispatch)
   → Effect VM: fixed-width trace, constant per-row evaluation cost.

4. **Atomic versioning** (every mutation increments version)
   → Cell nonce. Every turn increments. ConditionalTurns check nonce freshness.

5. **Promise pipelining reduces round-trips**
   → CapTP Phase 4 (just built). Cross-federation pipeline registry.
