# RevocationChannel: Opt-in Synchrony for Instant Revocation

A design for a synchrony primitive that enables instant capability revocation
when both the revoker and the subject opt in, without abandoning pyana's
async-by-default execution model.

---

## 1. The Primitive

A `RevocationChannel` is a circuit breaker between a revoker and one or more
subjects. Subjects voluntarily subscribe and check channel state before
exercising delegated capabilities.

```
RevocationChannel {
    channel_id: [u8; 32],       // H("pyana-revocation-channel" || revoker || nonce)
    revoker: CellId,            // the cell authorized to trip this channel
    subjects: Vec<CellId>,      // cells that check this channel before acting
    state: ChannelState,        // Active | Tripped { reason: [u8; 32], height: u64 }
    attestation: AttestedRoot,  // federation attestation covering channel state
}
```

The channel is a leaf in a federation-attested Merkle tree (the "channel tree"),
analogous to how `RevocationTree` covers token IDs today.

---

## 2. Lifecycle

1. **Creation.** Revoker creates a channel, declaring its `channel_id`. The
   federation includes the channel in the channel tree at the next block.

2. **Subscription.** A subject adds `channel_id` to their `DelegatedRef` (or
   as a separate field on their cell state). This is the opt-in.

3. **Steady state.** Before exercising a capability gated by this channel, the
   subject checks: is `channel_state == Active` per my last attestation? If yes,
   proceed. This is O(1) — one hash lookup in local state.

4. **Trip.** Revoker submits a signed `TripEvent { channel_id, reason }` to the
   federation. Consensus includes it in the next block. The channel tree updates.
   The new `AttestedRoot` reflects the tripped state.

5. **Propagation.** Federation gossip carries the new attestation. Any subject
   holding a stale attestation will see the trip on their next refresh. Any
   verifier requiring a fresh channel proof will reject actions after the trip.

6. **Post-trip.** A subject whose channel is tripped MUST NOT act on the gated
   capability. If they do, their proof will fail verification (the channel
   membership proof will show `Tripped` at the relevant height).

---

## 3. Interaction with Offline Operation

The channel degrades gracefully when connectivity is unavailable:

- Subject caches `(channel_state, attestation_height, attestation_timestamp)`.
- If `now - attestation_timestamp <= max_staleness`: act freely.
- If stale: must contact the federation (or a peer with a fresher attestation)
  before acting on the gated capability.
- If unreachable and stale: the subject cannot prove non-revocation. This is
  equivalent to the existing `DelegatedRef.is_stale()` behavior — the capability
  is frozen until connectivity returns.

This means the channel does NOT break offline operation. It bounds the window
during which a tripped channel goes unnoticed to `max_staleness`, exactly as
epoch-based revocation does today. The improvement is in the PUSH mechanism.

---

## 4. Comparison to seL4 CDT Revoke

| Property | seL4 CDT | Pyana RevocationChannel |
|----------|----------|-------------------------|
| Mechanism | Kernel walks capability derivation tree | Federation attests channel state flip |
| Latency | Instant (kernel syscall) | Bounded async (next attestation + gossip) |
| Scope | All descendants of the revoked cap | All subscribers to the channel |
| Authority | Kernel (trusted, centralized) | Federation quorum (distributed) |
| Offline | N/A (single-machine) | Degrades to staleness-bounded eventual |
| Granularity | Per-capability | Per-channel (can gate one or many caps) |

The core trade-off: seL4 has a single trusted kernel that can atomically walk
the derivation tree. Pyana has no single authority — the federation is the
closest analog, and it operates in rounds. We accept bounded delay in exchange
for distribution, fault tolerance, and offline operation.

---

## 5. Why This Beats Fast Epoch Bumps

The existing `delegation_epoch` mechanism works like this: parent bumps epoch,
child's `DelegatedRef` becomes stale, child must refresh. The problem:

- **Polling.** The child discovers the bump only when it checks staleness. If
  `max_staleness` is 60s, the child might act for up to 60s after revocation.
- **No proof of visibility.** A verifier cannot tell whether the child SAW the
  bump and ignored it, or simply hasn't checked yet.
- **Coarse.** Bumping the epoch revokes ALL children, not targeted ones.

Channels fix all three:

- **Push via gossip.** The trip is carried by federation attestation gossip. A
  connected subject learns of it within one consensus round (~seconds), not at
  their next staleness check.
- **Provably visible.** The attestation IS the proof. A verifier can require:
  "your action must include a channel-active proof at height >= H." If the
  channel was tripped at height H, no valid proof exists. Third-party
  verification becomes possible.
- **Targeted.** A channel can gate a single delegation without disturbing others.

---

## 6. Composition with Existing Primitives

**DelegatedRef.max_staleness** — Controls how often the subject refreshes its
channel attestation. A `max_staleness` of 0 means "check every time" (strongest
guarantee). A value of 300 means "I tolerate 5 minutes of stale state."

**BudgetGate** — A tripped channel can freeze the budget gate for the affected
subject. Trip semantics: "your budget slice is no longer valid." The executor
checks channel state as part of budget validation.

**IntentEngine** — When a channel trips, all pending intents from the affected
subject are auto-cancelled. The trip event is the cancellation signal. Intent
matchers can subscribe to channel state to avoid matching against stale intents.

**ReceiptChain** — The trip event becomes a receipt in the federation's chain.
This provides provable history: "channel X was tripped at height H with reason R,
signed by revoker, attested by quorum." Auditable and non-repudiable.

---

## 7. ZK Circuit: Prove Non-Revocation

The channel tree is a Merkle tree. Proving "my channel is active" is a standard
membership proof: the leaf at `channel_id` has state `Active` as of root R.

In the STARK presentation (per `circuit/src/ivc.rs`):

1. Prover includes a Merkle path from `channel_id` to the channel tree root.
2. The path proves the leaf value is `Active` (not `Tripped`).
3. The channel tree root is part of the `AttestedRoot` at height H.
4. Verifier checks: H >= (current_height - max_staleness_in_blocks).

This composes with the existing IVC proof: "I am authorized (fold chain valid)
AND my channel is active (Merkle membership at recent height)." Both are
constant-size proofs regardless of chain history.

A tripped channel produces no valid membership proof for `Active` state — the
leaf value has changed. Revocation is cryptographically unforgeable.

---

## 8. Comparison Table

| Strategy | Revocation latency | Offline support | Verifiable by 3rd party | Cost per action | Targeted |
|----------|-------------------|-----------------|------------------------|-----------------|----------|
| No check | Never (trust subject) | Full | No | 0 | N/A |
| Epoch staleness | max_staleness window | Full (degrades) | No (polling-based) | 0 (check local clock) | No (all children) |
| **RevocationChannel** | **1 consensus round + gossip** | **Full (degrades)** | **Yes (attestation proof)** | **1 hash lookup + cached proof** | **Yes** |
| Full synchrony | Instant | None (requires liveness) | Yes | 1 round-trip to authority | Yes |

---

## 9. When to Use vs. When Not

**Use channels when:**
- High-value delegations (financial authority, signing keys, admin access)
- Compromised-agent response (need to cut off a subject within seconds)
- Compliance requirements (auditors need proof that revocation was visible)
- Multi-party workflows where verifiers need non-revocation guarantees

**Do NOT use channels when:**
- Casual agent swarms (epoch staleness is sufficient, less coordination overhead)
- Low-risk operations (the subject's misbehavior is bounded by the capability)
- Fully offline agents (they can't refresh attestations anyway)
- Short-lived delegations (expires before revocation would matter)

Channels are a POLICY choice made at delegation time, not a protocol mandate.
A `DelegatedRef` without a `channel_id` behaves exactly as today: epoch-based,
poll-on-staleness. Adding a channel is strictly additive.

---

## 10. Open Questions

- **Channel tree vs. revocation tree:** Should channels live in the existing
  `RevocationTree` or a separate tree? Separate is cleaner (different leaf
  semantics) but adds a second root to `AttestedRoot`.

- **Multi-revoker channels:** Should a channel support multiple authorized
  revokers (e.g., "any of these 3 admins can trip it")? Adds complexity but
  mirrors real organizational structures.

- **Channel reset:** Can a tripped channel be re-activated? If yes, this
  enables "pause/resume" semantics. If no, revocation is permanent and a new
  channel must be created for re-delegation.

- **Gossip protocol:** How does the trip propagate outside the federation's
  direct subscribers? Need a gossip protocol that ensures subjects learn of
  trips within bounded time, even if they aren't directly connected to a
  federation node.
