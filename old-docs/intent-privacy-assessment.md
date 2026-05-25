# Intent Privacy Assessment: Is Pyana's Intent System Private Enough?

Short answer: No. The system provides component-level privacy (PIR for browsing, STARK proofs for fulfillment) but the composition leaks enough metadata to profile participants in a real marketplace.

## 1. Intent Posting Is a Surveillance Surface

Intents are broadcast in cleartext over gossip. Every peer sees the full MatchSpec: actions, resources, constraints, budget. The CommitmentId is pseudonymous but REUSED across intents from the same cclerk within an epoch. An observer trivially builds profiles:

- "CommitmentId 0xAB posts GPU compute intents every Monday, budget 500-1000"
- "CommitmentId 0xCD always needs document/reports/* read access after 0xAB posts"
- Volume, timing cadence, and budget ranges fingerprint participants even without identity

The epoch-scoped nullifier system (K uses per epoch per stake) actually HELPS the attacker: it caps the anonymity set per stake commitment to K observable actions.

**Severity: Critical.** In a marketplace with <1000 active participants, behavioral fingerprinting from public intents alone likely de-anonymizes the top 20% of participants within weeks.

## 2. PIR Is Realistic Only in DownloadAll Mode

The three PIR modes have these real-world failure modes:

**TwoServer IT-PIR** requires non-colluding servers. In a marketplace with one operator, this is theater. With two operators, they have economic incentive to share data (or be compelled by the same jurisdiction). The security model is "honest-but-curious with non-collusion" -- the weakest realistic assumption for adversarial marketplaces.

**SingleServerPadded** hides which row but not that you queried, when you queried, or how often. A server tracking query frequency and timing can intersect queries with subsequent fulfillments to infer interests. The blinding commitment proves nothing to a malicious server that simply ignores it.

**DownloadAll** is genuinely private (server learns nothing post-download) but requires downloading the entire padded database per session. At 64 intent IDs per tag and 2048 bytes per row, a 1000-tag marketplace is ~2MB per refresh. Feasible for small catalogs. Breaks at 100k+ tags.

**Realistic path:** DownloadAll for small marketplaces (<5000 items). For larger ones, no deployed PIR scheme survives an honest threat model against a motivated single operator.

## 3. Timing Correlation Destroys Fulfillment Privacy

The system has NO mixing, batching, or delay mechanism for fulfillments. The flow is:

1. Intent appears on gossip (public, timestamped)
2. Fulfillment commitment appears (public, timestamped, 5-second reveal window)
3. Fulfillment reveal (reveals granted actions/resource)
4. Intent removed from pool

An observer sees: intent posted at T, commitment at T+2s, reveal at T+7s, intent gone at T+8s. In a marketplace with 10 active fulfillers for a given resource type, the timing narrows the fulfiller's identity to whoever was online and capable during that 2-second window.

The commit-reveal protocol prevents frontrunning but actively HARMS privacy by creating two observable correlated events (commit + reveal) instead of one.

## 4. "Hiding Who but Revealing What" Is Insufficient

Private mode STARK proofs prove "I can satisfy this" without revealing which token. But the intent (public) declares exactly WHAT is being transacted. Combined with the fulfillment's granted_actions and granted_resource (transmitted to the creator and visible in the payment turn), the full transaction semantics are known to:

- All gossip peers (intent contents)
- The intent creator (fulfillment details)
- The executor (payment turn with transfer amounts in cleartext)
- Any observer correlating intent disappearance with payment activity

The STARK proof hides the delegation chain and token identity -- useful for credential privacy, insufficient for marketplace anonymity where the TRANSACTION ITSELF is sensitive.

## 5. Gossip Network Is Undefended

No mixnet, no onion routing, no padding, no dummy traffic. The wire server logs IP addresses. Message sizes vary (STARK proofs range from ~1KB to ~50KB depending on derivation depth). A well-positioned ISP or gossip peer builds a complete real-time map of all marketplace activity with participant IP addresses attached.

## What Real Intent Privacy Requires

**Layer 1 -- Network:** Tor or mixnet transport for gossip. Fixed-size message padding. Dummy traffic to prevent timing analysis. This is table-stakes and the system has none of it.

**Layer 2 -- Intent Content:** Encrypted intents where only the matcher (not the gossip network) sees the MatchSpec. Approach: encrypt the intent body to a set of designated matchers using threshold encryption or functional encryption. The gossip layer propagates opaque blobs; only authorized matching nodes decrypt. This requires a matcher trust model that does not currently exist.

**Layer 3 -- Matching:** Batched matching with epoch-based reveals. Instead of immediate fulfillment, collect intents into time-windowed batches (e.g., 60-second epochs). All fulfillments for an epoch are revealed simultaneously, destroying timing correlation. Cost: latency.

**Layer 4 -- Fulfillment Delivery:** Replace direct fulfillment delivery with a dead-drop or relay system. The fulfiller posts an encrypted fulfillment to a shared bulletin board; the intent creator retrieves it via PIR. Neither party communicates directly.

**Layer 5 -- Payment:** Integrate the existing Pedersen commitment and conservation proof machinery into the executor. Payments must be committed values, not cleartext u64. This exists in pyana's crypto layer but is not wired into the Turn system.

## Honest Assessment

The current system provides:
- Private BROWSING (PIR, in DownloadAll mode only)
- Private CAPABILITY PROOF (STARK, strong)
- Pseudonymous POSTING (CommitmentId, weak -- linkable within epochs)

It does NOT provide:
- Private intent content (gossip sees everything)
- Unlinkable intent-to-fulfillment correlation (timing destroys this)
- Network-level metadata protection (none)
- Private payments (executor sees cleartext amounts)
- Anonymous fulfillment delivery (direct, no relay)

For a real anonymous marketplace, the system needs encrypted gossip (achievable with existing sealed-box primitives), batched matching (architectural change, moderate effort), and committed-value payments (primitives exist, integration is the work). The network layer requires Tor or equivalent -- no amount of application-layer crypto fixes an undefended transport.

The gap is integration and architecture, not missing cryptography. The hard research problem is efficient encrypted matching (functional encryption over MatchSpecs) -- everything else is engineering against known designs.
