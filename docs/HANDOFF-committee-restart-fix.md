# HANDOFF — the N3 committee-restart hole: A/B decision

**Diagnosed at** `HEAD = 29ab74bc1` ("fix(node/consensus): diagnose N3
committee-restart hole"). Pinned by
`dregg_persist::tests::full_mode_single_sig_root_is_refused_genuine_quorum_accepted`
(`persist/src/tests.rs:110+`). This doc reduces the fix to **one read → pick A or
B**. Both are consensus-visible protocol additions, not plumbing.

---

## The hole (one paragraph)

On finalizing a turn, the full-mode commit path persists a `StoredAttestedRoot`
carrying **only the local node's single signature** with `threshold = committee
size` (`node/src/blocklace_sync.rs:4529-4546`, inside `execute_finalized_turn`).
On restart, `verify_signed_anchor_and_rollback` (`node/src/state.rs:1221`) calls
`StoredAttestedRoot::verify_signatures` (`persist/src/federation.rs:84`), which
requires `quorum_signatures.len() >= threshold` valid **committee** signatures
over the root's `signing_message()`. `1 < 3`, so a full-mode committee node
**fail-closes after finalizing ≥1 height**. The recovery anchor is *correct*
hardening; the persistence *under-feeds* it. Solo / threshold-1 is unaffected.

Why it can't be closed by "just aggregate the votes we already have":

1. The only cross-node quorum that forms is the `FinalizationVote` set
   (`node/src/finalization_votes.rs`), which signs
   `VOTE_DOMAIN || block_id || level` (`finalization_votes.rs:72-78`) — **not**
   the root's `merkle_root`-binding `signing_message()`
   (`persist/src/federation.rs:110-154`).
2. Votes arrive **async**: the synchronous persist happens inside
   `execute_finalized_turn` (~`blocklace_sync.rs:4529`); the node emits its own
   vote only *after*, at `blocklace_sync.rs:3680`
   (`emit_finalization_vote` → `record_finalization_vote`, `:2380`). Peer votes
   land later over gossip.
3. `VoteCollector` retains **distinct-signer KEY sets only**
   (`finalization_votes.rs:146`, `votes: HashMap<BlockId, HashSet<[u8;32]>>`) —
   the **signature bytes are discarded** after counting.
4. `signing_message()` binds a **wall-clock `timestamp`**
   (`blocklace_sync.rs:4511` `timestamp_for_root = now`; executor sets it via
   `wall_clock_secs()`, `executor_setup.rs:45/59`), so committee peers cannot even
   *produce* matching signatures over the root — each computes a different
   preimage.

---

## The shared prerequisite (both A and B need it)

**Make the attested-root preimage deterministic.** Any cross-node signature
agreement over the root requires every node to derive the *identical* preimage;
the wall-clock `timestamp` breaks that (point 4). So both fixes must first derive
the root's `timestamp` from the **finalized block** (not `wall_clock_secs()`).

- **Change:** `blocklace_sync.rs:4511` (`timestamp_for_root`) sources from the
  finalized block's deterministic time; `executor_setup.rs:45/59` stops seeding a
  wall-clock timestamp into the committed state root.
- **Wire/consensus-visible:** the preimage domain bumps
  `dregg-attested-root-v4` → `-v5` in both
  `persist/src/federation.rs:112` and the mirror
  `dregg_types::AttestedRoot::signing_message`. All committee members must upgrade
  together (a genesis/epoch boundary).

---

## Fix A — deterministic root + a dedicated signed-gossip root-sig exchange

Add a **new** gossip message carrying each member's signature over the
deterministic root; aggregate ≥threshold, then persist.

| Change | File / function | Kind |
|--------|-----------------|------|
| Deterministic timestamp (shared prereq) | `blocklace_sync.rs:4511`, `executor_setup.rs:45/59`, `federation.rs:112` (+ `dregg_types` mirror) | consensus-visible domain bump |
| New `BlocklaceGossipMessage::AttestedRootSig { block_id, root_preimage_id, voter, sig }` | `node/src/blocklace_sync.rs` (message enum + dispatch), the blocklace gossip topic | **new wire message** |
| Collect root-sigs per finalized root until `≥threshold`, then persist | `blocklace_sync.rs` (a new collector paralleling `VoteCollector`) + the persist call in `execute_finalized_turn` | new state + async persist |

- **Wire-format change:** a *new* gossip message type on the blocklace topic, plus
  the shared preimage domain bump. Two consensus-visible surfaces.
- **Liveness tradeoff:** the synchronous commit cannot block on network gossip, so
  the persisted root **trails the finalized head** — it lands a round or two behind
  as root-sigs assemble. On restart the anchor recovers to the **last
  quorum-signed root** and replays the unaggregated tail (an unaggregated head is
  treated as *no anchor*).

## Fix B — extend `FinalizationVote` to bind the finalized `merkle_root`

Fold the deterministic root's binding into the **existing** vote so its sigs *are*
the root's quorum signatures; retain them; persist when the vote-quorum assembles.

| Change | File / function | Kind |
|--------|-----------------|------|
| Deterministic timestamp (shared prereq) | as above | consensus-visible domain bump |
| `FinalizationVote` gains `merkle_root` (+ the root fields it must bind) and folds them into `signing_message` | `finalization_votes.rs:41-78` | **wire message change**, `VOTE_DOMAIN` v1→v2 |
| `VoteCollector` retains `(voter, signature)` pairs, not just signer keys; `RecordOutcome::ReachedQuorum` carries the assembled sigs | `finalization_votes.rs:140-285` (`votes:` map + `record`) | in-memory only |
| On `ReachedQuorum`, assemble retained sigs into `StoredAttestedRoot.quorum_signatures` and persist the root | `blocklace_sync.rs:2380` (`record_finalization_vote`); `execute_finalized_turn` stops persisting the lone single-sig root | reuses existing gossip path |
| Vote preimage == the root's canonical bytes, so retained sigs verify under `verify_signatures` unchanged | `persist/src/federation.rs:84` unchanged (already binds `merkle_root`) | none |

- **Wire-format change:** `FinalizationVote`'s signed message gains the
  `merkle_root` binding (`VOTE_DOMAIN` v1→v2), plus the shared preimage domain
  bump. **One** consensus-visible message, on the **existing** channel — no new
  message type.
- **Liveness tradeoff:** identical in shape to A — the root persists only when the
  vote-quorum assembles (async, after finalization), so it **trails the head**. But
  it pays that cost with the machinery that already exists and is already proven.

---

## Recommendation — **Fix B**

Reasoning, smallest-blast-radius first:

1. **B rides proven machinery.** The whole `finalization_votes.rs` suite already
   exists and is green: distinct-signer quorum gating, the two-node exchange sim
   (`two_nodes_reach_consensus_attested_by_exchanging_votes`), the funnel invariant
   (`quorum_crossing_is_reported_on_whichever_vote_is_second`), and live epoch
   reconfigure. B extends **one struct's signed preimage** and **retains sigs the
   collector already verifies and currently throws away** (`finalization_votes.rs:146`).
   A introduces a *parallel* collector + a *new* gossip message type that
   duplicates exactly what `VoteCollector` + the FinalizationVote gossip already do.
2. **B touches fewer consensus surfaces.** Both need the shared preimage-determinism
   bump. Beyond that, B changes **one** existing message (`VOTE_DOMAIN` v1→v2) on
   the **existing** channel; A changes an existing preimage **and** adds a whole new
   `BlocklaceGossipMessage` variant with its own dispatch, dedup, and re-emit/nonce
   handling (the `FinalizationVote::nonce` liveness machinery, `:54-65`, would have
   to be re-created for the new message).
3. **B keeps the attested-root verifier untouched.** `verify_signatures` already
   binds `merkle_root`; if the vote preimage *is* the root's canonical bytes, the
   retained vote sigs are valid `quorum_signatures` with **zero** change to
   `persist/src/federation.rs`'s check. A's parallel sigs would still need to land
   in the same shape, so B gets there with strictly less new code.

**The one thing B must add:** `VoteCollector` currently stores signer keys only
(`HashSet<[u8;32]>`); B changes that to retain `(voter, Signature)` so the sigs
survive to persist time. That is the entire net-new data structure — everything
else is a field addition and a persist call moved from `execute_finalized_turn`
(the lone-sig write) to `record_finalization_vote` (the quorum-assembly write).

**Pick A only if** you want the attested-root signature exchange fully decoupled
from the finality-vote path (e.g. to persist a quorum-signed root even when the
finality-vote quorum and the root-sig quorum should be independently timed). That
decoupling is the sole thing A buys, at the cost of a second consensus-visible
message and a duplicate collector.
