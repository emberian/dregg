# Dynamic Hints Integration Plan

## 1. What Dyna-hinTS Proposes

**Paper**: "Dyna-hinTS: Silent Threshold Signatures for Dynamic Committees" (Kate, Mukherjee, Samanta, Sarkar)

### Core Idea

Dyna-hinTS extends the silent threshold signature (STS) paradigm to support **dynamic committees** — specific subsets of signers chosen per epoch — without requiring per-committee DKG or full recomputation.

### Architecture (Three Phases)

**Phase 1: One-Time Preprocessing (unchanged from hinTS)**
- Each party `P_i` generates `sk_i`, computes `pk_i = [sk_i]_1`, and broadcasts their `hinTS_i` (the same hint structure we already compute in `hints/src/snark/hints.rs`).
- The aggregator verifies all hints (pairing checks), computes the aggregation key AK and verification key VK = `([SK(tau)]_1, [W(tau)]_1, [T(tau)]_2)`.
- VK is posted on-chain. **This happens ONCE for the entire universe of N signers.**

**Phase 2: Committee Selection (per epoch)**
- A randomness beacon outputs `(y, pi_RB)` for epoch `e`.
- A committee `Com_e` of `n` members is selected from the `N` total signers using the beacon output.
- The aggregator computes a KZG commitment `[B_Com(tau)]_2 = product_{i in Com_e} [L_i(tau)]_2` encoding the committee membership.
- Posts `[B_Com(tau)]_2` and proof `pi_Com_e = (y, pi_RB, E_Com_e)` to the bulletin board.
- **Cost**: `n` group multiplications in G2 (one per committee member). For n=20, this is ~0.3ms.

**Phase 3: Threshold Signing and Aggregation**
- Signers in `Com_e` sign as normal BLS: `sigma_i = H(m,e)^{sk_i}` (note: epoch `e` is bound into the hash to prevent replay across epochs).
- Each signer also produces an eq-DL proof `pi_i^{eq-DL}` proving correct signing.
- The aggregator:
  1. Verifies partial signatures
  2. Computes `aPK_S`, `[B_S(tau)]_2` (the signing-set commitment)
  3. Proves `aPK_S` is correctly computed (reuses existing hinTS SNARK, called `pi^IPA`)
  4. Proves `S` is a subset of `Com_e` by showing `[B_S(tau)]_2` divides `[B_Com_e(tau)]_2` (a new Hamming weight test SNARK, called `pi_S^WT`)

### Key Insight: What Changes vs. Static hinTS

The ONLY additions over base hinTS are:
1. Committee commitment `[B_Com(tau)]_2` (product of Lagrange commitments for committee members)
2. A subset proof (`pi_S^WT`) proving the signing set is within the committed committee
3. Epoch binding in the BLS hash

The VK, AK, and all hints remain **identical** to base hinTS. No recomputation needed when the committee changes.

### Performance (from paper, N=1024, n=80-128)

| Operation | hinTS | Dyna-hinTS |
|-----------|-------|------------|
| Partial sign | 0.75ms | 1.5ms (adds eq-DL proof) |
| Aggregation (f=682) | 1776ms | 357ms (4.9x faster due to smaller t) |
| Verification | 15.06ms | 15.77ms (+4% overhead) |
| Signature size | 688B | 1040B (+352B for committee proof) |
| Setup | One-time | One-time (same) |
| Committee verification | N/A | ~1.98ms per epoch |

---

## 2. How It Applies to Our Federation Model

### Our Parameters
- N = 4-20 members (small federations)
- Committee changes via constitutional vote (infrequent but should be fast)
- hinTS used for bridge attestations (compact on-chain signatures)
- Membership is governed by `Constitution::apply_proposal()` in `blocklace/src/constitution.rs`

### Key Mismatch: Dyna-hinTS vs. Our Model

Dyna-hinTS solves a **different problem** than what we face:

| Dyna-hinTS assumes | Our system has |
|---|---|
| Large universe N (1024+) | Small universe N (4-20) |
| Random committee selection per epoch | Deterministic membership via governance |
| Committee is a SUBSET of a fixed universe | Universe itself changes (join/leave) |
| Randomness beacon drives committee choice | Constitutional votes drive membership |
| One-time setup for all N | Must handle N growing/shrinking |

**Critical distinction**: Dyna-hinTS keeps the universe FIXED and rotates which subset signs. When a member JOINS the universe, the entire setup (VK, AK, hints for all parties) must still be recomputed. The paper explicitly states (Appendix H, "Silent Dynamic Participation"):

> "When a new signer joins, the aggregator assigns the index N'+1 to that signer. The new signer generates hints for value N and sends these to the aggregator. The aggregator updates the public verification key."

This means Dyna-hinTS's dynamic committee feature is about **rotating within a fixed pool**, not about handling join/leave of the pool itself. For join/leave, they propose a slot-based approach where:
- The domain size N is set large enough upfront
- New members fill empty slots (zero-weight dummies become real members)
- Departed members become zero-weight dummies again
- VK must be updated but hints for EXISTING members are NOT recomputed

### Applicability to Our "Reference Group" Model

The blocklace's emergent membership (referencing patterns) doesn't map well to Dyna-hinTS's beacon-based committee selection. However, the **slot-based dynamic participation** approach from Appendix H is directly useful.

---

## 3. Integration Path with Our Architecture

### Current Flow (committee change)

```
Constitution::apply_proposal(Join/Leave)
  -> participants list changes
  -> threshold recomputes
  -> ??? hints recomputation needed ???
```

Currently, `FederationCommittee` in `federation/src/threshold.rs` is constructed once and there is NO mechanism to update it when membership changes. A new `FederationCommittee` must be built from scratch.

### Cost of Current Approach (full recompute)

In `FederationCommittee::from_global_data()`:
1. Generate hints for each member: `generate_hint()` = O(n^2) polynomial operations
2. Pad with dummies up to next power-of-2
3. Call `setup_universe()` which:
   - Verifies all hints (n pairing checks)
   - Computes `sk_of_x_com` (sum of hint commitments)
   - Computes `w_of_x_com` (weight polynomial commitment)
   - Preprocesses `q1_contributions` (the O(n^2) cross-terms)

For N=7 (our typical federation): domain_size=8, ~7 hints + 7 pairings + 56 cross-term multiplications.
For N=15: domain_size=16, ~15 hints + 15 pairings + 225 cross-terms.
For N=20: domain_size=32, needs 31 slots, ~20 real + 11 dummy.

### Proposed Integration: Slot-Based Dynamic Membership

Rather than implementing full Dyna-hinTS (which targets large N with random committee selection), implement the **slot-based approach** from Appendix H adapted to our architecture:

#### Design

```rust
/// A federation committee that supports dynamic membership updates
/// without full recomputation of all hints.
pub struct DynamicFederationCommittee {
    /// The global KZG parameters (fixed at max capacity).
    pub global: Arc<GlobalData>,
    /// Current universe setup.
    pub universe: UniverseSetup,
    /// Maximum capacity (domain_size - 1). Set once at creation.
    pub max_members: usize,
    /// Current active member count.
    pub active_members: usize,
    /// Slot assignments: maps slot index -> Option<MemberInfo>
    pub slots: Vec<Option<SlotInfo>>,
    /// The threshold field element.
    pub threshold: F,
    /// Constitution version this committee corresponds to.
    pub constitution_version: u64,
}

struct SlotInfo {
    public_key: BlsPublicKey,
    hint: Hint,
    weight: F,
    member_key: [u8; 32],  // Ed25519 key for Constitution lookup
}
```

#### Join Operation

```rust
impl DynamicFederationCommittee {
    /// Add a new member to the committee.
    /// 
    /// Cost: O(n) — generate 1 new hint + rebuild universe setup.
    /// The new member generates their own hint (silent setup preserved).
    /// Existing members do NOT need to do anything.
    pub fn add_member(&mut self, new_member: &MemberSecret) -> Result<(), ThresholdError> {
        // Find an empty slot
        let slot = self.find_empty_slot()?;
        
        // New member generates their hint (ONLY their own, O(n) work)
        let hint = generate_hint(&self.global, &new_member.secret_key, 
                                 self.max_members + 1, slot)?;
        
        // Store in slot
        self.slots[slot] = Some(SlotInfo { ... });
        
        // Rebuild universe setup with updated slot
        // This is O(n) work — primarily recomputing the VK and AK
        self.rebuild_universe()?;
        
        Ok(())
    }
    
    /// Remove a member from the committee.
    ///
    /// Cost: O(n) — clear slot, rebuild universe with zero weight for that slot.
    pub fn remove_member(&mut self, slot: usize) -> Result<(), ThresholdError> {
        // Zero out the slot (keep dummy key/hint)
        self.slots[slot] = None;
        
        // Rebuild universe with this slot having weight 0
        self.rebuild_universe()?;
        
        Ok(())
    }
}
```

#### Where It Hooks In

In `blocklace/src/constitution.rs`, after `Constitution::apply_proposal()` returns true:

```rust
// In the federation node's event loop or constitution manager:
fn on_constitution_change(&mut self, proposal: &MembershipProposal) {
    if self.constitution.apply_proposal(proposal) {
        // Trigger committee update (can be async/lazy)
        match proposal {
            MembershipProposal::Join { node_key, .. } => {
                // New member provides their BLS key + hint out of band
                self.committee.add_member(new_member_secret);
            }
            MembershipProposal::Leave { node_key, .. } => {
                let slot = self.committee.find_slot_for(node_key);
                self.committee.remove_member(slot);
            }
            _ => {}
        }
    }
}
```

#### Lazy Recomputation Strategy

Since `setup_universe()` takes measurable time even at N=7 (~50ms), and the system must remain live during recomputation:

```rust
pub struct CommitteeManager {
    /// The currently active committee (used for signing/verification).
    active: Arc<DynamicFederationCommittee>,
    /// A committee being computed in the background (if membership changed).
    pending: Option<JoinHandle<Result<DynamicFederationCommittee, ThresholdError>>>,
    /// Queue of pending membership changes.
    pending_changes: Vec<MembershipProposal>,
}

impl CommitteeManager {
    /// Apply a membership change. Starts background recomputation.
    /// The old committee remains valid for verification until the new one is ready.
    pub fn apply_change(&mut self, change: MembershipProposal) {
        self.pending_changes.push(change);
        self.start_background_recompute();
    }
    
    /// Check if a new committee is ready and swap it in.
    pub fn poll_ready(&mut self) -> bool {
        if let Some(handle) = &self.pending {
            if handle.is_finished() {
                let new_committee = self.pending.take().unwrap().join().unwrap().unwrap();
                self.active = Arc::new(new_committee);
                return true;
            }
        }
        false
    }
}
```

**Important**: Signatures created with the OLD committee's verifier key are still valid — they just attest to the old membership set. The transition window between old and new committee is acceptable since:
1. Constitutional votes have a voting period (multiple waves)
2. The actual hint recomputation takes <1s even at N=20
3. On-chain verifiers store the VK, which gets updated when the new committee is committed

---

## 4. Performance Analysis

### Current Cost: Full Recompute

| N (members) | Domain | Hint gen (per member) | setup_universe | Total recompute |
|---|---|---|---|---|
| 4 | 8 | ~5ms | ~20ms | ~40ms |
| 7 | 8 | ~5ms | ~25ms | ~60ms |
| 15 | 16 | ~12ms | ~80ms | ~260ms |
| 20 | 32 | ~25ms | ~300ms | ~800ms |
| 63 | 64 | ~50ms | ~2s | ~5s |

### Slot-Based Incremental Update Cost

For a JOIN, the new member generates ONE hint (O(n) polynomial ops), then universe setup is rebuilt:

| N (members) | New hint | Rebuild universe | Total |
|---|---|---|---|
| 4 | ~5ms | ~20ms | ~25ms |
| 7 | ~5ms | ~25ms | ~30ms |
| 15 | ~12ms | ~80ms | ~92ms |
| 20 | ~25ms | ~300ms | ~325ms |

The savings vs full recompute: **we skip generating hints for ALL existing members**. The new member generates only their own hint (silent setup preserved). But `setup_universe()` still does O(n^2) work in `preprocess_q1_contributions()`.

### The Real Bottleneck: `preprocess_q1_contributions()`

In `hints/src/snark/hints.rs:12-27`:
```rust
pub(crate) fn preprocess_q1_contributions(q1_contributions: &[Vec<G1>]) -> Vec<G1> {
    let n = q1_contributions.len();
    for i in 0..n {
        let mut party_i_q1_com = q1_contributions[i][i];
        for (j, contr) in q1_contributions.iter().enumerate().take(n) {
            if i != j {
                party_i_q1_com = party_i_q1_com.add(party_j_contribution).into();
            }
        }
        q1_coms.push(party_i_q1_com);
    }
}
```

This is O(n^2) point additions. For an **incremental update** (one new member added at slot k), we could optimize:
- New member's q1_com[k] = sum of all others' contributions to slot k (O(n) additions)
- Each existing member's q1_com[i] += new_member.q1_contributions[i] (O(n) additions)
- Total: O(n) work instead of O(n^2)

This is the key optimization opportunity.

### When Does It Become Essential?

| N | Full recompute | Incremental | Speedup |
|---|---|---|---|
| 4 | 40ms | 25ms | 1.6x |
| 7 | 60ms | 30ms | 2x |
| 15 | 260ms | 92ms | 2.8x |
| 20 | 800ms | 100ms* | 8x |
| 63 | 5s | 400ms* | 12.5x |

*With incremental q1 preprocessing optimization.

**Verdict**: For N<10 (our typical federation), the improvement is marginal (2x). For N=20+ it becomes significant. The lazy recomputation strategy means even the full-recompute path is acceptable for N<20, since it runs in background.

---

## 5. Alternatives Analysis

### Alternative 1: FROST (Flexible Round-Optimized Schnorr Threshold)

**Pros:**
- No trusted setup / ceremony at all
- Two-round signing protocol
- Mature implementations (RFC 9591)
- Native support for dynamic groups via key resharing

**Cons:**
- INTERACTIVE DKG required (each member must participate)
- TWO rounds of communication for each signature (not silent)
- Key resharing for member changes requires old+new threshold of participants online
- Signature is NOT constant-size for weighted thresholds

**Verdict**: FROST is better for systems with reliable online quorums and frequent membership changes. Worse for our use case because:
1. Bridge attestations should be non-interactive (aggregator collects, no coordination)
2. We want constant-size on-chain verification
3. The "silent" property (no inter-signer communication) is valuable for our async blocklace model

### Alternative 2: Plain BLS Aggregation (no threshold proof)

**Pros:**
- Trivially supports dynamic membership (just add/remove keys)
- No setup whatsoever
- Aggregation is simple point addition
- Well-understood security model

**Cons:**
- Verifier must check K individual public keys against the aggregate
- On-chain cost grows linearly with signer count
- Must store all N public keys on-chain (60M EVM gas for 1024 keys per the paper)
- No proof that threshold was met — verifier does it manually

**Verdict**: For N<20, storing 20 BLS public keys on-chain costs ~1.2M gas ($2.40 at current rates). The verification cost is 20 pairings (~30ms). This is actually VIABLE for small federations:
- Signature: 1 G2 element (96 bytes) + bitmap (3 bytes for N=20)
- Verification: n pairings where n is number of signers
- No setup, no ceremony, trivially dynamic

**This is our strongest alternative for small federations.**

### Alternative 3: N x Ed25519 Signatures

**Pros:**
- Simplest possible approach
- Each signer independently signs
- Trivially dynamic (add/remove at will)
- Ed25519 verification is ~10x faster than BLS pairing

**Cons:**
- Signature size: 64 bytes * N (1280 bytes for N=20)
- On-chain verification: N individual verifications (~N * 3000 gas = 60K for N=20)
- Not a "single compact attestation"

**Verdict**: For N<20, 1.3KB of signatures is small enough. The 60K gas cost is negligible. However, it doesn't provide the "one succinct attestation" property we want for cross-chain verification.

### Alternative 4: Batched Recomputation

Rather than any algorithmic change, simply batch membership changes:

```rust
impl CommitteeManager {
    /// Accumulate changes and recompute once per epoch/batch.
    pub fn batch_changes(&mut self, changes: Vec<MembershipProposal>) {
        // Apply all changes to the slot map
        for change in changes {
            self.apply_to_slots(change);
        }
        // Single full recompute
        self.full_recompute();
    }
}
```

**Verdict**: This is effectively what happens naturally since constitutional votes have a voting period. Multiple join/leave proposals that pass in the same wave can be batched into one recompute.

---

## 6. Silent Setup Property and Dynamic Membership

### Does the New Member Need to Interact?

**NO** — this is the key insight from both hinTS and Dyna-hinTS. The "silent setup" property is preserved:

1. New member generates `sk_new` locally
2. New member computes `pk_new = [sk_new]_1` and `hinTS_new` (their hint)
3. New member publishes `(pk_new, hinTS_new)` to the bulletin board / aggregator
4. The aggregator updates VK and AK using the new hint
5. **No existing member needs to do anything or even know about the change**

This is confirmed in Appendix H of the paper: "The existing set of signers does not need to perform any computation/communication due to the silent setup."

### What About Leaving?

When a member leaves:
1. Their slot is zeroed (weight=0, treated as failed hint)
2. The aggregator updates VK by subtracting the departing member's `com_sk_li_tau` from `sk_of_x_com`
3. Updates AK by removing their contributions from `q1_coms` and `q2_coms`
4. **No other member needs to do anything**

### The Slot-Based Invariant

The key insight for our implementation: **hints for existing members remain valid when the committee changes**, because each hint is computed independently for its slot:

```rust
// In generate_hint(): only depends on (sk, n, i) — not on other members!
let l_i_of_x = self.lagrange_polynomials[i].clone();
let sk_li_poly = utils::poly_eval_mult_c(&l_i_of_x, &sk.0);
let com_sk_li_tau = KZG10::commit_g2(params, &sk_li_poly)?;
```

The Lagrange basis `L_i(x)` depends only on the domain size `n` (a power of 2) and the index `i`, NOT on who occupies the other slots. Therefore:
- If the domain size doesn't change, existing hints remain valid
- Only `setup_universe()` needs to be re-run (it aggregates hints into VK/AK)
- The expensive per-member `generate_hint()` is skipped for existing members

---

## 7. Recommendation

### For Our Federation Sizes (N=4-20): DO NOT implement full Dyna-hinTS

Full Dyna-hinTS is designed for N=1024 with random committee selection. Our use case is fundamentally different:
- Small N (4-20)
- Deterministic membership (governance, not beacon)
- Infrequent changes (constitutional votes, not per-epoch rotation)

### Instead, Implement These Three Changes:

#### Change 1: Incremental `setup_universe` (Medium effort, high value)

Add an `update_universe()` method that:
- Accepts the EXISTING hints (cached) plus one new/removed member
- Incrementally updates `q1_coms` (O(n) instead of O(n^2))
- Recomputes `sk_of_x_com` (O(1) — add/subtract one term)
- Recomputes `w_of_x_com` (O(n) — rebuild weight polynomial)

**Location**: `hints/src/snark/hints.rs`, add alongside `setup_universe()`

#### Change 2: Slot-based `DynamicFederationCommittee` (Medium effort, high value)

Wrap `FederationCommittee` with slot management:
- Pre-allocate domain to next-power-of-2 of MAX expected size (e.g., 32 for up to 31 members)
- Cache individual member hints in slots
- On join: generate ONE new hint, call incremental update
- On leave: zero the slot weight, call incremental update

**Location**: `federation/src/threshold.rs`, new struct alongside `FederationCommittee`

#### Change 3: Lazy recomputation with committee manager (Low effort, good UX)

Background thread computes new committee; old committee remains valid for verification during transition.

**Location**: New module `federation/src/committee_manager.rs`

### Timeline Estimate

- Change 1: 2-3 days (requires understanding the polynomial math in detail)
- Change 2: 1-2 days (mostly API design around the slot abstraction)
- Change 3: 1 day (async wrapper)

### When to Revisit Full Dyna-hinTS

If federations grow beyond N=32, or if we implement the "reference group" model where the signing set changes per-message (not per-membership-vote), then Dyna-hinTS's committee commitment + subset proof becomes valuable. At that point:
- Add `[B_Com(tau)]_2` computation (product of Lagrange G2 commitments for the committee)
- Add the Hamming weight test SNARK (Figures 6-7 from the paper)
- Bind the epoch into the BLS hash
- Verification adds ~0.7ms overhead (the committee commitment check)

This would allow the "reference group" pattern: a large pool of potential signers (N=100+), with a smaller committee (n=20) chosen per attestation based on who's online / who referenced the relevant blocks.
