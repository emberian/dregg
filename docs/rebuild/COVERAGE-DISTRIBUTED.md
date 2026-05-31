# Audit: Dregg1 Distributed/Consensus/Networking Coverage in Dregg2 Lean Metatheory

**Audit Date:** 2026-05-31  
**Scope:** Distributed consensus, networking, and coordination semantics from Rust implementation covered by Lean formalization  
**Methodology:** Read Rust `blocklace/` (11k LOC), `federation/` (8k LOC), `node/` (24k LOC), `coord/` (6k LOC), `dfa/` (2.5k LOC); cross-reference Lean `metatheory/Dregg2/Authority/Blocklace.lean`, `Coordination.lean`, `Proof/BFT*.lean`, `Exec/DfaRouting.lean`  
**Legend:** **(P)** = PROVED (faithful model, full soundness); **(A)** = modeled ABSTRACTLY (captures spec-shape but omits real runtime behavior); **(X)** = ABSENT

---

## Summary: Critical Findings

**Honest Assessment:** Lean metatheory is strong on consensus theory (BFT safety, causal DAGs, DFA routing) but **fundamentally mismatches** Rust's actual distributed system on three critical axes:

1. **Consensus Model Mismatch** — Lean formalizes classical voting-round BFT (Li–Lesani / Malkhi–Reiter); Rust implements Cordial Miners DAG-based consensus. The theorems are inapplicable.
2. **Network Oracle vs. Reality** — Lean assumes `recv_mono` (messages eventually delivered); Rust's cordial dissemination protocol (push/pull/pull-response) is unformalized.
3. **Coordination Deadlock-Freedom** — Explicitly OPEN per `Coordination.lean` docstring; Layer 3 (Stingray) entirely absent.

---

## I. Coverage Matrix: Dregg1 Features vs. Dregg2 Formalizations

| **Feature (Rust File:Line)** | **Dregg2 Location** | **Status** | **Gap If A** | **Severity** |
|---|---|---|---|---|
| **Blocklace: Content-addressed DAG** | Authority/Blocklace.lean | **(P)** | Hash-injectivity is §8 obligation, not proved | High |
| Equivocation detection: `(creator, seq, id)` | Blocklace.lean:179–202 | **(A)** | Rust checks triple heuristic; Lean checks incomparability only (no seq enforcement) | **HIGH** ⚠ |
| Causal closure (`insert`, `merge`) | Blocklace.lean:182–223, finality.rs | **(P)** | — | Critical |
| Finality level progression (Local→Bilateral→Attested→Ordered) | finality.rs:156–177 + Blocklace.lean:358–373 | **(A)** | Lean models tier-2/3; tier-0/1 unmodeled | Medium |
| **Quorum threshold (2f+1)** | federation/lib.rs:140–146 + Proof/BFT.lean | **(P)** | — | Critical |
| **BFT consensus (rounds, voting, quorum)** | Proof/BFT.lean:54–181 | **(A)** | Rust uses Cordial Miners DAG, not voting rounds | **CRITICAL** ⚠ |
| Blocklace honest virtual chain | finality.rs:217–219 (self_seq increment) + Blocklace.lean:228–245 | **(A)** | Rust uses seq counter; Lean uses `≺`-ordering | High |
| **Gossip/dissemination protocol** | blocklace_sync.rs (72k LOC) + dissemination.rs | **(X)** | Entirely absent; only `recv_mono` oracle assumed | **CRITICAL** ⚠ |
| **Coordination Layer 2 (atomic 2-phase commit)** | coord/atomic.rs + Coordination.lean:1–60 | **(A)** | Rust protocol (Propose/Vote/Commit); Lean MPST spec without step formalization | High |
| **Coordination Layer 3 (Stingray)** | coord/budget.rs (72k LOC) | **(X)** | Entirely absent | **CRITICAL** ⚠ |
| **Deadlock-freedom / progress** | Coordination.lean | **(X)** | "[REFUTED] the linearity⇒I-confluence conflation"; no proof | **CRITICAL** ⚠ |
| **DFA routing (accepting runs)** | dfa/router.rs:490–512 + Exec/DfaRouting.lean | **(P)** | — | Critical |
| **Federation revocation (Merkle tree)** | federation/revocation.rs | **(X)** | Entirely absent | **CRITICAL** ⚠ |
| **Node turn-production loop** | node/main.rs | **(X)** | No model of node's consensus loop | **CRITICAL** ⚠ |
| **Leader election** | (implicit in gossip) | **(X)** | Lean models randomized Pacemaker; Rust has no explicit leader code | **CRITICAL** ⚠ |

---

## II. Critical Gaps Explained

### Gap 1: Consensus Model — Classical BFT vs. Cordial Miners DAG

**Rust consensus** (`blocklace/` + `node/`):
- Uses Cordial Miners DAG (arXiv:2402.08068).
- Blocks accumulate with causal links and acknowledgment edges.
- No rounds, no leader election, no voting phases.
- Finality = quorum (2f+1) acknowledgments (ack edges in the DAG).

**Lean model** (`Proof/BFT.lean`):
- Classical BFT: rounds, leader proposals, replica votes.
- Quorum threshold = 2f+1 distinct voters per height.
- Safety: `bft_agreement` — two quorums for distinct blocks → contradiction.
- Liveness: randomized synchronizer with expected-O(1) views to honest leader.

**The Mismatch:**
```
Rust:   Block → Gossip → Ack accumulation → Quorum → Finality
Lean:   Leader proposes → Round vote → Quorum → Consensus
```

**Consequence:** Lean's BFT theorems are inapplicable to Rust's actual consensus. Rust's finality relies on blocklace paper's safety argument (incomparable-pair detection), not on voting-round consistency.

**Severity:** **CRITICAL**

---

### Gap 2: Gossip Protocol — Assumed vs. Unformalized

**Lean assumption** (`World.recv_mono`):
```lean
recv_mono : ∀ t t', t ≤ t' → World.recv t ⊆ World.recv t'
```
"Messages, once received by an honest node, stay received." (CRDT union semantics.)

**Rust reality** (`blocklace_sync.rs` + `dissemination.rs`):
- Implements **cordial dissemination** (push/pull/pull-response).
- Tracks peer knowledge: "which blocks has peer X seen?"
- Sends causal deltas: "here are the blocks you need plus their dependencies."
- No guarantee that all peers eventually receive all blocks (liveness is probabilistic, not deterministic).

**The Gap:**
- Lean proves `recv_mono` correctness under the oracle.
- Rust's gossip protocol must *achieve* `recv_mono` — but it is **not formalized**.
- If gossip is broken (e.g., a peer drops blocks, or causal delta calculation is wrong), Lean's proofs are moot.

**Consequence:** All network-dependent proofs (BFT safety, finality, liveness) rest on an unverified foundation: the cordial dissemination protocol.

**Severity:** **CRITICAL**

---

### Gap 3: Equivocation Detection Heuristic — Sequence Number vs. Incomparability

**Rust detector** (`finality.rs:795–808`):
```rust
pub fn detect_equivocation(&self, block: &Block) -> Option<EquivocationProof> {
    let id = block.id();
    for (existing_id, existing) in &self.blocks {
        if existing.creator == block.creator
            && existing.seq == block.seq  // ← SAME SEQUENCE NUMBER
            && *existing_id != id         // ← DIFFERENT CONTENT
        {
            return Some(EquivocationProof { ... });
        }
    }
    None
}
```

**Lean detector** (`Blocklace.lean:179–202`):
```lean
structure Equivocation (B : Lace) (p : AuthorId) (a b : Block) : Prop where
  incomp : incomparable B a b  -- neither a ≺ b nor b ≺ a
```

**The Difference:**
| Aspect | Rust | Lean |
|---|---|---|
| **Condition** | `(creator, seq, id)` triple with same creator+seq, different id | Incomparable pair: `¬(a ≺ b) ∧ ¬(b ≺ a)` |
| **Depends on** | Sequence number matching | Causal DAG structure only |
| **Content-agnostic?** | No (checks `id` mismatch) | Yes (incomparability is pure order) |

**The Asymmetry:**
- Rust: "Equivocation = same creator + same seq + different hash."
- Lean: "Equivocation = same creator + incomparable blocks (seq not mentioned)."

These are **not equivalent**:
- Rust's rule is **narrower**: requires sequence number collision.
- Lean's rule is **stronger**: any incomparable pair counts, regardless of seq.

But for an **honest node**, both rules fire the same way:
- Honest node increments seq, so no duplicate seqs.
- Honest node acks its own tip, so its blocks form a totally-ordered chain `≺`.
- Neither detector fires for honest nodes.

**The Real Gap:** Rust's `detect_equivocation` is called in `receive_block` and `merge` when processing incoming blocks. The function checks **all blocks in the map** for a seq-duplicate. Lean's theorem `honest_no_equivocation` assumes the **entire blocklace satisfies `HonestChain`** (all blocks by an author are `≺`-ordered), which is a *global* invariant on all creators simultaneously. Rust **does not enforce `HonestChain` globally** — it only increments its own `self_seq`.

**Consequence:** Lean's proof that honest nodes never equivocate uses a property (total ordering of each creator's blocks) that Rust's node code does **not enforce**. Rust relies on the **blocklace structure itself** (incomparable detection) to catch Byzantine nodes, but Lean models this with a semantic total-ordering property on honest creators.

**Severity:** **HIGH** — equivocation is the Byzantine-repelling core.

---

### Gap 4: Coordination Deadlock-Freedom

**Coordination.lean docstring** (lines 36–45):
```
The THREE judgements, kept ORTHOGONAL:
  * Law 1 (conservation / linearity) — Core / Resource;
  * Law 2 (ordering / session) — THIS module's project/projectability;
  * the third judgement (I-confluence) — [REFUTED] the linearity⇒I-confluence conflation.

...the soundness/fidelity/deadlock-freedom THEOREMS are stated as faithful Props
with `sorry` bodies (each `sorry` = a real obligation; many are `study-choreography`'s
CONFIRMED-OPEN problems — flagged in the relevant docstrings).
```

**Rust coordination** (`coord/atomic.rs`):
- Implements 2-phase commit (Propose → Vote → Commit/Abort).
- No explicit deadlock-freedom proof or analysis.

**Lean status:**
- Deadlock-freedom: **`sorry` — NOT PROVED.**
- Global/local type projection: **defined** but fidelity unproven.
- I-confluence: **conflict explicitly named and flagged as unresolved**.

**Consequence:** Coordination safety (the property that multi-party turns don't deadlock) is **unverified**. Any deadlock bug in the 2PC implementation would not be caught by Lean.

**Severity:** **CRITICAL**

---

### Gap 5: Stingray Bounded Counters (Layer 3)

**Rust implementation** (`coord/budget.rs`, `coord/shared_budget.rs`, ~200 LOC):
- Slices a balance into per-silo bounded counters.
- Slice ceiling = `B × (f+1) / (2f+1)`.
- Each silo can debit locally without coordination.
- Rebalance via signed spending certificates.

**Lean:** Completely absent. No formalization, no proof of aggregate safety or rebalance correctness.

**Consequence:** Concurrent spending (a critical performance feature) is unverified. If the slice-ceiling formula is wrong or rebalance logic is buggy, no Lean proof catches it.

**Severity:** **CRITICAL**

---

### Gap 6: Revocation Merkle Tree (Federation)

**Rust** (`federation/revocation.rs`):
- Maintains Merkle accumulator of revocations.
- Non-membership proofs verified against attested roots.

**Lean:** Completely absent.

**Consequence:** A critical security feature is unformalized. If the Merkle tree or proof logic is flawed, Lean does not catch it.

**Severity:** **CRITICAL**

---

### Gap 7: Honest-Vote-Once Law (Lean assumption, Rust non-enforcement)

**Lean assumes** (`Proof/BFT.lean:97–98`):
```lean
honest_vote_once : ∀ (v b₁ b₂ : Nat), ¬ Byzantine v →
  v ∈ votersFor votes b₁ → v ∈ votersFor votes b₂ → b₁ = b₂
```
"An honest node votes for at most one block per height."

**Rust enforcement:** The node gossips blocks and counts acks. There is **NO explicit vote-once enforcement**. A Rust node can ack two incomparable blocks, as long as they're causally independent. The blocklace structure (DAG + incomparability detection) replaces explicit voting discipline.

**Consequence:** Lean's BFT safety proof depends on an assumption that **Rust's node software does not enforce**. Rust relies on protocol correctness (blocklace + gossip), not voting discipline.

**Severity:** **CRITICAL**

---

## III. What IS Formally Proved

### Proved (P) Features

| Feature | Theorem | File |
|---|---|---|
| **Blocklace equivocation detectability** | `equivocation_detectable`, `observer_detects` | Blocklace.lean:198–213 |
| **Honest chains avoid equivocation** | `honest_no_equivocation`, `honest_chain_implies_comparable` | Blocklace.lean:238–257 |
| **Causal closure correctness** | `lookup_of_mem`, `cdt_is_blocklace` | Blocklace.lean:106–354 |
| **Finality monotonicity** | `attested_mono` | Blocklace.lean:375–393 |
| **BFT safety (under honest model)** | `bft_safety`, `bft_agreement` | Proof/BFT.lean:174–193 |
| **Quorum intersection** | `honest_witness_in_intersection` | Proof/BFT.lean:121–165 |
| **DFA routing soundness** | `routed_message_followed_accepting_route`, `unique_route`, `delivery_route_nonempty` | Exec/DfaRouting.lean:135–189 |
| **Randomized synchronizer (expected-O(1) views)** | `expected_views_O1`, `honest_hit_as`, `synchronizer_round_obtains` | Proof/Synchronizer.lean:113–226 |

### Abstractly Modeled (A) Features

| Feature | Model | Gap |
|---|---|---|
| **Consensus finality** | Ack-count threshold (2f+1) | Modeled; implementation details unproven |
| **2-Phase commit coordination** | MPST global/local types with projection | Protocol steps and deadlock-freedom NOT proved |
| **Network delivery** | `World.recv_mono` oracle | Assumes eventual delivery; gossip protocol unverified |
| **BFT liveness** | Randomized leader election + GST synchronizer | Model assumed; Rust's actual leader selection not formalized |

### Absent (X) Features

| Feature | Impact |
|---|---|
| **Gossip/dissemination protocol** | Network safety unverified |
| **Stingray bounded counters** | Concurrent spending unverified |
| **Revocation Merkle tree** | Revocation verification unverified |
| **Coordination deadlock-freedom** | Multi-party safety unproven |
| **Node turn-production loop** | Consensus loop unmodeled |
| **Leader election** | Liveness mechanism unrelated to Lean model |
| **Mempool state machine** | Local state unmodeled |

---

## IV. Severity Ranking of Gaps

### CRITICAL (affect safety or liveness fundamentally)

1. **Gossip protocol unformalized** — `recv_mono` oracle assumed without proof of cordial dissemination.
2. **BFT model mismatch** — Lean models voting-rounds; Rust uses Cordial Miners DAG.
3. **Honest-vote-once not enforced** — Lean assumes; Rust does not.
4. **Stingray unformalized** — Concurrent spending entirely unverified.
5. **Revocation Merkle tree absent** — Critical security feature unmodeled.
6. **Coordination deadlock-freedom OPEN** — Explicitly unproven.
7. **Leader election mechanism** — Pacemaker model has no Rust counterpart.

### HIGH (significant coverage gaps)

8. **Equivocation detection heuristic** — Sequence-number vs. incomparability; enforcement differs.
9. **Coordination 2-Phase commit** — MPST spec without protocol formalization.
10. **Cordial dissemination incentives** — Peer knowledge, causal-delta optimization unformalized.
11. **Virtual-chain enforcement** — Lean's `≺`-ordering vs. Rust's seq-incrementing differ.

---

## V. Final Verdict by Layer

| Layer | Grade | Summary |
|---|---|---|
| **1. Blocklace (DAG consensus)** | **A–** | Causal structure proved; equivocation detection has model-mismatch; honest chains use `≺`-ordering not enforced in Rust |
| **2. Coordination (atomic multi-party)** | **C–** | MPST spec without protocol steps or deadlock-freedom proof |
| **3. Coordination (Stingray budget)** | **F** | Entirely absent |
| **4. Federation (consensus + revocation)** | **D** | Quorum threshold proved; revocation Merkle tree absent; BFT model inapplicable |
| **5. Network (gossip)** | **C–** | Only oracle `recv_mono` assumed; protocol unformalized |
| **6. DFA routing** | **A** | Delivery soundness, determinism, routing fully proved |
| **7. Node (turn loop, leader election)** | **F** | Unmodeled |
| **Overall** | **C+** | Strong on consensus theory; weak on distributed systems reality |

---

## VI. Key Recommendations

1. **Reframe Lean as consensus-theoretic sandbox**, not a faithful model of dregg1.
2. **Isolate network oracle assumption** — document that all proofs rest on `recv_mono` without proving gossip achieves it.
3. **Resolve BFT vs. Cordial Miners mismatch** — clarify whether Rust's DAG-based consensus benefits from classical BFT safety or needs a separate argument.
4. **Formalize Stingray** — new metatheory module for Layer 3 soundness.
5. **Formalize revocation Merkle tree** — critical security feature must be verified.
6. **Prove deadlock-freedom** — close `Coordination.lean` `sorry` bodies or name sharp obstructions.

---

**Honest Conclusion:** Lean is a rigorous **consensus theory** sandbox with clean proofs of BFT safety, DAG causal structure, and DFA routing. But it does NOT faithfully model dregg1's distributed system, which uses a DAG-based consensus (not voting-rounds), an unformalized gossip protocol, and unverified coordination semantics. The gap is not a defect in Lean — it is a *design choice* favoring theory over implementation fidelity. For an industrial distributed system, the mismatch is material and should be explicitly acknowledged in any security/correctness claim.

