# COVERAGE AUDIT: dregg1 BRIDGE / APPLICATIONS / ECONOMICS / SDK vs dregg2 Lean Metatheory

**Audit Date:** 2026-05-31  
**Scope:** Cross-reference Real Rust Implementations (dregg1) with Lean Formalization (dregg2)  
**Repos:**
- **dregg1 (Rust):** `/Users/ember/dev/breadstuffs/bridge/`, `starbridge-apps/`, `sdk/`, `token/`
- **dregg2 (Lean):** `/Users/ember/dev/breadstuffs/metatheory/`

**Verdict Summary:**
- **Bridge Protocol:** PARTIALLY MODELED — Comparison predicate (**P**ROVED) but atomic-swap semantics and relayer oracle remain (**A**BSTRACT in design doc, not formalized in Lean code)
- **Shipped Applications (nameservice, identity, subscription, governed-namespace):** (**A**BSTRACT) — Not modeled in dregg2; ClockDAG is a separate non-shipped demonstrator
- **SDK (turn construction, wallet, capabilities):** (**A**BSTRACT) — Turn execution semantics in Lean do not bind real SDK proof generation or token attenuation
- **Economics (fees, gas, demurrage):** PARTIALLY MODELED — Gas metering (**P**ROVED) in `Exec/Gas.lean`; no fee market, staking, or demurrage

---

## 1. COVERAGE MATRIX

### Bridge / Cross-Chain Protocol

| Feature | dregg1 Location | dregg2 Location | Status | Notes |
|---------|---|---|---|---|
| **Comparison predicate (threshold ≤ v)** | `bridge/src/lib.rs:1-70` (AIR binding) | `metatheory/Dregg2/Crypto/Bridge.lean` (full end-to-end) | **(P) PROVED** | `bridge_bridge` theorem: Satisfies ↔ BridgeRelation; comparison via `RecordCircuit.range` (fully proved, no primitive seam) |
| **OPENING (digest binding c = compress vDigest salt)** | `bridge/src/lib.rs` (PiBinding in AIR) | `Dregg2/Crypto/Bridge.lean:68-69` (Opens definition) | **(P) PROVED** | Abstract `compress` equation; binding is Layer-A carrier, never invoked in Bridge.lean itself |
| **STARK verify → relation holds** | `bridge/src/present.rs:3821` (verify oracle) | `Dregg2/Crypto/Bridge.lean:240-247` (bridge_verify_sound) | **(P) DERIVED** | Soundness derived from `bridge_bridge` + STARK `extractable` carrier |
| **Dial wiring at selective floor** | implicit in `bridge/src/` | `Dregg2/Crypto/Bridge.lean:275-287` (bridgeKindObligation, bridge_dial_wired) | **(P) PROVED** | Bridge.lean §C: commitment + threshold disclosed, observed value hidden |
| **Atomic swap (lock/mint nonce pairing)** | `plans/midnight-bridge-production.md` (design doc) | `PHASE-BRIDGE.md §5.1` (sorries in BridgeAction algebra) | **(A) ABSTRACT** | BridgeAction structure designed but `bridge_atomic_by_nonce`, `bridge_conservation_cross_chain` theorems in PHASE-BRIDGE.md are `sorry` — never formalized in actual Lean |
| **Dispute oracle (challenge window + slashing)** | `bridge/src/present.rs` (relayer state machine, federation attestation) | `PHASE-BRIDGE.md §5.2` (pseudocode in design doc) | **(A) ABSTRACT** | Design names `DisputeOracle` class but no `.lean` file implements it; Dispute assumption carried as a `Prop` parameter in the verifier |
| **Foreign-chain finality model** | `bridge/src/midnight_observer.rs:739` (Cardano light client stub) | `PHASE-BRIDGE.md §4.3` (OPEN: "Foreign finality model is OPEN") | **(X) ABSENT** | Cardano/Ethereum consensus NOT formalized; bridge assumes foreign state as a parameter |
| **Relayer protocol (observe, attest, finalize)** | `bridge/src/present.rs` (federation attestation), `app-framework/src/midnight_bridge.rs` (relayer state machine) | `PHASE-BRIDGE.md §5.3` (pseudocode, not Lean) | **(A) ABSTRACT** | Design doc sketches relayer steps but no formalized state-machine model in Lean |
| **Light-client (Merkle membership over foreign blocks)** | `bridge/src/midnight_observer.rs` (Cardano finality) | `Dregg2/Crypto/Merkle.lean` (reusable membership), `PHASE-BRIDGE.md §4.2c` (extension roadmap) | **(A) ABSTRACT** | Merkle membership proved; foreign-chain application to Cardano headers NOT modeled |

### Shipped Applications (nameservice, identity, subscription, governed-namespace)

| Feature | dregg1 Location | dregg2 Location | Status | Notes |
|---------|---|---|---|---|
| **Nameservice registry (register, renew, transfer)** | `starbridge-apps/nameservice/src/lib.rs:1-100+` (FactoryDescriptor, turn builders) | **—** | **(X) ABSENT** | No Lean model; cell programs are ABSTRACT in dregg2 (Exec.CellProgram is a stub) |
| **Identity credential issuance** | `starbridge-apps/identity/src/lib.rs` (credential lifecycle) | **—** | **(X) ABSENT** | Token/credential handling in SDK; no per-app verification in dregg2 |
| **Subscription (publish/consume events)** | `starbridge-apps/subscription/src/lib.rs` (event streaming) | **—** | **(X) ABSENT** | App-specific state machine NOT modeled |
| **Governed namespace (propose, vote, commit)** | `starbridge-apps/governed-namespace/src/lib.rs` (governance voting) | **—** | **(X) ABSENT** | Multi-signer coordination NOT modeled in metatheory |
| **FactoryDescriptor (cell template binding)** | `starbridge-apps/nameservice/src/lib.rs:100+` (field constraints, state schema) | `Dregg2/Exec/CellProgram.lean` (stub) | **(A) ABSTRACT** | CellProgram is a parameter; no real nameservice constraints formalized |
| **Turn builder (build_register_action, build_renew_action, etc.)** | `starbridge-apps/nameservice/src/lib.rs:150+` | **—** | **(X) ABSENT** | SDK turn construction not bound to Lean Turn semantics |

### SDK (Agent Runtime, Cipherclerk, Turn Construction)

| Feature | dregg1 Location | dregg2 Location | Status | Notes |
|---------|---|---|---|---|
| **AgentCipherclerk (token management, signing)** | `sdk/src/cipherclerk.rs:200+` | **—** | **(X) ABSENT** | Local token wallet NOT modeled in Lean |
| **Turn construction (committed payments, conservation proofs)** | `sdk/src/committed_turn.rs:1-150+` (CommittedTurnBuilder, Bulletproof range, conservation proof) | `Dregg2/Exec/TurnExecutor.lean`, `Exec/TurnExecutorFull.lean` (executor, not builder) | **(A) ABSTRACT** | TurnExecutor models *acceptance* (checking turn validity), NOT *construction* (building witness proofs). Bulletproof generation, value commitment creation NOT modeled. |
| **Token attenuation (narrow scope, delegate)** | `token/src/traits.rs:60+` (Attenuation struct, attenuate method) | `Dregg2/Authority/Caveat.lean` (predicate caveats) | **(A) ABSTRACT** | Caveats are auth predicates; Token attenuation (macaroon/biscuit narrowing) is DISTINCT from caveat predicates and NOT formalized |
| **Wallet (hold tokens, prove capability)** | `sdk/src/cipherclerk.rs` (token chain, proof generation) | **—** | **(X) ABSENT** | Proof generation NOT modeled; only Verifier (accept/reject) is in dregg2 |
| **Mnemonic seed management** | `sdk/src/mnemonic.rs:412+` | **—** | **(X) ABSENT** | Key derivation NOT modeled |
| **Proof verification (verify_presentation)** | `sdk/src/verify.rs:935+` | `Dregg2/Crypto/Bridge.lean`, `Dregg2/Authority/Predicate.lean` (predicate verifier) | **(P) PARTIAL** | Predicate verifiers (including Bridge) are proved; full presentation proof verification is NOT unified in dregg2 |
| **CapTP promise / zkpromise (conditional turn)** | `sdk/src/` (NO IMPL) — part of W3-I roadmap | `Dregg2/Exec/CapTP.lean`, `Dregg2/Await.lean` | **(A) IN PROGRESS** | zkpromise/zkawait modeling is ongoing (task #82) |

### Token / Economics

| Feature | dregg1 Location | dregg2 Location | Status | Notes |
|---------|---|---|---|---|
| **Authorization tokens (Macaroon, Biscuit)** | `token/src/lib.rs:1-80+` (AuthToken trait, format detection) | `Dregg2/Authority/Predicate.lean` (predicate verifier), `Bridge.lean` (bridge as predicate) | **(A) ABSTRACT** | Token *format* (HMAC/Datalog) NOT modeled; predicate verifier is a slot for authorization checking |
| **Token attenuation (narrow scope)** | `token/src/traits.rs:60+` (Attenuation, caveats) | `Dregg2/Authority/Caveat.lean` (auth predicates) | **(A) DISTINCT** | Caveats ≠ attenuation; macaroon narrowing is NOT formalized |
| **Macaroon backend (HMAC verify, caveat discharge)** | `token/src/macaroon_backend.rs:500+` (verify_and_discharge) | **—** | **(X) ABSENT** | HMAC verification NOT modeled |
| **Biscuit backend (Datalog, Ed25519 verify)** | `token/src/biscuit_backend.rs:400+` | **—** | **(X) ABSENT** | Datalog evaluation + Ed25519 NOT modeled |
| **Revocation registry (non-membership proofs)** | `token/src/revocation.rs:200+` (RevocationRegistry, NonMembershipProof) | `Dregg2/Crypto/NonMembership.lean` (Merkle non-membership) | **(P) PROVED** | Merkle non-membership is proved; token revocation oracle NOT bound to it |
| **Gas metering (per-action schedule)** | `coord/src/atomic.rs:50+` (fee field in turns) | `Dregg2/Exec/Gas.lean:60-85` (gasCost schedule, execGas executor) | **(P) PROVED** | Gas.lean: 5 action kinds, distinct nonzero costs (revoke=1, balance=2, delegate=3, burn=4, mint=5); `execGas` proves pure guard + fail-closed |
| **Fee market (dynamic pricing, bidding)** | **NOT IMPL** | **—** | **(X) ABSENT** | Fees are constant per-action; no auction/market model |
| **Staking (validator bonds, slashing)** | **NOT IMPL** | **—** | **(X) ABSENT** | Slashing logic is in bridge (Dispute oracle design doc); no general staking model |
| **Demurrage (age-decay of balances)** | **NOT IMPL** | **—** | **(X) ABSENT** | ClockDAG protocol mentions demurrage (SPEC §11) but it is NOT modeled in dregg2 |

---

## 2. BLUNT ASSESSMENT

### Is the Real Bridge Protocol Modeled in Lean?

**Answer: PARTIALLY.**

- **Comparison predicate (threshold ≤ v):** ✅ FULLY PROVED in `Bridge.lean` via `bridge_bridge` theorem. The comparison AIR (`RecordCircuit.range`) has NO primitive seam — it is pure combinatorics proved end-to-end.

- **OPENING (c = compress vDigest salt):** ✅ ABSTRACT but structurally sound. The opening is an uninterpreted equation; its binding/collision-resistance is a Layer-A carrier (`CryptoPrimitives.binding`), never invoked inside Bridge.lean. This is discipline: the seam is named and isolated.

- **Atomic swap (lock/mint with nonce):** ❌ **DESIGN DOC ONLY.** Section 5.1 of `PHASE-BRIDGE.md` sketches the algebra (`BridgeAction` struct, `bridge_atomic_by_nonce` theorem) but these theorems **carry `sorry`** in the doc and are **NOT in any `.lean` file**. The proof sketch says "the federation's agreement on nonce ensures atomicity" but this is informal — a formalized Dispute oracle that enforces the nonce invariant does not exist in the codebase.

- **Dispute oracle (challenge window, slash-on-wrong):** ❌ **PSEUDOCODE IN DESIGN DOC.** Section 5.2 of `PHASE-BRIDGE.md` gives Rust pseudocode for `DisputeOracle` (challenge_window_blocks, finalized check, is_disputed). No `.lean` file exists; the bridge verifier assumes foreign-chain finality as a bare `Prop` parameter (never discharged).

- **Relayer protocol (observe → attest → finalize):** ❌ **DESIGN DOC + IMPLEMENTATION STUB.** Real Rust in `app-framework/src/midnight_bridge.rs` and `bridge/src/present.rs` sketches the state machine (Idle → Observing → AttestingObservation → AwaitingChallenge → Finalizing). No Lean state-machine model; no proof that the relayer-state transitions preserve the bridge invariants.

**Verdict:** The bridge protocol's **soundness core** (comparison + opening) is **PROVED**. The **atomicity guarantee** (the whole reason cross-chain matters) is **DESIGN-ONLY**. The **operational semantics** (how the relay and federation actually enforce atomicity) is **UNMODELED**.

---

### Are ANY of the Shipped starbridge-apps Modeled in dregg2?

**Answer: NO.**

The four shipped apps (nameservice, identity, subscription, governed-namespace) are **NOT formalized in dregg2**. They live as Rust implementations:

- **nameservice:** `starbridge-apps/nameservice/src/lib.rs` — a FactoryDescriptor + turn builders. Dregg2 has a **stub** `Exec.CellProgram` but NO nameservice field-constraint model.
- **identity:** `starbridge-apps/identity/src/lib.rs` — credential issuance and lifecycle. NOT modeled.
- **subscription:** `starbridge-apps/subscription/src/lib.rs` — publish/subscribe event streaming. NOT modeled.
- **governed-namespace:** `starbridge-apps/governed-namespace/src/lib.rs` — multi-signer governance voting. NOT modeled.

**ClockDAG is a SEPARATE, NON-SHIPPED demonstrator:**
- `metatheory/ClockDAG/Model.lean` — a standalone modeling exercise of the Simbi Mesh-Credit protocol (a mutual-credit DAG ledger in PRODUCTION, but NOT dregg2).
- It reuses dregg2 theorems (Conservation, Blocklace, JointCell, Merkle, NonMembership) to model 4 safety invariants.
- It is **NOT part of the dregg2 core** (`Dregg2.lean` does not reference it) and is **NOT a shipped app**.

**Why:** Cell programs are **userspace policy** in dregg2's design. The kernel enforces authority/conservation/causality; the app defines field constraints. No single app's constraints are baked into the metatheory.

---

### Does dregg2 Model the SDK's Turn Construction and Wallet?

**Answer: NO (only the executor, not the builder).**

**What dregg2 DOES:**
- `Exec/TurnExecutor.lean` (basic turns) and `Exec/TurnExecutorFull.lean` (full op-set) — the **executor**: given a turn, does it satisfy authority/conservation?
- `Exec/AuthTurn.lean` — authorization checking (does the action's predicate discharge?).
- Proof that an accepted turn preserves the ledger invariants (`execFullTurn_conserves`, `execFullTurn_each_attests`).

**What dregg2 DOES NOT:**
- **Turn construction:** How does the SDK *build* a turn with witness proofs? CommittedTurnBuilder (in `sdk/src/committed_turn.rs`) compiles commitments and range proofs into NoteSpend/NoteCreate effects. Dregg2 does NOT model this.
- **Proof generation:** Bulletproof range proofs, Schnorr conservation proofs, STARK spending proofs — all generated on-device. NOT modeled in Lean.
- **Token attenuation:** Macaroon/Biscuit narrowing (in `token/src/traits.rs`). This is DISTINCT from caveat predicates (`Dregg2/Authority/Caveat.lean`) and NOT formalized.
- **Wallet semantics:** How the cipherclerk holds tokens, derives signing keys, manages nonces. NOT modeled.

**Why the gap:** The Lean model is a **specification of the protocol** (executor) not an **implementation model** (builder). The SDK is the implementation; verification assumes the SDK outputs valid turns.

---

### Is There ANY Economics (Fees/Gas/Staking/Demurrage)?

**Answer: PARTIALLY (gas yes, others no).**

**Gas Metering: ✅ PROVED**
- `Dregg2/Exec/Gas.lean:60-85` defines a per-action schedule:
  - `revoke := 1` (cheapest, pure subtraction)
  - `balance := 2` (transfer)
  - `delegate := 3` (capability grant)
  - `burn := 4` (destroy node supply)
  - `mint := 5` (create node supply, most expensive)
- All costs are nonzero (no free action) and pairwise distinct (schedule is real, not vacuous).
- `execGas` executor proves:
  - `gas_monotone` — remaining gas = budget − totalCost (consumed = Σ per-action costs).
  - `gas_exhaustion_fails_closed` — if totalCost > budget, turn fails to `none` (all-or-nothing).
  - `gas_sufficient_runs` — if budget ≥ totalCost AND turn is otherwise valid, metered result = unmetered `execFullTurn` (pure guard).
  - `gas_conserves` and `gas_preserves_attests` — gas adds no safety loss.
- **Discipline:** No `axiom`/`sorry`; pure, computable, `#eval`-able.

**Fee Market, Staking, Demurrage: ❌ NOT MODELED**
- **Fees:** The SDK/coord includes a `fee` field in turns (`coord/src/atomic.rs:50+`) but there is NO Lean model of fee collection, burning, or distribution. Gas schedule is a liveness bound; fee is not modeled.
- **Staking:** Slashing (in Dispute oracle) is informally designed (`PHASE-BRIDGE.md §5.3` pseudocode). No formal staking model (validator bonds, slash proofs, incentive alignment).
- **Demurrage:** ClockDAG spec mentions demurrage (SPEC §11, age-decay of balances). NOT formalized in dregg2; only ClockDAG's mutual-credit invariant is proved (ClockDAG/Model.lean).

---

## 3. THE REAL APP QUESTION (Magnesium Vision): Which dregg1 App is Closest to Verified End-to-End?

**Short Answer: NONE. The shipped apps (nameservice, identity, subscription, governed-namespace) are NOT verified. The only end-to-end verified app is ClockDAG, which is SEPARATE and NOT SHIPPED.**

### Shipped Apps vs. Verified Demonstrator

| App | Implementation | Dregg2 Model | Verified? | Status |
|---|---|---|---|---|
| **Nameservice** | `starbridge-apps/nameservice/src/lib.rs:1-100+` (register, renew, transfer) | **NO** | ❌ NO | Works in production; no Lean model. Field constraints are checked at runtime; no pre-conditions. |
| **Identity** | `starbridge-apps/identity/src/lib.rs` (credential issuance) | **NO** | ❌ NO | Token lifecycle tracked; no formal security model. |
| **Subscription** | `starbridge-apps/subscription/src/lib.rs` (pub/sub events) | **NO** | ❌ NO | Event streaming; state machine NOT modeled. |
| **Governed-namespace** | `starbridge-apps/governed-namespace/src/lib.rs` (voting) | **NO** | ❌ NO | Multi-signer coordination; no voting invariant proved. |
| **ClockDAG** | `simbi-inc/clockdag-protocol` (separate, production mutual-credit) | `metatheory/ClockDAG/Model.lean` | ✅ YES | Demonstrator: 4 safety invariants (conservation, no-double-spend, HTLC atomic, light-client sound) proved by reusing dregg2 theorems. **NOT a dregg app; separate project.** |

### Why No Shipped App is End-to-End Verified

1. **Cell programs are userspace policy.** The dregg kernel verifies authority + conservation + causality; the app defines constraints. No single app's logic (nameservice's rent expiry, identity's credential revocation, etc.) is axiomatized in the kernel.

2. **No cell-program model in dregg2.** `Exec/CellProgram.lean` is a stub:
   ```lean
   -- (pseudocode)
   structure CellProgram where
     name : String  -- just a label; no actual constraints
   ```
   Real nameservice field constraints (e.g., "EXPIRY_SLOT must monotone-increase by rent epoch") are checked at runtime, not in Lean.

3. **No app-specific turn builders.** The SDK builds turns with effects (SetField, EmitEvent, GrantCapability). Dregg2 verifies the executor accepts them; it does NOT verify the SDK's turn-builder logic (how to correctly populate fields to enforce nameservice uniqueness, etc.).

4. **Integration gap.** The pathway to end-to-end app verification would be:
   - Formalize the app's state-machine invariants (e.g., nameservice: per-name ownership unique, expiry ≥ registration height).
   - Bind the app's cell program to dregg's CellProgram type.
   - Prove the app's turn builders emit turns that preserve invariants.
   - This is **NOT DONE** for any shipped app.

### ClockDAG: Why It's NOT a dregg App

From `metatheory/ClockDAG/Model.lean`:1–14:

> ClockDAG (`simbi-inc/clockdag-protocol`, the "Simbi Mesh Credit Protocol") is a **SEPARATE project — not Dragon's Egg (dregg2).** Simbi is in production and is NOT scheduled to be ported onto dregg. This module is a *modeling exercise*: it shows that dregg2's already-proved primitives faithfully capture the core SAFETY invariants of a real shipped mutual-credit DAG ledger.

ClockDAG is a **peer network of mutual-credit agents**; dregg2 is a **federation of cells under a shared ledger**. They share NO deployed code; ClockDAG's verification is a proof of concept that dregg2's tools (Conservation, Blocklace, JointCell, Merkle, NonMembership) are reusable.

---

## 4. VERDICT: Coverage + Ranked Gaps

### Coverage Summary

| Component | Scope | Modeled? | Proved? | Severity |
|-----------|-------|----------|---------|----------|
| **Bridge — Comparison predicate** | Cross-chain threshold check | ✅ YES | ✅ YES (bridge_bridge) | ✓ (core proved) |
| **Bridge — Atomic swap** | Lock/mint nonce pairing | ⚠️ DESIGN DOC | ❌ NO | HIGH (atomicity unproved) |
| **Bridge — Dispute oracle** | Challenge window + slashing | ⚠️ DESIGN DOC | ❌ NO | HIGH (operational gap) |
| **Bridge — Relayer protocol** | Observe, attest, finalize | ⚠️ DESIGN DOC | ❌ NO | HIGH (liveness unproved) |
| **Shipped apps (4)** | Nameservice, identity, subscription, governed-namespace | ❌ NO | ❌ NO | HIGH (no model) |
| **SDK — Turn construction** | Proof generation, witness assembly | ❌ NO | ❌ NO | MEDIUM (impl-only) |
| **SDK — Token attenuation** | Macaroon/Biscuit narrowing | ❌ NO | ❌ NO | MEDIUM (DISTINCT from caveats) |
| **SDK — Wallet** | Token storage, key management | ❌ NO | ❌ NO | MEDIUM (impl-only) |
| **Economics — Gas metering** | Per-action cost, budget bound | ✅ YES | ✅ YES (execGas) | ✓ (proved) |
| **Economics — Fee market** | Dynamic pricing, auction | ❌ NO | ❌ NO | MEDIUM (not impl) |
| **Economics — Staking** | Validator bonds, slashing | ⚠️ DESIGN DOC | ❌ NO | HIGH (security-critical) |
| **Economics — Demurrage** | Age-decay of balances | ❌ NO | ❌ NO | LOW (ClockDAG-specific) |

### Ranked Gaps (What's Missing for Magnesium Vision)

**TIER 1 — CRITICAL (Blocks Verified End-to-End Bridge)**

1. **Bridge Atomic Swap Algebra** (HIGH EFFORT)
   - **Gap:** `BridgeAction` structure and `bridge_atomic_by_nonce` theorem in PHASE-BRIDGE.md §5.1 are pseudocode with `sorry`.
   - **Impact:** The bridge's soundness guarantee (Comparison predicate) is proved, but atomicity (the *reason* for cross-chain) is unproved.
   - **Path:** Formalize BridgeAction in `Dregg2/Bridge/BridgeAction.lean`; prove matched nonces prevent double-release; wire Dispute oracle assumption.
   - **Effort:** ~2–3 weeks (proof engineering + reusing Registry machinery).

2. **Dispute Oracle Model** (HIGH EFFORT)
   - **Gap:** Federation attestation + challenge window + slash-on-wrong logic is pseudocode only.
   - **Impact:** Relayer has no formal guarantee that foreign observations will be accepted or slashed consistently.
   - **Path:** Formalize DisputeOracle in `Dregg2/Bridge/DisputeOracle.lean` as a `Prop`-carrier (like Blocklace.signed); bind to relayer state machine.
   - **Effort:** ~2 weeks (oracle modeling + cascade with bridge verifier).

3. **Relayer State Machine** (MEDIUM EFFORT)
   - **Gap:** Relayer transitions (Idle → Observing → Finalizing) have no formal invariant.
   - **Impact:** No proof that relayer respects ordering (observe before finalize) or handles timeouts correctly.
   - **Path:** Formalize `Dregg2/Bridge/RelayerStateMachine.lean` with step-complete semantics.
   - **Effort:** ~1 week (state-machine model, safety property).

**TIER 2 — IMPORTANT (Blocks Verified Apps)**

4. **Cell Program Formalization** (HIGH EFFORT)
   - **Gap:** `Exec/CellProgram.lean` is a stub; nameservice field constraints (rent expiry, ownership unique) are NOT axiomatized.
   - **Impact:** Apps cannot be verified end-to-end because their invariants are not in the type.
   - **Path:** Extend CellProgram with `StateConstraint` + `FieldConstraint` types; prove turn builders preserve them.
   - **Effort:** ~4–6 weeks (per app, ~2–3 weeks per app after framework is in place).

5. **App-Specific Invariants (Nameservice Example)** (MEDIUM EFFORT)
   - **Gap:** No Lean model of "per-name ownership unique and monotone-increasing expiry."
   - **Impact:** Nameservice field constraints are enforced at runtime; no pre-condition proof.
   - **Path:** Define nameservice state invariant in Lean; prove turn builders (register, renew, transfer) preserve it.
   - **Effort:** ~2–3 weeks (invariant formalization + turn-builder proof for one app; can be templated for others).

**TIER 3 — NICE-TO-HAVE (Blocks Proof Completeness)**

6. **SDK Turn Construction Binding** (HIGH EFFORT)
   - **Gap:** Bulletproof range proofs + Schnorr conservation proofs are generated in Rust; not bound to Turn semantics.
   - **Impact:** No end-to-end proof that SDK-generated turns are valid (only post-hoc executor verification).
   - **Path:** Extract SDK proof generation as an FFI; bind to Turn.conservation_proof in `Dregg2/Exec/TurnExecutorFull.lean`.
   - **Effort:** ~4–6 weeks (FFI extraction + proof-generation algebra).

7. **Token Attenuation Formalization** (MEDIUM EFFORT)
   - **Gap:** Macaroon/Biscuit narrowing (in `token/src/traits.rs`) is distinct from caveat predicates; not modeled.
   - **Impact:** Token delegation (attenuate + delegate) has no formal narrowing invariant.
   - **Path:** Define TokenAttenuation algebra in `Dregg2/Authority/TokenAttenuation.lean`; prove narrow does not escalate capability.
   - **Effort:** ~2–3 weeks (algebra + reuse caveat machinery).

8. **Fee Market Model** (MEDIUM EFFORT)
   - **Gap:** Gas schedule exists; fee market (dynamic pricing, bidding, burning) does not.
   - **Impact:** No bound on transaction affordability or incentive alignment.
   - **Path:** Extend Gas.lean with FeeMarket algebra; prove fee burning = reward distribution conserves total.
   - **Effort:** ~2 weeks (fee model + conservation proof).

9. **Staking + Slashing Model** (HIGH EFFORT)
   - **Gap:** Validator bonds and slashing are design-doc only; no formal model.
   - **Impact:** No proof that slashing detects / punishes malfeasance.
   - **Path:** Formalize `Dregg2/Economics/Staking.lean` (bond deposit, slash condition, reward); bind to Dispute oracle.
   - **Effort:** ~4–6 weeks (game-theoretic algebra + incentive proof).

---

## 5. HONEST SCOPE: What IS Verified vs. What IS NOT

### Definitively PROVED (In Lean, Machine-Checked)

✅ **Bridge comparison predicate** — threshold ≤ v is proved sound via `RecordCircuit.range` (no primitive seam).  
✅ **Multi-asset conservation** — per-asset ledger balance is preserved by every committed transfer (Exec/MultiAsset.lean).  
✅ **Gas metering** — per-action schedule is enforced; turn fails closed if over-budget (Exec/Gas.lean).  
✅ **Merkle membership** — inclusion proof is sound against committed tree (Crypto/Merkle.lean).  
✅ **Non-membership** — exclusion proof is sound (Crypto/NonMembership.lean).  
✅ **ClockDAG safety invariants** — transfer conservation + no-double-spend + HTLC atomic + light-client sound (by reuse of dregg2 theorems).  

### Definitively NOT PROVED

❌ **Bridge atomicity** (lock/mint staying tied across chains) — proved only if Dispute oracle assumption holds; Dispute oracle itself is unmodeled.  
❌ **Nameservice field constraints** — rent expiry + ownership unique — NOT axiomatized in dregg2.  
❌ **Identity credential lifecycle** — NOT modeled.  
❌ **Subscription state machine** — NOT modeled.  
❌ **Governed-namespace voting** — NOT modeled.  
❌ **SDK turn construction** — witness proof generation and assembly NOT modeled.  
❌ **Token attenuation narrowing** — NOT modeled (distinct from caveats).  
❌ **Wallet semantics** — token storage + key management NOT modeled.  
❌ **Fee market** — dynamic pricing NOT modeled.  
❌ **Staking + slashing incentives** — NOT modeled.  
❌ **Foreign-chain consensus** — Cardano/Ethereum finality NOT modeled.  

### DESIGN DOCS (Written, Not Formalized)

⚠️ **PHASE-BRIDGE.md** — Bridge atomic swap, Dispute oracle, Relayer protocol, Light-client roadmap (all in Sections 5–7, with sorries or pseudocode).  
⚠️ **plans/midnight-bridge-production.md** — Production relayer architecture, federation attestation, bond slashing.  

---

## 6. OVERCREDITING RISK ASSESSMENT

**This audit is skeptical about coverage claims.** The failure mode is **overstating formalization** (e.g., "the bridge is verified" when only the comparison predicate is).

**High-Risk Claims (Watch for Overcrediting):**

1. **"Bridge Protocol is Verified"** → Reality: Comparison ✅, Atomicity ❌, Dispute ❌, Relayer ❌. **Claim:** "Bridge soundness is proved for the comparison predicate; atomic-swap and relayer semantics remain design-doc-only."

2. **"Apps Run on Verified dregg2"** → Reality: Apps have NO Lean model; kernel verifies executor only. **Claim:** "Dregg2 verifies the execution *layer*; app-specific invariants (per-app cell program constraints) are NOT verified."

3. **"SDK Integrates with Dregg2 Verification"** → Reality: SDK builds turns; Dregg2 accepts/rejects them. No cross-binding. **Claim:** "Dregg2 verifies the executor's acceptance predicate; SDK turn construction is NOT verified."

4. **"ClockDAG is a Dregg App"** → Reality: ClockDAG is SEPARATE, non-shipped, peer network. **Claim:** "ClockDAG is a standalone modeling exercise; it is NOT part of the dregg federation."

**Mitigation:** Always cite the specific theorem (e.g., `bridge_bridge`, `maExec_conserves_per_asset`, `gas_sufficient_runs`) and its `#assert_axioms` footprint when claiming verification.

---

## 7. FILES REFERENCED (Absolute Paths)

### dregg1 (Rust Implementation)

**Bridge Protocol:**
- `/Users/ember/dev/breadstuffs/bridge/src/lib.rs` (73 lines) — module re-exports
- `/Users/ember/dev/breadstuffs/bridge/src/present.rs` (3821 lines) — presentation proofs + verifier
- `/Users/ember/dev/breadstuffs/bridge/src/action_binding.rs` (261 lines) — AIR binding for bridge actions

**Shipped Applications:**
- `/Users/ember/dev/breadstuffs/starbridge-apps/nameservice/src/lib.rs` (1000+) — register/renew/transfer
- `/Users/ember/dev/breadstuffs/starbridge-apps/identity/src/lib.rs` — credential lifecycle
- `/Users/ember/dev/breadstuffs/starbridge-apps/subscription/src/lib.rs` — pub/sub events
- `/Users/ember/dev/breadstuffs/starbridge-apps/governed-namespace/src/lib.rs` — governance voting

**SDK:**
- `/Users/ember/dev/breadstuffs/sdk/src/lib.rs` (232 lines) — module structure
- `/Users/ember/dev/breadstuffs/sdk/src/cipherclerk.rs` (900+) — token wallet, signing
- `/Users/ember/dev/breadstuffs/sdk/src/committed_turn.rs` (1000+) — turn builder with proofs
- `/Users/ember/dev/breadstuffs/sdk/src/verify.rs` (935 lines) — proof verification

**Token / Economics:**
- `/Users/ember/dev/breadstuffs/token/src/lib.rs` (80 lines) — module structure
- `/Users/ember/dev/breadstuffs/token/src/traits.rs` (250+) — AuthToken, Attenuation
- `/Users/ember/dev/breadstuffs/token/src/macaroon_backend.rs` — HMAC verify
- `/Users/ember/dev/breadstuffs/token/src/biscuit_backend.rs` — Datalog + Ed25519
- `/Users/ember/dev/breadstuffs/coord/src/atomic.rs` — fee field in turns (50+)

### dregg2 (Lean Metatheory)

**Bridge:**
- `/Users/ember/dev/breadstuffs/metatheory/Dregg2/Crypto/Bridge.lean` (468 lines) — fully proved comparison + opening
- `/Users/ember/dev/breadstuffs/docs/rebuild/PHASE-BRIDGE.md` — design doc: atomic swap, dispute oracle, relayer protocol

**Multi-Asset & Economics:**
- `/Users/ember/dev/breadstuffs/metatheory/Dregg2/Exec/MultiAsset.lean` (150 lines) — per-asset conservation
- `/Users/ember/dev/breadstuffs/metatheory/Dregg2/Exec/Gas.lean` (300+) — gas metering (proved)

**Apps & Cell Programs:**
- `/Users/ember/dev/breadstuffs/metatheory/Dregg2/Exec/CellProgram.lean` — stub

**Authorization:**
- `/Users/ember/dev/breadstuffs/metatheory/Dregg2/Authority/Caveat.lean` — caveat predicates (NOT token attenuation)
- `/Users/ember/dev/breadstuffs/metatheory/Dregg2/Authority/Predicate.lean` — predicate verifier interface

**ClockDAG (Separate, Non-Shipped):**
- `/Users/ember/dev/breadstuffs/metatheory/ClockDAG/Model.lean` (200+) — mutual-credit DAG safety invariants

---

## 8. FINAL RECOMMENDATION

**For Magnesium Vision ("Real App on Verified dregg2"):**

1. **Bridge Atomic Swap (MUST HAVE):** Formalize BridgeAction algebra + Dispute oracle. Without this, cross-chain transactions have no formal atomicity proof. **Effort:** ~4 weeks.

2. **Cell Program Framework (MUST HAVE):** Extend `Exec/CellProgram.lean` to carry state invariants. This is the prerequisite for ANY app verification. **Effort:** ~2 weeks (framework); ~2–3 weeks per app.

3. **Nameservice as Pilot App (SHOULD HAVE):** Pick the simplest shipped app (nameservice: register, renew, transfer) and prove its state machine preserves per-name ownership + monotone-increasing expiry. **Effort:** ~3 weeks (after framework is in place).

4. **SDK Turn Construction (NICE-TO-HAVE):** Extract proof generation and bind to Turn semantics. Blocks full end-to-end SDK verification but not critical for app-level correctness. **Effort:** ~4–6 weeks.

**Sequential Path (Effort: ~15–20 weeks):**
- Week 1–2: Formalize CellProgram framework.
- Week 3–4: BridgeAction + Dispute oracle.
- Week 5–7: Nameservice state invariant + turn-builder proof.
- Week 8–15: Identity, subscription, governed-namespace (in parallel or sequence).
- Week 16–20: SDK turn construction (parallel with apps if capacity allows).

**Honest Scope:** Dregg2 is a **verified executor** — it guarantees that accepted turns preserve conservation + authority + causality. Apps will run on it correctly *as long as they emit valid turns*. The missing piece is **app-specific correctness** — proving the app's turn-builders emit those valid turns. That's where the next layer of formalization lives.

---

> End of COVERAGE-APPS.md. This is a READ-ONLY analysis. No code was modified.
