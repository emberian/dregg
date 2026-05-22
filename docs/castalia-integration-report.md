# Castalia/Zenith Integration Analysis for Pyana

## 1. What Castalia/Zenith Actually Needs from Pyana

Castalia does not need pyana's full runtime. It needs three specific things at the integration seam:

**A verifier boundary (secS)**: A function that accepts a presentation request containing `{subject_id, state_id, hub_id, requested_action, requested_resource, policy_context, credential_or_capability, proof_or_signature_material, freshness_context}` and returns `allow | deny | stale | needs_review`. The MVP version checks signed JSON credentials and Hub policy tables. Pyana's verification modes (trusted/selective/private) slot into this same interface later without changing the contract.

**A policy vocabulary (secZ)**: Datalog facts that name Castalia's governance concerns:
```
subject(subject_id)
state(state_id)
hub(hub_id)
member(subject_id, state_id)
role(subject_id, state_id, reviewer)
registry_recognizes(registry_id, state_id)
can_submit_rfc(subject_id, state_id, rfc_id)
can_review(subject_id, state_id, artifact_id)
can_ratify_bucket(subject_id, state_id, bucket_id)
can_dispatch_agent(subject_id, hub_id, work_order_id)
```
Pyana's `pyana-trace` Datalog evaluator can express these directly. Zenith defines the vocabulary; pyana proves predicates over it.

**Attenuated task capabilities for agents/work-orders**: When Hub dispatches a work order, the agent receives a scoped, time-limited, budget-bounded capability token rather than ambient credentials. Pyana's `AuthToken` (macaroon + Biscuit hybrid with caveats) and `tokenizer` (sealed secret proxy) map directly. The agent returns a proof-carrying receipt chain as its audit trail.

What Castalia does NOT need from pyana: federation consensus, cell execution, note trees, the intent marketplace, the browser extension, or the economic model. These are pyana-internal infrastructure. Castalia integrates at the capability/proof/verification surface, not the runtime surface.


## 2. What Gabriel's Off-Chain Transfer Paper Adds

Gabriel's paper describes a privacy-preserving ownership transfer protocol where:

- Each object has an on-chain `objContract` with only three fields: `creator` (public key), `state` (dynamic public key representing current owner), and `counter` (strictly increasing timestamp).
- Actual object data never touches the chain -- it travels encrypted between wallets off-chain.
- Transfers rotate the `state` key on-chain (proving ownership changed) while the object payload moves privately between clients.
- The `counter` provides a monotonic ordering guarantee equivalent to a blockchain without broadcasting ownership.

**The primitive pyana should adopt**: The `objContract.counter` pattern -- a minimal on-chain anchor that provides ordering and non-repudiation without revealing who owns what. This maps to pyana's existing machinery in two ways:

1. **Nullifier sets** already serve the same purpose for note spending (prove something happened without revealing what).
2. **Federation state roots** already commit to ordering without revealing content.

The specific adoption: pyana's macaroon nonces and revocation roots could optionally be anchored to an on-chain counter contract in Gabriel's style. The counter proves "this capability was exercised at time T" or "this revocation happened before time T" without revealing the capability holder or the revocation target. This is precisely what the `PyanaVault` and `PyanaCredentialGate` contracts in `docs/base-integration.md` already scaffold -- Gabriel's paper provides the theoretical foundation for why that design is sound.

**What pyana should NOT adopt from the paper**: The paper's key rotation transfer model (where `state` rotates to a new key pair on every transfer). Pyana capabilities attenuate -- they narrow but don't rotate identity. The transfer model is relevant for NFT-like objects (Castalia's soulbound credentials), not for capabilities.


## 3. The Soulbound Credential Question

This is the central design tension. Castalia's soulbound credentials are explicitly non-transferable. Pyana's entire design is built on attenuation-only delegation (capabilities narrow as they move through the system). These are not contradictions; they are two different objects serving two different roles.

**The reconciliation**:

| Concept | What it is | Pyana model | Transfer behavior |
|---------|-----------|-------------|-------------------|
| Soulbound credential | Standing/membership proof: "S is a reviewer in community C" | Credential fact in Datalog: `role(S, C, reviewer)` | NEVER transfers. Bound to `subject_id`. |
| Attenuated capability | Action authority: "S may review artifact A until time T" | `AuthToken` with caveats: `action=review, resource=A, expiry=T` | Attenuates only. Can be delegated with narrowing. |

The rule from the integration brief is explicit: **membership/standing credentials should remain non-transferable claims bound to a subject. Pyana capabilities can be delegated FROM that standing for specific tasks, times, resources, and budgets.**

In implementation:

1. A `SoulBoundCredential` (Castalia's `soul_bound_credentials` table, status: active/revoked/expired/suspended) is checked as a **predicate fact** in pyana's Datalog, not stored as a token. It is a signed JSON credential (off-chain fallback) or a Midnight credential (target). Pyana's `prove_predicate_unlinkable()` can prove predicates over it without revealing it.

2. An attenuated capability is minted by Hub when the soulbound holder needs to act. The capability references the credential but is not the credential. It expires, it can be further narrowed, and it produces receipts.

3. Pyana's non-revocation proofs (`prove_not_revoked`, `prove_not_revoked_accumulator`) map to Castalia's credential status transitions. When a credential is revoked, its revocation hash enters the revocation set. Future capability presentations fail the non-revocation check.

**What must NOT happen**: collapsing `member(S, C)` into a transferable Pyana token. The moment standing becomes a bearer token, you get a secondary market in community standing. The integration brief explicitly warns against this.


## 4. The Immediate Demo That Would Be Most Useful

The smallest convergence artifact from the integration brief:

```
subject S is a reviewer in state/community C
S receives attenuated capability to review artifact A until time T
S presents proof to secS
secS returns allow
Hub records review action with attached proof/receipt handle
```

**Concrete implementation using existing pyana surfaces**:

1. **secZ definition** (Datalog facts, lives in Hub config):
   ```
   role(S, C, reviewer).
   can_review(S, C, A) :- role(S, C, reviewer), artifact_community(A, C).
   ```

2. **Capability minting** (Hub creates a pyana `AuthToken`):
   - Root: Hub's signing key
   - Caveats: `action = "review"`, `resource = artifact_id`, `expiry = T`, `budget = 1`

3. **Presentation** (pyana SDK, running in the reviewer's client):
   - Trusted mode for same-Hub (8 microsecond verification, cleartext token + Datalog trace)
   - Selective mode for cross-community (STARK proof of role predicate, ~200ms)

4. **Verification** (secS, initially just a Hub endpoint):
   - Checks token signature chain
   - Evaluates Datalog policy
   - Returns `allow` + metadata for audit

5. **Receipt** (Hub records `AuditEvent` with `authorization_method: "offchain_signed"` and the receipt handle)

This demo requires:
- The `pyana-token` crate (works, tests pass)
- The `pyana-trace` crate (works, tests pass)
- A thin secS HTTP endpoint in Hub (new, ~100 lines)
- A secZ policy file (new, ~20 lines of Datalog)

It does NOT require: federation, STARK proofs, the browser extension, note trees, or the EVM bridge. Those are upgrades to the same interface.


## 5. What Pyana Should NOT Do

The integration brief is explicit about these boundaries:

1. **Do not collapse community standing into capabilities.** Roles like `member`, `reviewer`, `steward`, `contributor`, `agent`, `bucket_ratifier`, `repo_writer` should not be flattened into one token. They must remain credential facts plus attenuated task capabilities derived from them.

2. **Do not make Pyana federation membership identical to Castalia state/community membership.** A Castalia state may use one or more Pyana federations, and a Pyana federation may host many Castalia states. These are not the same concept. Do not map `state_id` directly to a pyana federation ID.

3. **Do not assume Matrix disappears.** Pyana's intent/MCP/3PI surfaces do not replace community conversation and social trust. Matrix stays as the social coordination layer.

4. **Do not assume Base/EVM becomes canonical identity.** Pyana's EVM bridge is useful for public verification/settlement, not necessarily identity root. Treat Base as a proving/settlement demo path.

5. **Do not make Hub state proof-only yet.** Hub still needs readable database/case/review/artifact state. Pyana proofs attach to Hub records before replacing any persistence model.

6. **Do not assume production readiness.** Local workspace tests are blocked by missing `plonky3-recursion` sibling. Several docs describe key components as in-progress. Zenith should not build a production trust boundary on unverified claims yet.

7. **Do not assume a single unified proof path is settled.** Recursive heterogeneous composition, encrypted turns in production consensus, and SP1/EVM deployment are not yet fully operational.


## 6. The secC/secS/secZ Mapping

The integration brief provides a clean three-layer mapping to pyana's current architecture:

### secC = client/prover/wallet side

**Pyana surface**: Browser extension (`window.pyana`), SDK (`AgentWallet`, `AgentRuntime`, `SiloClient`), HD wallet, proof generation, capability holding.

**What it does for Castalia**: Holds credentials (soulbound reference) and capabilities (attenuated tokens). Chooses verification mode (trusted/selective/private). Generates presentations and proofs. Seals/unseals private data via tokenizer. Can authorize actions requested by a Hub portal or web page.

**Current SDK APIs that map**:
- `AgentWallet::authorize_anonymously()` -- anonymous credential presentation
- `AgentWallet::prove_predicate_unlinkable()` -- prove role/standing without revealing identity
- `AgentWallet::prove_not_revoked()` -- prove credential is still active
- `AgentWallet::create_private_note()` / `transfer_note_privately()` -- private value (future treasury)

### secS = local verifier/resource gatekeeper

**Pyana surface**: Node verification layer (`pyana-node` HTTP API), wire verification (`pyana-wire` STARK verification on receive), MCP/HTTP authorization checks.

**What it does for Castalia**: The Hub endpoint that checks presented credentials/capabilities/proofs against policy before allowing actions. Returns `allow | deny | stale | needs_review`. Records `AuditEvent`. Guards secrets, resources, repo access, RFC promotion, and agent dispatch.

**Architecture**: Initially a Hub API endpoint (thin wrapper). Later may become the `secS-daemon` at `/Users/bananawalnut/repos/secS-daemon` (Rust daemon, port 9000) for hub-to-hub and agent-to-hub intent verification.

### secZ = Zenith policy profile over the generic substrate

**Pyana surface**: Datalog evaluator (`pyana-trace`), predicate proofs (`pyana-circuit`), Castalia-specific fact schemas (new, to be defined by Zenith).

**What it does for Castalia**: Names the governance semantics as policy facts. Defines role schemas (`CommunityRole`), community capabilities (`CommunityCapability`), RFC/bucket/repo action policies. This is where Castalia says "what reviewer means" and pyana proves "this subject satisfies the reviewer predicate."

**Relationship**: secZ is authored by Zenith/Castalia community governance. It uses pyana as the engine but is not defined by pyana. Pyana is the substrate; secZ is the policy profile painted on top.


## 7. Gabriel's "On-Chain Nonce" Question: Should Pyana's Macaroon Nonces Be On-Chain?

Gabriel's paper uses an on-chain atomic counter (`objContract.counter`) that provides three properties:
1. Strict ordering (timestamps are monotonically increasing)
2. Non-repudiation (the counter update is immutable once committed)
3. Privacy (the counter reveals THAT something changed, not WHAT or WHO)

**Should pyana's macaroon nonces be on-chain?**

Not by default, but optionally for specific use cases. Here is the analysis:

**What on-chain nonces would enable**:
- **Public audit of capability exercise frequency** without revealing holders. An on-chain counter per resource shows "this artifact was reviewed 3 times" without revealing which reviewers.
- **Cross-federation non-repudiation**. If community A dispatches work to community B's agent, an on-chain nonce proves the work was acknowledged at time T, even if B's federation goes offline.
- **Credential status anchoring**. A revocation nonce anchored on-chain provides a global ordering of "credential X was revoked before time T" that any light client can verify without trusting any single federation.
- **Double-exercise prevention** for one-shot capabilities. If a capability says "may review artifact A exactly once," an on-chain nullifier (derived from the capability + action) prevents re-exercise even across federation restarts.

**What on-chain nonces would NOT be appropriate for**:
- Routine API calls (gas cost, latency).
- Internal federation operations (federation consensus already provides ordering).
- Same-hub operations (Hub's database provides ordering locally).

**Recommended design**: Pyana macaroon nonces remain off-chain by default. The `chain/` workspace (SP1/EVM settlement, `PyanaVault`, `PyanaCredentialGate`) provides an optional on-chain anchoring path for high-value or cross-trust-domain operations. The nonce goes on-chain only when the action crosses a trust boundary that neither party's local federation covers -- precisely Gabriel's original use case of "transfers between wallets that don't share a trusted third party."

This maps to the Base integration scaffolding already in pyana:
- `PyanaVault.withdraw()` uses an on-chain nullifier for double-spend prevention
- `PyanaCredentialGate.verifyCredential()` uses an on-chain presentation nullifier for sybil resistance
- Both use SP1-wrapped STARK proofs so the on-chain contract sees only ~260 bytes of Groth16 proof

For Castalia specifically: treasury actions (stablecoin distributions via future-revenue contracts) would use on-chain nonces. RFC promotion, review submission, and repo access would not.


---

## Summary of Recommended Next Steps

1. Define the secZ fact vocabulary (Datalog, ~20 predicates for community/RFC/bucket/work-order/repo authority).
2. Define the secS request/response schema (`presentation_request` -> `allow | deny | stale | needs_review`).
3. Map each secZ fact to current Hub fields or signed JSON credentials.
4. Build the one end-to-end demo: "reviewer presents attenuated capability, secS verifies against Datalog policy, Hub records action with receipt."
5. Do NOT start with full federation, anonymous credentials, or on-chain settlement. Those are upgrades to the same interface.

The integration is narrow: a verifier boundary, a policy vocabulary, and attenuated capability dispatch. Everything else is optional infrastructure that plugs into these three slots later.
