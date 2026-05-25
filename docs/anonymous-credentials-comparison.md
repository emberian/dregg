# Anonymous Credentials: Pyana vs. Existing Systems

## Pyana's Approach

Pyana is not an anonymous credential system that bolted on capabilities. It is a capability system that naturally produces anonymous credentials as a consequence of its attenuation model.

A credential in pyana is an attenuated capability chain — a sequence of monotone narrowing steps starting from a federated issuer. Presentation proves "I hold a valid chain whose final state authorizes action X" via STARK, revealing only the federation root, a blinded presentation tag, and optionally selected facts. The chain itself, the issuer identity within the federation, and all intermediate capabilities remain private.

Key primitives: Poseidon2 Merkle membership (issuer in federation), fold AIR (each attenuation step only narrows), derivation AIR (Datalog evaluation proving authorization from final state), ring membership via blinding factor (issuer unlinkability), and fresh presentation randomness (multi-show unlinkability).

## Comparison Matrix

### Idemix (IBM) — CL Signatures

Idemix provides multi-show unlinkable credentials with selective attribute disclosure via Camenisch-Lysyanskaya signatures on committed attribute vectors.

**Feature parity:** Both achieve multi-show unlinkability and selective disclosure. Idemix supports predicate proofs over attributes (e.g., age >= 18). Pyana supports arbitrary predicate proofs via arithmetic/relational AIRs and temporal predicates ("attribute X >= Y for N blocks").

**Pyana advantages:** Post-quantum security (STARKs have no pairing/DL assumptions). More expressive predicates — Datalog evaluation means pyana can prove policy conclusions, not just attribute comparisons. Private policy evaluation: the verifier need not know the policy rules, only the conclusion. Capability attenuation gives composable delegation that Idemix lacks entirely.

**Pyana disadvantages:** Proof size (~24 KiB STARK vs. ~1 KiB CL signature proof). Proving time (STARK generation is orders of magnitude slower than CL proofs). No standardization. Idemix has decades of academic analysis and real deployments.

### U-Prove (Microsoft) — Blind Signatures

U-Prove tokens are one-show unlinkable: each token presentation is linkable to itself but unlinkable across shows. Multi-show requires multiple issued tokens.

**Feature parity:** Both provide selective disclosure. U-Prove has simpler issuance (blind RSA signatures).

**Pyana advantages:** Multi-show unlinkability from a single credential (via fresh presentation randomness + blinded tag). No need to pre-issue N tokens for N shows. Delegation — U-Prove has no native mechanism for passing restricted sub-credentials to third parties; pyana's attenuation chain handles this natively. Post-quantum.

**Pyana disadvantages:** Proof size and proving time. U-Prove tokens are tiny (~200 bytes) and verification is one RSA check. U-Prove has a simpler trust model (single issuer, no federation).

### BBS+ Signatures (W3C VC Data Integrity)

BBS+ is now the W3C standard for anonymous credential selective disclosure. Pairing-based, efficient multi-show unlinkability, efficient selective disclosure of individual signed messages from a multi-message signature.

**Feature parity:** Both achieve multi-show unlinkability and per-attribute selective disclosure. BBS+ has efficient batch issuance.

**Pyana advantages:** Post-quantum (BBS+ is broken by quantum computers due to pairing dependence). Predicate proofs beyond equality — BBS+ discloses attributes or hides them; proving "attribute > X" requires layering ZK range proofs on top. Pyana's circuit does this natively. Capability delegation — BBS+ credentials are static signed claims with no native sub-credential or attenuation mechanism. Private Datalog evaluation gives pyana policy-level proofs (not just attribute-level).

**Pyana disadvantages:** Proof size (BBS+ proofs are ~500 bytes; pyana STARKs are ~24 KiB). Verification time (BBS+ is milliseconds; STARK verification is tens of milliseconds). Ecosystem maturity — BBS+ has W3C backing, multiple implementations, VC ecosystem integration.

### Midnight (Cardano) — ZK Smart Contracts

Midnight uses ZK proofs (Plonk-family) for private smart contracts with shielded state. Users prove predicates about their state without revealing it.

**Feature parity:** Both use ZK to prove authorization over private state. Both support selective disclosure of specific values from a private state.

**Pyana advantages:** Capability-native — Midnight's model is smart-contract-state-centric (prove things about your private contract state), while pyana's model is delegation-centric (prove you hold sufficient authority through a chain). Pyana's fold chain gives provable monotone narrowing without on-chain state. Federation-scoped revocation without global state. Offline verification — pyana proofs are self-contained; Midnight requires chain access for state roots.

**Pyana disadvantages:** No smart contract expressiveness (Midnight can prove arbitrary computations over private state). Midnight has Cardano ecosystem backing and funding.

### Hyperledger AnonCreds — SSI Standard

AnonCreds (evolved from Idemix) is the deployed standard in Aries/Indy SSI ecosystems. CL-signature-based, with link-secret binding, schema/credential-definition separation, and revocation via accumulators.

**Feature parity:** Both achieve unlinkable presentations, selective disclosure, and revocation. AnonCreds uses cryptographic accumulators for revocation; pyana uses non-membership proofs against a sorted revocation tree (NonRevocationAir).

**Pyana advantages:** Post-quantum. No credential schema rigidity — AnonCreds requires pre-defined schemas with fixed attribute slots; pyana's fact-based model is schema-free. Delegation (AnonCreds has no sub-credential mechanism). Private policy evaluation (AnonCreds verifiers must specify exactly which attributes they need; pyana verifiers just check the conclusion).

**Pyana disadvantages:** No ecosystem (AnonCreds has Aries, cipherclerks, production government deployments). No interoperability standards. Proof size and verification time.

### IRMA/Yivi — Production Attribute Credentials (Netherlands)

IRMA uses Idemix internally, deployed for Dutch government services. Flow-based: user selects which attributes to disclose per interaction.

**Feature parity:** Both achieve selective disclosure and unlinkability. IRMA has real user-facing cclerk UX.

**Pyana advantages:** Delegation (IRMA credentials cannot be sub-attenuated and passed to agents). Post-quantum. Composable policy evaluation rather than per-attribute disclosure selection.

**Pyana disadvantages:** No cclerk. No government adoption. No user-facing UX story. IRMA is in production with millions of users.

## What Is Unique to Pyana

1. **Capability attenuation as the credential primitive.** Other AC systems issue credentials as signed attribute bundles. Pyana's credentials ARE attenuated capability chains — the structure that proves authorization simultaneously embodies the delegation history and the principle of least privilege. This is not bolted on; the fold AIR IS the credential issuance mechanism.

2. **Private Datalog evaluation.** No other AC system proves policy conclusions in zero knowledge. Idemix/BBS+ prove attribute predicates. Pyana proves "these Datalog rules, evaluated over this (private) fact set, concluded ALLOW." The verifier need not know the rules.

3. **Federation-scoped trust and revocation.** The trust anchor is not a single issuer but a federation Merkle root. Ring membership (blinded leaf) hides WHICH federation member issued the credential. Revocation is federation-local (sorted-tree non-membership proof), not global.

4. **Temporal predicates.** Prove "attribute X satisfied predicate P for N consecutive blocks" without revealing the attribute values or the specific blocks. No other AC system has this.

## Is It Bolted On?

No. The anonymous credential properties emerge structurally from the capability model:

- **Unlinkability** comes from the blinding factor on issuer membership + fresh presentation randomness — both are natural consequences of hiding the capability chain (which is the entire point of the fold AIR).
- **Selective disclosure** comes from the Poseidon2 commitment over revealed facts — a direct consequence of the Merkle-committed fact set that the fold chain operates on.
- **Attenuation** IS the issuance mechanism. There is no separate "issue credential" step; delegating a restricted capability IS issuing a sub-credential.
- **Revocation** reuses the federation's state consensus — the same infrastructure that orders state transitions also maintains the revocation accumulator.

The capability model does not merely support anonymous credentials — it IS an anonymous credential system whose internal structure happens to be a capability chain rather than a signed attribute vector.
