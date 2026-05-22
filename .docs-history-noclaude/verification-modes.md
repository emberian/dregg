# Verification Modes

Pyana uses a progressive disclosure model for authorization verification. The same
token chain and Datalog semantics underpin all three modes; what changes is how much
the verifier learns and what cryptographic assurance backs the result.

## Overview

| Mode | Latency | Proof size | Verifier learns | Trust assumption |
|------|---------|-----------|-----------------|------------------|
| Trusted | ~8 us | 0 (no proof) | Everything | Verifier holds root key |
| Selective Disclosure | ~200 ms | ~45 KB | Chosen facts + conclusion | STARK soundness |
| Fully Private | ~500 ms | ~80 KB | One bit (allow/deny) | STARK soundness |

---

## Mode 1: Trusted

**When to use:** Cloud API verification, internal microservices, fly.io-style auth,
multiplayer IDE silos -- anywhere the verifier already possesses the root secret key
and can run Datalog locally.

### What happens

1. Token is decoded and its caveats are compiled to a FactSet.
2. The Datalog evaluator runs the full policy against the authorization request.
3. The result includes the `TokenClearance` (capabilities, expiry, subject) and
   the full `AuthorizationTrace` (every rule that fired, every derivation step).

### API

```rust
use pyana_sdk::{AgentWallet, VerificationMode, AuthorizationPresentation};

let presentation = wallet.authorize(&token, &request, VerificationMode::Trusted)?;

// The caller receives everything:
match presentation {
    AuthorizationPresentation::Trusted { clearance, trace } => {
        println!("Authorized: {:?}", clearance.capabilities);
        println!("Policy matched: {:?}", clearance.matched_policy);
        println!("Derivation steps: {}", trace.steps.len());
    }
    _ => unreachable!(),
}
```

### Verifier receives

- `TokenClearance`: matched policy, capabilities, format, expiry, subject
- `AuthorizationTrace`: full derivation (rules fired, substitutions, derived facts)

### Verifier learns

Everything: the token contents, which rules fired, intermediate derived facts,
the evaluation order, timing characteristics.

### Performance

- ~8 microseconds for typical tokens (5-15 caveats)
- No proof generation overhead
- No network round-trip if verifier is co-located

### Trust assumptions

- The verifier holds the root symmetric key (or the issuer's signing key)
- The verifier's Datalog evaluator is correct
- No third-party verification possible without sharing the key

---

## Mode 2: Selective Disclosure

**When to use:** Cross-organization capability presentation, audit scenarios where
the verifier needs to see *some* facts (e.g., which service is authorized, what
actions are permitted) but should not learn everything (e.g., the full caveat chain,
internal delegation structure, or user identity).

### What happens

1. Token is decoded and Datalog evaluation runs locally (same as Trusted mode).
2. The prover selects which facts from the evaluation trace to reveal.
3. A STARK proof is generated over the full derivation, with revealed facts as
   public inputs and hidden facts remaining private witness.
4. The verifier sees: the conclusion, the chosen revealed facts, and the proof.

### API

```rust
use pyana_sdk::{AgentWallet, VerificationMode, AuthorizationPresentation, FactIndex};

// Reveal facts at indices 0 and 2 from the evaluated fact set
let presentation = wallet.authorize(
    &token,
    &request,
    VerificationMode::SelectiveDisclosure {
        reveal: vec![FactIndex(0), FactIndex(2)],
    },
)?;

match presentation {
    AuthorizationPresentation::Selective { revealed_facts, proof, conclusion } => {
        assert!(conclusion); // authorized
        println!("Revealed: {:?}", revealed_facts);
        println!("Proof size: {} bytes", proof.len());
    }
    _ => unreachable!(),
}
```

### Verifier receives

- `conclusion: bool` -- whether the authorization succeeded
- `revealed_facts: Vec<Fact>` -- the subset of facts the prover chose to disclose
- `proof: Vec<u8>` -- STARK proof that the full evaluation (including hidden facts)
  derives the stated conclusion

### Verifier learns

- Whether the request is authorized
- The specific facts that were explicitly revealed
- Nothing about unrevealed facts, the chain length, or which rules fired for
  unrevealed derivations

### Performance

- ~200 ms proof generation (dominated by multi-step AIR witness construction)
- ~45 KB proof size (depends on number of derivation steps)
- ~5 ms verification

### Trust assumptions

- STARK soundness (computational: no efficient adversary can forge a proof)
- The revealed facts are correct (they are public inputs to the proof)
- The verifier trusts the federation root (the issuer is a registered member)

---

## Mode 3: Fully Private

**When to use:** Anonymous credential presentation, private DEX authorization,
scenarios where the verifier should learn absolutely nothing beyond "yes" or "no."

### What happens

1. Token is decoded and Datalog evaluation runs locally.
2. The full multi-step derivation trace is encoded as a `MultiStepDerivationAir` witness.
3. A STARK proof is generated with only the conclusion (allow/deny) as public output.
4. The verifier learns exactly one bit: authorized or not.

### API

```rust
use pyana_sdk::{AgentWallet, VerificationMode, AuthorizationPresentation};

let presentation = wallet.authorize(&token, &request, VerificationMode::FullyPrivate)?;

match presentation {
    AuthorizationPresentation::Private { proof, conclusion } => {
        assert!(conclusion);
        println!("Proof size: {} bytes", proof.len());
        // Verifier learns nothing else
    }
    _ => unreachable!(),
}
```

### Verifier receives

- `conclusion: bool` -- the single-bit authorization result
- `proof: Vec<u8>` -- STARK proof over the full MultiStepDerivationAir

### Verifier learns

- One bit: authorized or denied
- Nothing about: token contents, chain length, intermediate facts, which rules
  fired, the number of derivation steps, the service name, the capabilities

### Performance

- ~500 ms proof generation (full multi-step AIR with up to 8 derivation steps)
- ~80 KB proof size (larger due to full derivation encoding)
- ~10 ms verification

### Trust assumptions

- STARK soundness (computational)
- The verifier trusts the federation root
- Zero knowledge: the proof reveals nothing beyond the conclusion

---

## Mode Selection Guide

```text
Do you hold the root key?
  YES --> Mode 1 (Trusted)
  NO  --> Does the verifier need to see specific facts?
            YES --> Mode 2 (Selective Disclosure)
            NO  --> Mode 3 (Fully Private)
```

### Decision factors

| Factor | Trusted | Selective | Private |
|--------|---------|-----------|---------|
| Latency budget | <1ms | <500ms | <1s |
| Verifier has root key | Required | Not needed | Not needed |
| Audit trail needed | Full trace | Partial | None |
| Cross-org boundary | No | Yes | Yes |
| Anonymity required | No | Partial | Full |

---

## Implementation Details

### Underlying functions per mode

| Mode | Entry point | Circuit |
|------|-------------|---------|
| Trusted | `pyana_token::datalog_verify::verify_token_datalog()` | None |
| Selective | `BridgePresentationBuilder::prove()` with partial public inputs | `MultiStepDerivationAir` |
| Private | `BridgePresentationBuilder::prove()` with conclusion-only public inputs | `MultiStepDerivationAir` |

### Wire protocol encoding

All three modes produce an `AuthorizationPresentation` enum that serializes via
postcard for the wire protocol. The verifier dispatches on the variant tag:

- `0x01` -- Trusted (clearance + trace, no proof)
- `0x02` -- Selective (revealed facts + proof + conclusion)
- `0x03` -- Private (proof + conclusion only)
