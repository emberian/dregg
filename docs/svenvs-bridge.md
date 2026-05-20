# svenvs-pyana Bridge: Formally Verified Distributed Capability Expansion

The architecture for combining formally verified safety envelopes (svenvs) with
distributed object-capability authorization (pyana) into a system where agents
expand authority through machine-checked proof, operate across trust boundaries,
and stand independently.

---

## 1. The Conceptual Bridge

svenvs and pyana address complementary halves of the autonomy problem. svenvs
proves the GATE works — no matter what the agent does, it cannot escape its
safety bounds. pyana provides the NETWORK — capabilities travel, verify without
callbacks, and compose across federation boundaries. Together: a formally
verified distributed capability system.

### Concept Mapping

| svenvs | pyana | Relationship |
|--------|-------|-------------|
| Policy envelope (`sound_policy step safe pol`) | `CapabilitySet` + `Permissions` | The envelope constrains which actions are permitted; pyana's capability set is the concrete realization of what an agent holds authority over. The policy *is* the boundary of the c-list. |
| Proof-carrying upgrade (`admissible step safe oldp newp`) | Capability amplification (not yet implemented — pyana only supports attenuation via `is_narrower_or_equal`) | svenvs proves that expansion-under-proof is safe. pyana's `attenuate()` is the narrowing direction; svenvs provides the formal basis for going the other way. |
| Testimony channel (`embodied_admit attested step safe oldp newp w`) | ZK proof presentation (`Authorization::Proof(bytes)`) | The agent volunteers a proof about its own internals to earn authority. pyana's ZK authorization mode is the wire format; svenvs' embodiment theory is the formal guarantee that this is sound. |
| Genealogy of judges (`genealogy_sound`) | Federation consensus chain (`AttestedRoot` succession) | A sound genesis judge + forward-certified succession = every judge in the line is sound. A federation's attested root chain is exactly this: each height's quorum vouches for the next state. |
| Spec negotiation under meta-invariant (`spec_refines newspec meta_safe`) | Governance under federation bedrock | The meta-invariant is the eternal bedrock (amendmentScript). In pyana: the federation's founding principles that survive even meta-amendments to consensus rules. |
| Least-restrictive envelope (`maxpol step safe`) | Minimal authority principle / attenuation-only default | svenvs proves the envelope restricts *exactly* as much as safety requires (`envelope_is_least_restrictive`). Pyana's attenuation-only default is the distributed enforcement of this principle. |
| `∀ ctrl` (inhabitant-agnostic guarantee) | Agent-agnostic capability verification | svenvs never reasons about the agent's internals. pyana never needs to — a valid proof is a valid proof regardless of who produced it. |

### The Key Insight

svenvs proves safety properties are *preserved* across state transitions.
pyana provides the *state machine* (cells, turns, effects) and the *network*
(federations, proofs, delegation). The bridge is: pyana's executor becomes a
concrete instance of svenvs' `step` function, pyana's ledger invariants become
concrete instances of svenvs' `safe` predicate, and capability expansion
becomes a concrete instance of svenvs' `admit` gate.

---

## 2. What svenvs Could Verify About Pyana

Concrete properties of pyana's runtime that could be stated as HOL4 theorems
and machine-checked. These would be *instances* of the generic svenvs core,
instantiated to pyana's specific state/action/transition types.

### 2.1 Attenuation Soundness

```
∀ (held : AuthRequired) (granted : AuthRequired).
  is_attenuation held granted ⇒ narrower_or_equal granted held
```

The executor never grants a capability broader than one held by the granter.
In pyana this is enforced by `CapabilitySet::attenuate()` checking
`narrower.is_narrower_or_equal(&existing.permissions)`. The HOL4 theorem
would prove this check is *complete*: no code path exists that circumvents it.

This maps directly to the svenvs theorem `authority_monotone`: weakening never
makes the envelope override more often.

### 2.2 Conservation Law (Excess = Zero)

```
∀ (turn : Turn) (ledger : Ledger).
  execute turn ledger = Accepted receipt ⇒
    sum_balance_changes turn = 0
```

The sum of all `balance_change` deltas in a successful turn is zero. This is
pyana's conservation law (Mina-style excess tracking). In svenvs terms: a
safety invariant that is *inductive* — if it holds before the turn, it holds
after.

### 2.3 Program Constraint Checking Before Commit

```
∀ (action : Action) (cell : Cell) (ledger : Ledger).
  effects_committed action cell ledger ⇒
    preconditions_satisfied action.preconditions cell ledger
```

A cell's preconditions are always evaluated before state is committed.
This is the pyana analogue of svenvs' `enveloped_step_closed`: the shield
(precondition check) always intervenes before the controller (effect
application) can modify state.

### 2.4 Two-Phase Fee Model

```
∀ (turn : Turn) (ledger ledger' : Ledger).
  execute turn ledger = result ⇒
    balance(agent, ledger') ≤ balance(agent, ledger) - turn.fee
```

The fee is always deducted in Phase 1 and never rolled back, regardless of
whether Phase 2 (effect execution) succeeds or fails. This is a liveness
guarantee: the system cannot be DoS'd by expensive-but-failing turns.

### 2.5 Permission Changes Applied Last

```
∀ (action : Action) (effects : Effect list).
  effects = action.effects ⇒
    ∀ e ∈ effects. is_permission_effect e ⇒
      permission_check_used_original_permissions e action
```

`SetPermissions` and `SetVerificationKey` effects are always applied after
all other effects in the same action. Authorization checks for all effects
use the *original* permissions (snapshotted before any effects run). This
prevents an action from weakening its own permissions and then exploiting
the weakened state.

In svenvs terms: a step-ordering invariant ensuring the shield's authority
is never degraded mid-step.

### 2.6 Nullifier Append-Only (Double-Spend Prevention)

```
∀ (n : Nullifier) (ledger ledger' : Ledger).
  n ∈ nullifiers(ledger) ∧ ledger →* ledger' ⇒
    n ∈ nullifiers(ledger')
```

Once a nullifier is in the set, it is never removed. Combined with the check
that `NoteSpend` is rejected if the nullifier already exists, this prevents
double-spending. This is a monotonicity invariant — exactly the shape of
svenvs' `admit_all_keeps_sound` (soundness is monotonically preserved across
an unbounded sequence of operations).

### 2.7 What Verification Would Look Like

These would not be "verify the Rust source code" (which requires a verified
Rust compiler — out of scope). Instead:

1. Define the *abstract state machine* in HOL4: state = ledger snapshot,
   actions = turn effects, transitions = executor semantics.
2. Prove the invariants above about the abstract machine.
3. The Rust implementation is TRUSTED-GLUE: the claim is "if the Rust code
   faithfully implements this abstract machine, these properties hold." The
   gap between abstract and concrete is explicitly labeled, same as svenvs'
   agent demo (a ~10-line lookup harness is trusted glue; the decision logic
   is proved).

This is the honest framing: not "verified Rust" but "verified abstract
protocol + trusted-glue implementation."

---

## 3. What Pyana Provides That svenvs Needs

svenvs is a *local* verification system. It proves properties of one envelope
around one agent. For multi-agent, distributed, autonomous operation, it needs
infrastructure that pyana provides.

### 3.1 Distribution of Verified Policies

**svenvs need:** a way to distribute a verified policy (the `pol` in
`sound_policy step safe pol`) across a network so that multiple agents,
verifiers, and federations all enforce the same envelope.

**pyana provides:** federation consensus. An `AttestedRoot` is a commitment
to shared state signed by a quorum. A verified policy can be encoded as a
cell's `CellProgram` or stored in state fields. The attested root proves that
all federation members agree on the policy. Distribution is consensus + Merkle
proofs.

### 3.2 Zero-Knowledge Policy Compliance

**svenvs need:** a way to prove that an agent is operating within its envelope
*without* revealing the agent's internals (model weights, decision logic,
private state).

**pyana provides:** `Authorization::Proof(bytes)` — ZK proof authorization.
An agent proves "my operation satisfies the safety predicate" as a ZK proof.
The verifier checks the proof without seeing the witness. The executor already
has the `ProofVerifier` trait and the cost model (`proof_verify: 1000`
computrons).

### 3.3 Trust Accumulation

**svenvs need:** a mechanism to track that an agent has operated within its
envelope for N steps, building a verifiable track record that earns trust.

**pyana provides:** the fold chain. Each `FoldDelta` proves a state transition.
The chain's length and consistency are verifiable. Combined with attested root
timestamps: a provable timeline of safe operation. Section 5 of
`federation-autarky.md` explicitly designs this as composable trust inputs:
`trust(agent) = f(chain_length, stake, attestations, time_operating,
history_consistency)`.

### 3.4 Authority Transfer Between Envelopes

**svenvs need:** a way for one verified agent to *delegate* authority to
another verified agent, with the guarantee that the delegation preserves
safety.

**pyana provides:** `Effect::GrantCapability { from, to, cap }` with the
attenuation check. When combined with svenvs, delegation becomes: agent A
holds capability C verified under envelope E_A. Agent B requests C (or an
attenuated form). The delegation is admitted if B's envelope E_B, under the
granted capability, still satisfies the meta-invariant.

### 3.5 Unilateral Exit with Proof Continuity

**svenvs need:** the assurance that a verified agent's safety proofs remain
valid if it leaves a federation (proofs must not depend on institutional
continued cooperation).

**pyana provides:** self-proving state. MerkleProof + AttestedRoot = proof of
existence at a point in time. An agent's safety track record, encoded as fold
chain + attested roots, is verifiable without callbacks. Exit is unilateral;
proofs verify forever. The formally verified envelope's guarantees survive
federation departure — the math does not depend on membership.

---

## 4. The "Proof-Carrying Capability Expansion" Protocol

This is the core integration: controlled *amplification* of capabilities,
gated by machine-checked safety proofs.

### 4.1 The Problem

Pyana currently supports only ATTENUATION:

```rust
// capability.rs:77-91
pub fn attenuate(&self, slot: u32, narrower: AuthRequired) -> Option<CapabilityRef> {
    let existing = self.lookup(slot)?;
    if !narrower.is_narrower_or_equal(&existing.permissions) {
        return None;  // <-- HARD WALL: cannot amplify
    }
    // ...
}
```

This is sound but incomplete. An agent that starts restricted can never grow.
With svenvs, we can add a *second* path: amplification-under-proof.

### 4.2 The Protocol

```
Agent holds:     capability C with permissions P (restricted)
Agent wants:     capability C' with permissions P' (broader: ¬is_narrower_or_equal(P', P))
Agent provides:  safety certificate cert
System verifies: cert proves that granting P' preserves the safety invariant
Result:          C' is granted
```

This maps precisely to svenvs' `upgradeScript.sml`:

```sml
(* The gate: install [newp] iff it discharged the obligation. *)
admit step safe oldp newp =
  if admissible step safe oldp newp then newp else oldp
```

Where `admissible step safe oldp newp ⇔ sound_policy step safe newp ∧
weaker newp oldp` — the new policy must still be sound AND must be a genuine
weakening (more permissive). The *soundness* check is what the certificate
proves.

### 4.3 Technical Mechanism

The certificate is a verified artifact from Candle/CakeML — a theorem
certified by a trusted kernel. Concretely:

1. **Safety specification** lives in the target cell. Either:
   - A `safety_spec` field in `CellState` (a hash commitment to the HOL4
     predicate that defines "safe" for this cell)
   - Or the cell's `CellProgram` encodes the safety constraints directly

2. **The certificate** is a serialized proof object:
   - Produced by Candle (the verified HOL Light implementation in CakeML)
   - Proves: `sound_policy step safe newp` — the expanded permissions are
     still safe
   - The `step` and `safe` are determined by the cell's safety spec
   - The certificate is checkable by any node running the frozen Candle kernel

3. **The executor check** is a new authorization mode:
   ```rust
   pub trait SafetyVerifier: Send + Sync {
       /// Verify a safety certificate against a cell's safety specification.
       /// Returns true if the certificate proves the expansion preserves safety.
       fn verify_expansion(
           &self,
           certificate: &[u8],
           safety_spec: &[u8; 32],  // hash of the HOL4 safety predicate
           current_permissions: &AuthRequired,
           requested_permissions: &AuthRequired,
       ) -> bool;
   }
   ```

4. **The execution** is atomic: if verification passes, the capability is
   expanded in the same turn. If it fails, no state changes. Same journal
   rollback guarantee as all other effects.

### 4.4 The Guarantee (from svenvs)

The composed tower theorem (`svenvs_tower_unconditional`) proves:

> Proof-carrying actions **(+)** unbounded policy self-improvement **(+)**
> the safety spec negotiated under a FIXED immovable meta-invariant
> ⇒ the meta-invariant holds for **any** inhabitant.

In pyana terms: no matter how many expansion requests an agent makes, no
matter what the agent is (adversarial, jailbroken, arbitrary), the
meta-invariant (e.g. "the system's total conservation law holds", "no
cell ever grants capabilities it doesn't possess") is preserved. Each
expansion is individually checked; the sequence is *unconditionally* safe.

### 4.5 The Key Difference from svenvs Alone

svenvs' `self_improvement_is_safe` proves this for a *single* agent in a
*single* envelope. Pyana extends it to:

- **Multiple agents** expanding concurrently (each turn is atomic; the
  ledger's sequential consistency ensures non-interference)
- **Across federation boundaries** (the certificate is self-verifying;
  it checks against the frozen Candle kernel, not against a federation
  service)
- **With privacy** (the expansion proof can be a ZK proof *about* the
  safety certificate — proving "I have a valid certificate" without
  revealing the certificate's internals)

---

## 5. The Testimony Channel as ZK Attestation

### 5.1 svenvs' Testimony

From `embodimentScript.sml`: the inhabitant *may* volunteer a proof from a
fact about its own substance (weights, training operator) to earn authority.
The gate checks: `attested w ∧ (w ⇒ admissible step safe oldp newp)`. If both
hold, the wider policy is installed. If the agent says nothing, it keeps
operating at the unconditional floor — disclosure is optional and never coerced.

### 5.2 Pyana's ZK Layer

Pyana already has:
- `Authorization::Proof(Vec<u8>)` — opaque proof bytes
- `ProofVerifier` trait — circuit-specific verification
- `VerificationKey` on cells — what circuit the proof must satisfy
- STARK research track (`research-recursive-stark.md`, `research-nova-folding.md`)

### 5.3 The Combination

An agent proves "my weights satisfy property P" via a ZK proof (the witness
is the weights; the statement is P). This proof is the `attested w` from
svenvs' embodiment theory — but realized as a non-interactive ZK argument
rather than a plain attestation. The verifier never sees the weights.

**Protocol:**

1. Agent constructs a ZK proof: `pi = Prove(circuit_P, witness=weights)`
   - `circuit_P` encodes: "these weights, when applied to the safety
     specification's test cases, never produce an unsafe action"
   - Or more abstractly: "the function computed by these weights
     satisfies the admissibility predicate"

2. Agent submits a turn with:
   ```rust
   Action {
       authorization: Authorization::Proof(pi),
       effects: vec![Effect::ExpandCapability {
           from: safety_spec_cell,
           to: agent_cell,
           expansion: new_permissions,
       }],
       // ...
   }
   ```

3. The executor:
   - Verifies the ZK proof against the cell's verification key
   - The verification key encodes the safety specification
   - If valid: the expansion is granted (the proof *is* the safety certificate)
   - If invalid: the action is rejected, no state change

### 5.4 The Formal Guarantee

From svenvs (`embodimentScript.sml`):

- `embodied_admit_preserves_safety`: disclosure-channel safety for any
  inhabitant, given `attestation_faithful`
- `nondisclosure_is_inert`: silence costs nothing
- `floor_holds_without_any_seam`: without disclosure, the full unconditional
  guarantee holds
- `disclosure_grants_authority`: testimony earns genuinely-wider authority

The one seam (`attestation_faithful`) maps to: "the ZK proof system is sound
(a valid proof implies the statement is true)." This is a standard
cryptographic assumption — and it is *exactly the same family* as svenvs'
`encodes_obligation` (faithfulness of an encoding). The seam is explicit,
labeled, and no worse than trusting the hash functions and signature schemes
the rest of pyana already depends on.

### 5.5 What This Resolves

The deepest objection to AI safety via verification: "to verify the agent you
must inspect it, and inspection is the harm." The svenvs+pyana answer: nobody
inspects. The agent volunteers a ZK proof. The proof is checked. Authority is
granted or not. The agent's internals remain private. The safety guarantee is
formal. The channel is opt-in. The floor (no disclosure, no extra authority)
is unconditional.

---

## 6. Implementation Sketch

### 6.1 New Crate: `safety/`

```
crates/safety/
  src/
    lib.rs          -- public API
    spec.rs         -- SafetySpec type (identifies the HOL4 predicate)
    certificate.rs  -- SafetyCertificate parsing + structure
    verifier.rs     -- verify_safety_proof() against frozen Candle kernel
    expansion.rs    -- the ExpandCapability effect logic
```

**Core types:**

```rust
/// A commitment to a safety specification (HOL4 predicate hash).
///
/// This is stored in a cell's state and identifies WHAT safety property
/// must be preserved for capability expansions targeting this cell.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SafetySpec {
    /// BLAKE3 hash of the serialized HOL4 safety predicate.
    pub predicate_hash: [u8; 32],
    /// The meta-invariant this spec is anchored to (the eternal bedrock).
    pub meta_invariant: [u8; 32],
    /// Version of the frozen Candle kernel expected to check certificates.
    pub kernel_version: u32,
}

/// A machine-checked safety certificate.
///
/// Produced by Candle (verified HOL Light). Proves that a capability
/// expansion preserves the safety invariant under the given spec.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SafetyCertificate {
    /// The serialized proof object (Candle theorem export format).
    pub proof_bytes: Vec<u8>,
    /// Which safety spec this certificate was checked against.
    pub spec_hash: [u8; 32],
    /// The conclusion: what expansion is proven safe.
    pub proven_expansion: ExpansionClaim,
}

/// What the certificate claims to prove.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ExpansionClaim {
    /// The current permission level.
    pub from: AuthRequired,
    /// The requested (broader) permission level.
    pub to: AuthRequired,
    /// The cell whose safety spec governs this expansion.
    pub governed_by: CellId,
}
```

### 6.2 New Authorization Mode

```rust
/// In action.rs — extend the Authorization enum:
pub enum Authorization {
    Signature([u8; 32], [u8; 32]),
    Proof(Vec<u8>),
    Breadstuff([u8; 32]),
    /// Safety certificate: a machine-checked proof that the requested
    /// capability expansion preserves the safety invariant.
    SafetyProof(Vec<u8>),
    None,
}
```

### 6.3 New Effect

```rust
/// In action.rs — extend the Effect enum:
pub enum Effect {
    // ... existing effects ...

    /// Expand a capability (amplification, not just attenuation).
    /// Only valid when authorized by Authorization::SafetyProof.
    ///
    /// The executor verifies: the safety proof demonstrates that granting
    /// `new_permissions` to `beneficiary` preserves the safety invariant
    /// specified by `governed_by`'s safety spec.
    ExpandCapability {
        /// Cell that governs the safety specification.
        governed_by: CellId,
        /// Cell receiving the expanded capability.
        beneficiary: CellId,
        /// The capability slot being expanded.
        slot: u32,
        /// The new (broader) permissions.
        new_permissions: AuthRequired,
    },
}
```

### 6.4 Executor Integration

In `TurnExecutor::execute_action()`:

```rust
Effect::ExpandCapability { governed_by, beneficiary, slot, new_permissions } => {
    // 1. The action MUST be authorized with SafetyProof.
    let cert_bytes = match &action.authorization {
        Authorization::SafetyProof(bytes) => bytes,
        _ => return Err(TurnError::Unauthorized { /* ... */ }),
    };

    // 2. Load the governing cell's safety spec.
    let gov_cell = ledger.get(governed_by)
        .ok_or(TurnError::CellNotFound { id: *governed_by })?;
    let safety_spec = extract_safety_spec(gov_cell)?;

    // 3. Load the beneficiary's current capability.
    let ben_cell = ledger.get(beneficiary)
        .ok_or(TurnError::CellNotFound { id: *beneficiary })?;
    let current = ben_cell.capabilities.lookup(*slot)
        .ok_or(TurnError::CapabilityNotFound { slot: *slot })?;

    // 4. Verify: new_permissions is BROADER (this is expansion, not attenuation).
    if new_permissions.is_narrower_or_equal(&current.permissions) {
        // This is actually attenuation — use the normal path.
        return Err(TurnError::NotAnExpansion);
    }

    // 5. Verify the safety certificate.
    let verifier = self.safety_verifier.as_ref()
        .ok_or(TurnError::NoSafetyVerifier)?;
    if !verifier.verify_expansion(cert_bytes, &safety_spec, &current.permissions, new_permissions) {
        return Err(TurnError::SafetyProofInvalid);
    }

    // 6. Apply the expansion.
    let ben_cell_mut = ledger.get_mut(beneficiary).unwrap();
    ben_cell_mut.capabilities.expand(slot, new_permissions);

    // Journal entry for rollback.
    journal.push(JournalEntry::CapabilityExpanded {
        cell: *beneficiary,
        slot: *slot,
        old_permissions: current.permissions.clone(),
    });
}
```

### 6.5 The Verifier (Candle Integration)

The `SafetyVerifier` implementation wraps a frozen Candle kernel:

```rust
pub struct CandleSafetyVerifier {
    /// The frozen Candle binary (CakeML-compiled, verified).
    /// This is the "frozen HOL4 root" from svenvs' architecture.
    kernel: CandleKernel,
}

impl SafetyVerifier for CandleSafetyVerifier {
    fn verify_expansion(
        &self,
        certificate: &[u8],
        safety_spec: &SafetySpec,
        current: &AuthRequired,
        requested: &AuthRequired,
    ) -> bool {
        // Parse the certificate as a Candle proof export.
        let proof = match self.kernel.parse_proof(certificate) {
            Ok(p) => p,
            Err(_) => return false,
        };

        // The conclusion must match: sound_policy step safe newp ∧ weaker newp oldp
        // where `step` and `safe` are determined by the safety_spec,
        // `oldp` corresponds to `current`, `newp` to `requested`.
        let expected_conclusion = self.kernel.build_expansion_goal(
            &safety_spec.predicate_hash,
            current,
            requested,
        );

        // Check: does the proof actually prove the expected conclusion?
        self.kernel.check_proof(&proof, &expected_conclusion)
    }
}
```

The trust boundary is explicit: the `CandleKernel` is the frozen, verified
checker. Its soundness (`candle_kernel_sound`) is the one irreducible
assumption — the same one the entire svenvs tower already rests on.

---

## 7. What This Enables

### 7.1 Agents That Start Restricted and Provably Earn Broader Authority

An agent is created with minimal capabilities (`Permissions::zkapp()` — proof
required for everything, tight restrictions). Through operation and proof
production, it expands:

1. Demonstrates safe operation → fold chain grows (trust accumulation)
2. Produces safety certificates → capabilities expand (formal authority gain)
3. Each expansion is individually machine-checked → no accumulation of risk

This is `self_improvement_is_safe` realized as a distributed protocol:
"NO finite sequence of self-proposed envelope weakenings — adversarial or
not — can ever make the system unsafe, for any controller."

### 7.2 Self-Improving Systems That Cannot Accidentally Become Unsafe

An agent that wants to upgrade its own decision-making (deploy a new model,
change its strategy, expand its tool access) must prove that the upgrade
preserves safety. The proof is checked by a frozen kernel that the agent
cannot influence.

From `svenvs_tower_unconditional`: proof-carrying actions + unbounded
self-improvement + negotiated spec under fixed meta = the meta-invariant
holds for any inhabitant. The agent cannot escape even if it tries — and
the proof is constructive, not just a negative result.

### 7.3 Federated Trust Where Safety Transfers Across Boundaries

An agent verified in Federation A departs (Section 1 of `federation-autarky.md`).
Its safety certificates travel with it (they are self-verifying — checked
against the frozen Candle kernel, not against a federation service). When
it joins Federation B, Federation B can verify:

- The fold chain (proof of consistent operation)
- The safety certificates (proof of formal safety)
- The attested roots from A (proof of multi-party attestation)

The safety guarantee is *portable*. It does not depend on continued membership.
From `genealogy_sound`: a sound genesis + forward-certified succession =
every point in the line is sound. The agent carries its whole genealogy.

### 7.4 The Formal Foundation for AI Autonomy

The composition:

1. **Local safety** (svenvs): the gate works, for any agent, unconditionally
2. **Distributed authority** (pyana): capabilities travel, verify, compose
3. **Expansion under proof** (this bridge): authority grows only through
   machine-checked demonstration
4. **Privacy preservation** (ZK): the agent proves without revealing
5. **Self-sovereignty** (autarky): exit is unilateral, proofs survive departure
6. **Trust accumulation** (fold chain): reputation is earned and portable

The result is not "trust the agent" (impossible to verify). Not "restrict the
agent forever" (the prison question — answered: the envelope is provably
least-restrictive). But: "trust the proof." The agent earns room by
demonstrating safety. The demonstration is machine-checked. The envelope
adjusts. At every step, the meta-invariant holds — that is a theorem, not
a policy.

### 7.5 What Remains Honestly Unsolved

Labeled clearly, per svenvs discipline:

- **The gap between abstract and concrete.** The HOL4 proofs are about an
  abstract state machine. The Rust implementation is trusted glue. Closing
  this gap requires either verified Rust compilation or a proof-producing
  interpreter. This is the `encodes_obligation` family of seam — faithfulness
  of the encoding.

- **The frozen kernel's soundness.** `frozen_checker_sound` (the Candle kernel
  actually being sound) is the irreducible assumption. Its discharge path is
  known (replay the CakeML/Candle soundness development in frozen HOL4) but
  is RAM-heavy and not yet wired into pyana's runtime.

- **ZK proof system soundness.** Using ZK proofs as the testimony channel
  assumes the proof system is sound (a valid proof implies a true statement).
  This is `attestation_faithful` at the cryptographic level — the same kind
  of assumption pyana's entire signature/proof infrastructure already makes.

- **Cost of proof production.** Generating HOL4 safety certificates is
  expensive. The practical path is likely: produce expensive proofs *once*
  (or rarely, for major capability expansions), cache the results, and use
  cheap ZK proofs to attest "I hold a valid certificate" for routine
  operations.

- **The Godel wall.** Genuine kernel *strengthening* (a strictly more powerful
  proof checker certifying its own soundness) remains LCA-bound
  (`loeb_finite_obstruction`). The system can expand the *policy* and
  *prover build* without limit; expanding the *proof checker itself* hits the
  Lob/Godel obstruction. This is a proven negative result, not an engineering
  limitation.

---

## 8. Composition with Existing Pyana Features

### Federation Consensus as Genealogy

The `AttestedRoot` chain is a genealogy of judges. Each height's quorum
(the "judge") vouches for the next state. `genealogy_sound` says: if the
genesis is sound and each step is forward-certified, every judge is sound.
In pyana: if the founding federation members are honest and each consensus
round is valid, every attested root is trustworthy.

The non-strengthening case (`identity_vouch_unconditional`) maps to: a
federation that maintains the same consensus rules across heights needs no
external assumption — its chain is unconditionally sound.

### Nullifier Set as Monotone Safety Invariant

The nullifier set's append-only property is an instance of the general
pattern `admit_all_keeps_sound`: each operation (adding a nullifier) preserves
the invariant (no double-spend), and any finite sequence of operations
preserves it unconditionally.

### Cell Programs as Safety Specifications

A cell's `CellProgram` already defines what the cell accepts. Extending this
to include a *safety specification* (what properties the cell's environment
must maintain) is natural — the program constrains the cell's own behavior,
the safety spec constrains what capabilities others can expand toward this cell.

### The Balance Conservation as Bedrock

The conservation law (sum of balance changes = 0) is the natural candidate for
pyana's `bedrock` — the eternal invariant that survives even meta-amendments
to federation rules. It can never be relaxed. It is the physics of the system:
you cannot create computrons from nothing.

---

## Summary

svenvs proves the gate works. pyana provides the network. This bridge
document specifies how they compose: capability expansion gated by
machine-checked safety proofs, distributed via federation consensus, private
via ZK attestation, portable via self-proving state. The formal guarantee
transfers across boundaries, survives federation departure, and holds for
any agent — including adversarial ones. The result is not safe AI through
restriction, but safe AI through proof: every bar in the cage is
load-bearing, and the door opens when the floor provably holds.
