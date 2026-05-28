# `Authorization::Custom` — design study

**Date:** 2026-05-24.
**Lane:** study/design (read-only, single new `.md`).
**Status:** design proposal; no code lands with this commit.

**Companion documents to read first.**
- `PREDICATE-INVENTORY.md` (§3 `WitnessedPredicate`; §4 composition
  rules).
- `SLOT-CAVEATS-DESIGN.md` and `SLOT-CAVEATS-EVALUATION.md`
  (`StateConstraint::Custom { ir_hash, descriptor, reads }`; the
  discipline applied to `Custom` escapes).
- `BOUNDARIES.md` (the boundary contract vocabulary used in §4).
- `AUDIT-protocol-composition.md` (the current `Authorization`
  shape and its multi-producer surface).
- `EXECUTOR-HONESTY-AUDIT.md` (T2 forge-effects, T6 cross-federation
  replay, T10 skip-permission, T11 stale proof).

The brief: today's `Authorization` enum has explicit variants
(`Signature`, `Proof`, `Breadstuff`, `Bearer`, `CapTpDelivered`,
`Unchecked`). With slot caveats v1, `WitnessedPredicate`, and DSL
backends, an app could in principle define its own auth mode by
attaching a `WitnessedPredicate` that proves authorization. Design
`Authorization::Custom`.

---

## §1. What is `Authorization::Custom`?

The proposal is one new variant of `turn::action::Authorization`:

```rust
pub enum Authorization {
    Signature([u8; 32], [u8; 32]),
    Proof { proof_bytes: Vec<u8>, bound_action: String, bound_resource: String },
    Breadstuff([u8; 32]),
    Bearer(BearerCapProof),
    Unchecked,
    CapTpDelivered { /* … */ },

    /// App-defined authorization: a `WitnessedPredicate` proves the
    /// authorization condition. The predicate's input is bound to
    /// the action's canonical signing message; the predicate's
    /// commitment names the auth mode.
    Custom {
        /// The witnessed predicate that proves authorization.
        predicate: WitnessedPredicate,
        /// The auth-mode descriptor: published name + version + boundary
        /// contract. The descriptor's `vk_hash` must match the
        /// predicate's `kind: Custom { vk_hash }` (or, for built-in
        /// kinds, the descriptor's `vk_hash` must equal the kind's
        /// canonical hash). Required so audit tools can render a
        /// human-readable mode without dereferencing the verifier.
        descriptor: AuthModeDescriptor,
    },
}
```

with the auxiliary shape:

```rust
/// Published descriptor of an auth mode. Mirrors the
/// `CustomDescriptor` shape in `SLOT-CAVEATS-EVALUATION.md §5.4(d)`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AuthModeDescriptor {
    /// Verifier key hash that names the auth mode in the registry.
    pub vk_hash: [u8; 32],
    /// Human-readable name + version. e.g. ("multisig", semver(2,0,0)).
    pub human_name: String,
    pub semver: dregg_types::SemVer,
    /// Authoring package reference (chain-attested or local).
    pub authoring_package: PackageRef,
    /// Boundary-contract advertisement (BOUNDARIES.md §5.2).
    /// Editorial; the executor does not enforce that the predicate's
    /// runtime behaviour matches this advertisement.
    pub boundary_contract: BoundaryContract,
}
```

The intent is *not* to introduce a new cryptographic primitive — the
crypto already lives in `WitnessedPredicate`'s kind verifier. The
intent is to give app authors a *single Authorization variant* that
routes through the predicate registry the same way
`StateConstraint::Witnessed(WP)` and `Preconditions::witnessed` do.

The single new structural commitment in `Custom` is the descriptor.
A naked predicate would already work mechanically (executor reads
`kind`, dispatches, calls verifier with input = signing message); the
descriptor lifts the *human-readable* and *governance-attested*
metadata out of the registry into the on-wire authorization so
cipherclerks, audit tools, and verifier replay can render and reason about
the mode without a registry lookup.

---

## §2. Verification path

The executor's `verify_authorization` (`turn/src/executor.rs:4348`)
gains one new arm. The flow:

1. Executor receives a `Turn` containing an `Action` with
   `Authorization::Custom { predicate, descriptor }`.
2. **Descriptor → kind consistency check.**
   - If `predicate.kind == WitnessedPredicateKind::Custom { vk_hash }`:
     require `vk_hash == descriptor.vk_hash`. (The descriptor
     advertises the same verifier the predicate names.)
   - If `predicate.kind` is a built-in (`Dfa`, `Temporal`, etc.):
     require `descriptor.vk_hash == canonical_vk_hash_for(kind)`.
     The canonical hash is a constant per built-in kind (mirrors
     how `Effect::Custom`-style registries pin built-ins per
     `DESIGN-max-custom-effects.md`).
3. **Registry lookup.** Resolve the verifier via
   `WitnessedPredicateRegistry::lookup(descriptor.vk_hash)`. If the
   federation does not have the verifier registered, reject with
   `TurnError::AuthModeNotRegistered { vk_hash }`. (No silent
   fallback. The mode must be on the federation's allowlist.)
4. **Input binding.** Compute the canonical action signing message
   `M = canonical_signing_message(action, position, federation_id,
   turn_nonce)` — the same message
   `compute_partial_signing_message` in
   `turn/src/executor.rs:5286` already constructs for the
   `Signature` path. Bind `M` as the predicate's input.
5. **Verifier call.** `verifier.verify(commitment, input = M,
   proof_bytes = action.witness_blobs[predicate.proof_witness_index])`.
   On error, return `TurnError::InvalidAuthorization { reason }`.
6. **Effect-mask check (optional, per descriptor).** If the
   `AuthModeDescriptor` declares an `allowed_effects: Option<EffectMask>`,
   apply the same facet-attenuation check that `Bearer` already
   performs (`turn/src/executor.rs:4412-4429`). The descriptor's
   mask must contain the action's effect-kind mask, or the action
   is rejected.

The dispatch reuses the existing predicate-registry machinery; the
only new code path is the four-step gate above. No new AIR; no new
canonical-message format; no new wire shape outside the variant
itself.

### §2.1. Cost accounting

The executor's `costs` table (`turn/src/executor.rs:4029-4035`)
gains one entry:

```rust
Authorization::Custom { predicate, .. } => match predicate.kind {
    WitnessedPredicateKind::Dfa => self.costs.dfa_verify,
    WitnessedPredicateKind::Temporal => self.costs.temporal_verify,
    WitnessedPredicateKind::MerkleMembership => self.costs.merkle_verify,
    WitnessedPredicateKind::BlindedMembership => self.costs.blinded_membership_verify,
    WitnessedPredicateKind::BridgePredicate => self.costs.bridge_predicate_verify,
    WitnessedPredicateKind::PedersenEquality => self.costs.pedersen_verify,
    WitnessedPredicateKind::Custom { .. } => self.costs.custom_auth_verify,
},
```

Per-kind costs were already needed when `StateConstraint::Witnessed`
landed; this just reuses them.

### §2.2. The replay path

Per `EXECUTOR-HONESTY-AUDIT.md` T11 (stale proof): the canonical
signing message includes `federation_id`, `turn_nonce`, and the
action hash. The predicate's input is exactly that message, so
the proof is bound to *this turn at this federation at this nonce
position*. Stale proofs do not replay; cross-federation proofs do
not replay; same-federation different-nonce proofs do not replay.
The argument is identical to the `Signature` path.

On `WitnessedReceipt`-scope-2 replay, the receipt carries:
- the full `Authorization::Custom` variant (predicate, descriptor),
- the `witness_blobs` index referenced by `proof_witness_index`,
- the `commitment` snapshot (if `commitment` was resolved from
  external state at receipt-time, per `PREDICATE-INVENTORY.md §6.3`).

The replayer re-runs steps 2-5 of §2 against the snapshotted
commitment and the receipt-bound message. Replay-soundness is
*the same* as the original verification because the verifier is
deterministic.

---

## §3. Use cases — motivating apps

The variant earns its place if real apps can use it. The retained
apps from `APPS-AS-USERSPACE-AUDIT.md` plus the multisig case yield
six concrete shapes.

### §3.1. Multisig auth (as `Custom`, not a dedicated variant)

A Merkle set of N signer keys, with a STARK that proves "at least
K of N signers produced an aggregate signature over the action's
canonical signing message."

```rust
Authorization::Custom {
    predicate: WitnessedPredicate {
        kind: WitnessedPredicateKind::Custom {
            vk_hash: multisig_v2_vk_hash,
        },
        commitment: signer_set_root,
        input_ref: InputRef::PublicInput { pi_index: 0 },
        proof_witness_index: 0,
    },
    descriptor: AuthModeDescriptor {
        vk_hash: multisig_v2_vk_hash,
        human_name: "kof_n_multisig".into(),
        semver: SemVer(2, 0, 0),
        boundary_contract: BoundaryContract {
            cleartext_inside: "the K signers who produced sub-signatures",
            commitment_inside: "anyone with the signer_set_root",
            acceptance_inside: "the STARK verifier learns only K-of-N satisfied",
            out_of_band: "everyone else",
        },
        ..
    },
}
```

The `commitment` is the Merkle root of the allowed signer set. The
proof's public inputs include the action's canonical signing
message; the verifier checks that K of N signers (private to the
proof) signed it. This *replaces* a hypothetical
`Authorization::Multisig` variant. The crypto shape — Merkle-set +
threshold-sig over a bound message — is generic; `Custom` is the
right place.

### §3.2. DAO-quorum auth

A `Custom` predicate where the commitment is the DAO's committee
key + voting-weight Merkle root, and the proof attests
"≥ threshold-weight of committee members signed this action's
canonical message." Differs from §3.1 only in the weight algebra:
some signers count more than one vote. Same shape; different verifier.

Motivating app: governance turns on the `dregg-governance` cell
proposed in `APPS-AS-USERSPACE-AUDIT.md` Lane H. Today such a turn
would have to either:
- carry a full `Vec<(signer_pk, signature)>` plus weight metadata
  in the witness (bloated, non-private), or
- use `Authorization::Proof` with custom verifier-key + non-canonical
  binding (loses the audit visibility — `Proof` has no descriptor).

`Custom` solves both: compact proof, registered verifier, named mode.

### §3.3. Time-locked auth

A `WitnessedPredicate { kind: Temporal, commitment: temporal_dsl_hash }`
where the DSL predicate is "height ≥ unlock_height AND the action is
the unique unlocking turn (binding the action hash into the predicate
state)."

This lets time-locks be authorization, not just constraint: a vault
cell could declare "any action against this cell requires
`Authorization::Custom` with a temporal predicate proving height ≥
unlock_height" — and the cclerk generates the proof at the time the
unlock comes due, with no executor-side scheduling needed.

The single existing user is `compute-exchange`'s ticket-release
("after height H, attestation expires"); §6 below traces it through.

### §3.4. Capability-conditional auth

A `WitnessedPredicate { kind: MerkleMembership, commitment:
capability_root_of_actor }` whose proof attests "the actor holds
capability X (cell-id Y) in their c-list." The proof is bound to the
action's signing message via PI.

This is *not* quite the same as `Authorization::Bearer`: bearer is
"I have a delegated cap presented inline"; capability-conditional
is "I hold this cap in my c-list and can prove membership without
revealing other caps." The use case is privacy-preserving
cap-presentation — a cell can require auth-by-cap-X without learning
which other caps the holder has, which is what
`dregg-nameservice`'s `name-owner` proof should look like once the
sovereign cell extends to private c-list membership.

### §3.5. Compute-attested auth

A `WitnessedPredicate { kind: Custom { vk_hash:
computation_attestation_air_vk } }` whose verifier checks "I ran
computation Y to completion and got result Z, and result Z is bound
to this action." The "computation" can be an Effect VM trace
(see `EFFECT-VM-SHAPE-A.md`).

Motivating app: `compute-exchange` — the bidder authorizes turn
"settle bid N" not with a signature but with a *proof that they
performed the requested computation and got the claimed answer*.
This is computational authorization in the strict sense: who can do
this now is "anyone who performed Y."

### §3.6. Identity-credential-attested auth

A `WitnessedPredicate { kind: BlindedMembership, commitment:
credential_ring_root }` — the action is authorized because the
sender proves membership in a blinded credential ring (e.g., "a
verified user of platform P") without revealing which credential.

Motivating app: `dregg-gallery`'s `verified-buyer` gate — a buyer
proves they belong to the platform's blinded buyer ring before the
seller's release-on-receipt action commits.

### §3.7. Combinations

Conjunction of two Custom predicates (e.g., "compute-attested AND
within time window") is *not* a new `Custom`; it's two clauses in
`Preconditions::witnessed: Vec<WitnessedPredicate>` plus a
`Custom { kind: Custom { vk_hash: trivial_passthrough_vk } }` as
the authorization. That keeps the authorization variant
single-shaped — one predicate proves auth — and pushes composition
to preconditions, where it already exists.

Recommendation: do **not** add `Authorization::CustomAll(Vec<…>)`
or `Authorization::CustomAny(Vec<…>)`. The composition surface is
`Preconditions::witnessed: Vec<WP>` per
`PREDICATE-INVENTORY.md §4.1`; reusing it avoids a second
composition algebra.

---

## §4. Boundary contracts

Per `BOUNDARIES.md §5.1`'s four-population vocabulary
(cleartext-inside / commitment-inside / acceptance-inside / out-of-band),
the **authorization** itself has its own boundary contract, and each
auth mode's `AuthModeDescriptor.boundary_contract` advertises that
contract.

### §4.1. The cleartext-inside set for `Authorization::Custom`

Different auth modes name different cleartext-inside sets. The
descriptor must say which.

| Mode | Cleartext-inside |
|---|---|
| K-of-N multisig (§3.1) | the K signers (each knows their own sub-signature); the set author (knows all N keys) |
| DAO-quorum (§3.2) | the committee members + the DAO secretary who assembles |
| Time-locked (§3.3) | anyone (the predicate is height-only; no secret) |
| Capability-conditional (§3.4) | the c-list owner (knows membership + Merkle witness) |
| Compute-attested (§3.5) | the computation runner (knows the trace) |
| Credential-attested (§3.6) | the credential holder + the credential issuer |

This matters because *the cclerk that constructs the action* must
be cleartext-inside the auth predicate. If the cclerk is
out-of-band, it cannot generate the proof; if the cclerk is only
commitment-inside, it can witness but not generate the proof. The
descriptor's `boundary_contract.cleartext_inside` field tells
audit tools which population can use this mode.

### §4.2. The commitment-inside set

In every mode, the *federation* is commitment-inside the auth
predicate's commitment — the federation sees the
`WitnessedPredicate.commitment` field in cleartext and uses it to
look up the verifier and resolve the input. The federation does not
see the *witness data* (the secret that the proof attests) except
through the action's `witness_blobs`, which may itself be encrypted
or blinded per the kind's design.

This is the same boundary as today's `Authorization::Proof`: the
proof bytes are visible, the public inputs are visible, the witness
is acceptance-inside the verifier.

### §4.3. The acceptance-inside set

The acceptance-inside set is the **STARK verifier** for the kind.
A predicate accepts, the verifier accepts, and the receiver of the
receipt accepts that "the authorization condition held" without
learning what specifically held it.

Concretely: under §3.4 (capability-conditional), a receipt-reader
sees that "the sender held a cap that's in the actor's c-list" but
does *not* learn which cap. Under §3.5 (compute-attested), the
receipt-reader sees that "the computation produced the claimed
result" but does not learn the trace.

This is *new* compared to today's `Signature`/`Proof` modes:
- `Signature` is acceptance-inside-trivially — anyone who sees the
  receipt sees who signed (the public key is in the action).
- `Proof` is acceptance-inside-the-verifier, but the verifier
  attests only that "the proof checks against
  (bound_action, bound_resource)" — a weak audit story.
- `Custom` makes the acceptance-inside story explicit per mode via
  the descriptor.

### §4.4. The out-of-band set

Out-of-band for `Authorization::Custom`:
- Anyone outside the federation gossip — they don't see the
  authorization at all.
- Anyone inside the federation but without the registered verifier
  for `vk_hash` — they cannot evaluate the proof (and must
  reject the receipt per §6 below, or trust another federation
  member).
- Anyone replaying the chain without the kind's verifier in their
  registry — same problem; the replay fails closed.

### §4.5. The composition of contracts

Per `BOUNDARIES.md §6`, when boundaries nest: a sovereign cell with
`Authorization::Custom { kind: BlindedMembership, … }` is:

```
out-of-band
  \
   federation (commitment-inside the auth commitment)
     \
      verifier (acceptance-inside the proof)
        \
         credential-holder (cleartext-inside the membership witness)
```

The innermost boundary is *the credential-holder*. The federation
learns only that the holder is in the ring; the verifier learns
only that the proof checks. This composition is the strongest
privacy story `Custom` can deliver.

### §4.6. What `Custom` does NOT change about boundaries

The action itself (effects, target, nonce, witness_blobs metadata)
remains visible to the federation. `Custom` authorizes the action,
not the action's content. To privatize the action body, see the
witnessed-receipt / sovereign-cell paths
(`BOUNDARIES.md §2.6, §2.8`).

---

## §5. Composition with existing `Authorization` variants

The hard question: should `Custom` *subsume* the explicit variants
(collapse the enum), or *coexist* with them?

### §5.1. Argument for subsumption

Mathematically every variant is "a witnessed predicate over the
canonical signing message":

- `Signature(r, s)` ≅ `Custom { predicate: WP { kind: Custom {
  vk_hash: ed25519_canonical }, commitment: actor_pk, input_ref:
  PublicInput { 0 }, proof_witness_index: 0 } }` with the
  "proof" being the 64-byte signature.
- `Proof { … }` ≅ `Custom { predicate: WP { kind: Custom { vk_hash:
  proof_verifier_vk }, commitment: bound_resource_hash, … } }`.
- `Bearer(BearerCapProof)` ≅ a `WP { kind: Custom { vk_hash:
  bearer_cap_air_vk }, … }`.
- `Breadstuff([u8; 32])` ≅ `WP { kind: Custom { vk_hash:
  cap_token_lookup_vk }, commitment: cap_token, … }`.
- `CapTpDelivered { … }` ≅ a `WP { kind: Custom { vk_hash:
  captp_delivery_vk }, … }`.
- `Unchecked` ≅ `WP { kind: Custom { vk_hash: zero_predicate_vk },
  proof: [] }`.

A unified surface gives one verification path, one cost-table
entry, one descriptor for every auth mode.

### §5.2. Argument against subsumption (the operative case)

Three structural objections to collapsing.

**(a) Some variants are too primitive to be a `WitnessedPredicate`.**
`Signature` is 64 bytes of `(r, s)` — there is no commitment to a
verifier key (the verifier is `ed25519::verify_strict`), there is
no `proof_witness_index` (the signature *is* the proof, and it
lives in the variant, not in `witness_blobs`), there is no
`InputRef` (the input is always the canonical signing message).
Wrapping it in `WitnessedPredicate` adds three pieces of
zero-information metadata to every signed turn — every cclerk pays
that bandwidth and audit-noise tax for no benefit. Same argument
for `Breadstuff` (a single 32-byte token hash).

This mirrors `PREDICATE-INVENTORY.md §3.6 case 1`: "static
cleartext-inside-fed pure predicates… forcing them through
`WitnessedPredicate` adds 32 bytes of zeroes commitment plus an
empty proof — wasted bandwidth and audit noise."

**(b) Some variants carry policy that doesn't fit the
predicate-input shape.** `Bearer(BearerCapProof)` carries
delegation-chain semantics — `expires_at`, `revocation_channel`,
`allowed_effects` — that the executor must check *outside* the
verifier call (the channel-active check is a live ledger lookup;
expiry is a height comparison). These can be modeled as `Custom`
predicates, but the resulting verifier becomes "verify the
delegation proof AND check expiry AND check channel AND check
facet" — the verifier accretes policy that's better factored as
explicit code paths.

**(c) The closed enum gives audit tools structural visibility per
`PREDICATE-INVENTORY.md §6.2`.** Today a cclerk rendering "this
turn is authorized by Signature" can decide UI based on a single
match arm. Under full subsumption it would render "this turn is
authorized by Custom { vk_hash: 0xabc… }" and require a registry
dereference to learn what 0xabc… *is*. That registry dereference
is fine if the descriptor is bundled with the variant — but at
that point you've reintroduced the structural shape, just under a
different name.

### §5.3. Decision: coexist

Recommendation: `Authorization::Custom` ships **alongside** the
existing variants. The platform retains its closed list of
mainline modes (`Signature`, `Proof`, `Breadstuff`, `Bearer`,
`CapTpDelivered`, `Unchecked`); `Custom` is the escape hatch.

This mirrors the slot-caveat decision in
`SLOT-CAVEATS-EVALUATION.md §6.2-§6.3` ("lifted-enum-first; ship
the named variants; keep `Custom` as the disciplined escape").
The reasoning carries: closed enums give AIR enforceability and
audit visibility; `Custom` covers what the closed set can't.

The migration path (§9) optionally deprecates dedicated variants if
their `Custom` equivalent proves more useful, but that's a v3
question, not v1.

---

## §6. Registry shape

What is the set of `vk_hash`es that may appear in `AuthModeDescriptor`
and `WitnessedPredicateKind::Custom { vk_hash }`?

Three candidate shapes, mirroring `PREDICATE-INVENTORY.md §6.2`.

### §6.1. Candidate: static enum

A closed `enum AuthModeKind { Multisig, DaoQuorum, TimeLock,
CapConditional, ComputeAttested, CredentialRing, … }` mirrors how
the existing `Authorization` variants are coded. Each kind has a
hardcoded verifier; new kinds require an enum addition (touches
every match arm).

Rejected: defeats the purpose of `Custom`. If `AuthModeKind` is
closed, app authors cannot register their own.

### §6.2. Candidate: trait-object polymorphism

Each kind is a `Box<dyn AuthVerifier>`. Maximally flexible. Rejected
for the same reason as in `PREDICATE-INVENTORY.md §6.2`:
`Authorization` is wire-serialized (it lives on Turns and Receipts);
trait objects don't trivially `Serialize + Deserialize`. The wire
shape must be data; the verifier is what the data names.

### §6.3. Candidate: `vk_hash`-keyed registry (chosen)

The exact pattern from `DESIGN-max-custom-effects.md`: every auth
mode is keyed by a 32-byte verifier-key hash. The
`AuthModeRegistry` resolves `vk_hash → AuthVerifier`. Two registry
tiers:

```rust
pub struct AuthModeRegistry {
    /// Platform-reserved vk_hashes (the canonical built-ins, if any
    /// of the explicit variants are also exposed as Custom for
    /// dual-encoding). Closed at compile time.
    builtins: BTreeMap<[u8; 32], &'static dyn AuthVerifier>,
    /// Federation-attested vk_hashes — auth modes the federation
    /// has admitted via a governance turn. Each entry's
    /// AuthModeDescriptor is on-chain.
    governance_attested: BTreeMap<[u8; 32], Arc<dyn AuthVerifier>>,
}

pub trait AuthVerifier: Send + Sync {
    fn verify(
        &self,
        commitment: &[u8; 32],
        signing_message: &[u8],
        proof_bytes: &[u8],
    ) -> Result<(), AuthVerifyError>;
    fn vk_hash(&self) -> [u8; 32];
    fn descriptor(&self) -> &AuthModeDescriptor;
}
```

The `governance_attested` map is the new piece. Per §8 below, the
discipline is that app-defined auth modes must be registered by a
governance turn — they cannot be self-registered by an action that
*uses* them. The chain of trust is: federation governance → registry
entry → individual turns using the mode.

The platform's built-in `WitnessedPredicateKind`s (`Dfa`,
`Temporal`, `MerkleMembership`, `BlindedMembership`,
`BridgePredicate`, `PedersenEquality`) each have a canonical
`vk_hash` registered as a builtin; `WitnessedPredicateKind::Custom
{ vk_hash }` routes through `governance_attested`.

### §6.4. Why mirror `Effect::Custom`

`DESIGN-max-custom-effects.md` argues for `Effect::Custom { vk_hash,
…}` as the apps-side effect-extension story. The `Authorization::Custom
{ predicate: WP { kind: Custom { vk_hash } }, descriptor }`
shape **mirrors that decision intentionally**: same registry tier
structure, same governance discipline, same wire shape (`vk_hash`
in the variant, descriptor in metadata). An app that adds a custom
effect and a custom auth mode uses the same registration ceremony
for both.

### §6.5. The "is the registry closed under cross-federation
agreement?" question

If federation F1 has `vk_hash = 0xabc…` registered to "multisig v2"
and federation F2 has `vk_hash = 0xabc…` registered to "credential
ring v1", a turn moving from F1 → F2 (via the bridge) carries
ambiguous authorization.

Per `EXECUTOR-HONESTY-AUDIT.md` T6, the canonical signing message
includes `federation_id` — so the proof is bound to F1. F2's
attempt to interpret it as a credential-ring proof will fail at
the verifier (the proof checks against the wrong commitment).
Soundness holds, but the user-experience is "your action looked
valid but isn't" — opaque.

**Recommendation:** `AuthModeDescriptor.vk_hash` should be **a
content-addressed hash of the verifier's canonical artifact**
(e.g., the verifier-key + auxiliary parameters), not an arbitrary
identifier. Then `0xabc…` *cannot* mean two different verifiers
across federations — collisions are computationally infeasible.
The naming becomes globally unambiguous.

This is the same discipline `SLOT-CAVEATS-EVALUATION.md §5.4(b)`
imposes for `StateConstraint::Custom { ir_hash, … }`: the hash is
of the canonical IR. Apply it here for the verifier artifact.

---

## §7. Replay semantics

Per `PREDICATE-INVENTORY.md §6.3` for `WitnessedPredicate` broadly:
**snapshot the commitment at receipt-time, replay against the
snapshot.**

For `Authorization::Custom`, this means the receipt carries:

1. The full `Authorization::Custom { predicate, descriptor }` variant
   (already part of the action, already part of the receipt — no
   change).
2. The `predicate.commitment` field — already in the variant.
3. The `witness_blobs[predicate.proof_witness_index]` — already
   part of the action and witness-bundle.
4. **New:** if `predicate.commitment` was resolved from external
   state at original verification time (a slot value, a
   peer-cell-attested root), the receipt's witness bundle must
   snapshot that source. This is the same `snapshot-the-source`
   discipline `WitnessedPredicate` uses generally
   (`PREDICATE-INVENTORY.md §6.3`); `Custom` inherits it without
   addition.

On replay:
- Replayer reads the receipt's `Authorization::Custom`.
- Looks up `descriptor.vk_hash` in *its* registry. If the verifier
  is not registered at the replayer, the replay fails closed —
  the replayer cannot independently verify and must either trust
  the federation that issued the receipt or refuse to replay.
- Calls `verifier.verify(commitment, signing_message, proof_bytes)`.
- The signing message is recomputed from the receipt's turn fields
  (same federation_id, same nonce, same action, same position).
- If verify accepts, the replay accepts this turn's authorization.

Replay-soundness is identical to the original verification: the
verifier is deterministic; the input is canonically recomputed;
the commitment is snapshotted. No new replay vulnerabilities
beyond what `WitnessedPredicate` already implies.

### §7.1. The "verifier not in replayer's registry" failure mode

This is *new*, compared to today's auth modes. Today every replayer
has hardcoded `Signature`, `Proof`, `Breadstuff`, `Bearer`,
`CapTpDelivered`, `Unchecked`. There is no failure mode for
"verifier not found at replay."

`Custom` introduces it. The receipt advertises which mode via
`descriptor`, so the replayer can give a useful error
(`UnknownAuthMode { descriptor: AuthModeDescriptor }`) instead of
opaque rejection — but the replay still fails closed.

**Operational consequence:** federations participating in cross-
federation replay (e.g., bridge counterparties) must agree on the
set of `vk_hash`es they will both honor, OR fall back to
`Custom`-free wire encodings for cross-federation traffic.

This is the same operational constraint `Effect::Custom` imposes
per `DESIGN-max-custom-effects.md`; `Custom` auth inherits it.

---

## §8. Threats and protections

Walk the threats in `EXECUTOR-HONESTY-AUDIT.md` and ask: does
`Custom` weaken any of them? Does it enable new ones?

### §8.1. T2 (forge effects)

Threat: executor adds an effect the actor didn't sign.

Defense under `Custom`: the predicate's input is the canonical
signing message, which is `H(federation_id, action.hash(), position,
turn_nonce)`. `action.hash()` covers `effects_hash`. An executor
that forges effects changes `effects_hash` → changes
`action.hash()` → changes the signing message → the proof no longer
binds to the message → verifier rejects.

Same protection as `Signature`. **`Custom` does not weaken T2.**

### §8.2. T6 (cross-federation replay)

Threat: take a turn signed for F1 and replay on F2.

Defense under `Custom`: the canonical signing message includes
`federation_id`. The proof binds to it. Replay on F2 fails at
the verifier.

**Provided** the canonical signing message construction does
include `federation_id` in the input fed to the predicate. The §2
flow specifies this. The executor implementation must be careful:
if a `Custom` verifier is implemented to ignore part of the input,
it could regress T6. Discipline: `AuthVerifier::verify` MUST accept
the full canonical signing message; partial-binding verifiers are
unsound. Document this in the trait's rustdoc.

### §8.3. T10 (skip permission check)

Threat: executor applies an effect the actor doesn't have caps for.

Defense under `Custom`: the descriptor's optional `allowed_effects`
mask, plus the per-effect cap-presence checks the executor already
does. `Custom` does not replace the cap-presence check; it
authorizes that the *condition* held, but cap-presence is a
separate gate.

**Custom does not weaken T10**, but app authors who confuse
"authorization" with "permission to do every effect" could ship
overly-permissive `Custom` modes. The discipline:
`AuthModeDescriptor.allowed_effects` is the maximum effect mask
the mode unlocks; the executor enforces it the same way it
enforces `BearerCapProof.allowed_effects`.

### §8.4. T11 (stale proof)

Threat: executor reuses an old proof against a new turn.

Defense under `Custom`: identical to today's `Proof` — the proof
binds to `turn_nonce` and `action.hash()` via the canonical
signing message. Old proof → wrong nonce → wrong message → wrong
public input → verifier rejects.

**Custom does not weaken T11.**

### §8.5. NEW T17 — unsound app-defined verifier

Threat (new): an app registers a `Custom` verifier that accepts
proofs it shouldn't (e.g., the verifier returns `Ok(_)` regardless
of `proof_bytes`). The executor consults the registry and accepts
any turn using this mode.

This is the most operationally important new threat. The discipline
is **who can register**.

- **Built-in modes (`builtins` tier).** Registered at compile time;
  audited as part of the platform; same trust as the platform code.
- **Governance-attested modes (`governance_attested` tier).**
  Registered via a federation-governance turn. The federation's
  governance cell signs the descriptor + verifier artifact, and
  the registry is populated as a side effect of that turn's
  execution. *No free registration.*

This means: registering a new `Custom` auth mode is itself a
governance act. Federations choose to admit them; users see the
admitted set via the descriptor's `authoring_package` field.

The threat is **bounded by the federation's governance**, not by
individual app authors. An app shipping an unsound verifier is no
more dangerous than the federation choosing to admit it; the
discipline is "the federation does not admit verifiers it has not
audited."

### §8.6. NEW T18 — verifier version drift

Threat (new): F1 admits `vk_hash = 0xabc…` as multisig-v2. F2
later admits `0xabc…` as a *patched* multisig-v2 with subtly
different acceptance semantics. Turns flowing F1 → F2 fail (or,
worse, pass under the new semantics when they should fail).

Defense: per §6.5, the `vk_hash` is content-addressed against the
verifier artifact. Patched semantics → different artifact →
different hash. The two federations have to register a *new*
`vk_hash` for the patched version; the descriptor's `semver` makes
this visible.

The audit trail is: every `vk_hash` is unique to one verifier
implementation; semver bumps are observable; cross-federation
agreement requires version-equality, not just `vk_hash` equality
(those are the same statement under content addressing).

### §8.7. NEW T19 — descriptor lies

Threat (new): the descriptor advertises `boundary_contract.cleartext_inside =
"the K signers"` but the actual verifier reveals more
(e.g., it requires PI to include all N signer identities, breaking
the "K-of-N anonymity" claim).

Defense: the descriptor is **advertising**, not enforcement. Audit
discipline is required to verify the verifier behaves as advertised.
Per `BOUNDARIES.md §5.2`, the descriptor is editorial.

This is *not* a soundness threat — turns still execute correctly
— it's a **privacy mis-claim** threat. The mitigation is the same as
for any privacy mis-claim: third-party audit of the verifier; the
auth-mode admission process should require it.

### §8.8. NEW T20 — registry-fork attack

Threat (new): a malicious federation member gossips a forged
registry update that adds an attacker-controlled verifier.

Defense: registry updates are governance turns. They are signed,
they appear in the chain, they are subject to federation quorum.
A forged update is a quorum-bypass attack — a much larger threat
than "Custom-specific."

`Custom` does not introduce a quorum-bypass vector that doesn't
already exist for any governance-attested registry (effects,
predicates, etc.).

---

## §9. Migration path

Three phases, ordered by risk and value.

### §9.1. Phase 1 — add the variant, no app usage

Land `Authorization::Custom { predicate, descriptor }` alongside the
existing variants. The executor gains the §2 verification arm. No
apps use it; no built-in modes are pre-registered.

Tests: positive cases stub a trivial `AuthVerifier` (e.g., always-pass,
or "verifier accepts iff input == known constant"). Negative cases:
unregistered `vk_hash` rejects; verifier-error rejects;
descriptor-kind-mismatch rejects.

This phase is **invisible to apps**. Nothing breaks; nothing changes
on the wire for existing turns. The variant is dormant until a
governance turn registers an auth mode.

### §9.2. Phase 2 — register one or two app modes

Pick two apps from §3:

- **`compute-exchange`** registers a `temporal_unlock_v1` auth mode
  for time-locked turn release (§3.3).
- **`dregg-multisig` (new factory)** registers `kof_n_multisig_v2`
  for multisig auth (§3.1).

Each requires:
1. The verifier implementation (verified in-tree).
2. The descriptor (human-readable name + semver + boundary
   contract).
3. A governance turn admitting the mode to the federation registry.
4. App-side tooling to construct `Authorization::Custom` with the
   right predicate.

The two apps validate the registry / governance / cclerk-construction
path end-to-end. No platform-level commitment to deprecating
existing variants yet.

### §9.3. Phase 3 — optional collapse

If Phase 2 proves the discipline works, evaluate collapse:

- **`Authorization::Multisig`** (hypothetical, never landed) — *don't
  land*; use `Custom`.
- **`Authorization::Breadstuff`** — could collapse to a `Custom` with
  a `cap_token_lookup_vk` verifier. But: `Breadstuff` is two
  bytes overhead vs. the full `Custom` envelope; the collapse is a
  size regression for the breadstuff-heavy workloads. **Don't
  collapse.**
- **`Authorization::Bearer`** — could collapse to `Custom { kind:
  Custom { vk_hash: bearer_cap_air_vk }, descriptor: …, … }`. But
  the bearer-policy (channel, expiry, facet) is special-cased in the
  executor (`turn/src/executor.rs:4383-4429`); collapsing requires
  encoding that policy into the verifier or into descriptor flags.
  Net win is structural cleanliness; net cost is a wire-format
  bump and a verifier with policy accretion. **Don't collapse in
  this lift; reconsider when bearer-v2 lands.**
- **`Authorization::CapTpDelivered`** — same as Bearer, but more so:
  the cert + signature dual is bespoke. **Don't collapse.**

The honest answer: **`Custom` lives next to the explicit variants
indefinitely.** Phase 3 is a hypothetical that should not be
scheduled.

### §9.4. What never migrates

- `Authorization::Unchecked` — by design, the audit-flagged
  no-auth path (`AUDIT-protocol-composition.md §9.1`).
  Collapsing it to `Custom { … kind: Custom { vk_hash:
  zero_predicate } }` *hides* the regression risk. Keep `Unchecked`
  loud and grep-able.
- `Authorization::Signature` — the most-used variant. Collapsing
  the wire shape regresses every signed turn. Keep.

---

## §10. Open questions

Hard calls the designer should make.

### §10.1. Does `AuthModeDescriptor` belong on the wire?

The descriptor is non-trivial (~200 bytes when including the boundary
contract strings). Three options:

- **(a) Full descriptor on wire** (proposed in §1). Verbose, but
  receipts are self-describing.
- **(b) Descriptor-by-reference.** The wire carries `descriptor_hash:
  [u8; 32]`; the descriptor lives in a federation-wide table. Costs:
  one indirection per turn rendering; receipts lose self-describability.
- **(c) Descriptor in registry only.** The wire carries only
  `vk_hash`; the descriptor is in the registry. Costs: descriptor is
  not on the receipt, so cipherclerks must consult the federation to
  render the auth mode.

Recommendation: **(c) for wire, (a) for receipt-display tooling.**
The wire carries `vk_hash` only (we already pay 32 bytes); the
cipherclerk's UI fetches the descriptor from the registry to render.
Receipts are dense; rendering is a UI concern.

This contradicts §1's strawman. Revise: `Authorization::Custom {
predicate: WitnessedPredicate }` — no descriptor field on the wire.
The descriptor lives in the registry, keyed by `predicate.kind`'s
`vk_hash` (for `Custom`-kind) or the canonical kind-hash (for
builtins). Tooling fetches via `AuthModeRegistry::descriptor_for`.

### §10.2. Are app-defined verifiers in-circuit?

Today's `Authorization::Proof` calls a STARK verifier; that's a STARK
proof. App-defined `Custom` verifiers could be:

- (a) STARK proofs that conform to a known AIR shape (the registry
  entry is the AIR).
- (b) Arbitrary code (the registry entry is a `Box<dyn AuthVerifier>`).
- (c) DSL-described predicates compiled to a known AIR family.

Recommendation: **(c) for federation-registered, (b) for testing,
(a) for the eventual default.** The DSL-described path
(`dregg-dsl/src/temporal.rs` is the existing precedent) gives the
strongest cross-implementation determinism.

This needs alignment with the slot-caveat / `WitnessedPredicate` IR
canonicalization story (`SLOT-CAVEATS-EVALUATION.md §5.4(b)`).
Same IR; same hash story.

### §10.3. Can `Custom` carry multiple proofs?

The §1 shape has one `proof_witness_index: u8` — one proof per
`Custom` authorization. What if the auth requires two coupled proofs
(e.g., multisig + temporal unlock)?

Recommendation: **no**. Use `Preconditions::witnessed: Vec<WP>` for
the second clause; `Authorization::Custom` carries the principal
authorization, preconditions carry the rest. Mirrors the §3.7
non-decision.

### §10.4. Should `Authorization::Custom` enable the action's
permission-check?

Today `to_auth_kind` (`turn/src/action.rs:211`) maps signature/proof
to `AuthKind::Signature` / `AuthKind::Proof`. Permission checks
ask: is this action's auth kind sufficient for the cell's required
auth? E.g., `AuthRequired::Signature` accepts `AuthKind::Signature`;
`AuthRequired::Proof` accepts both.

For `Custom`, what does the lattice look like?

Two options:

- (a) `Custom` maps to its own `AuthKind::Custom { vk_hash }`. The
  cell's `permissions.for_action(…)` would have to list which
  `vk_hash`es it accepts. New first-class lattice elements per mode.
- (b) `Custom` does not participate in the lattice; the cell instead
  declares `AuthRequired::Custom { vk_hash }` to require a specific
  auth mode. The cell decides which modes are acceptable; the
  action either matches or doesn't.

Recommendation: **(b)**. Cells that want a custom auth declare
*specifically* which mode they want. Cells that don't care continue
using `AuthRequired::Signature` / `Proof` and ignore `Custom`. The
lattice stays narrow; mode-specificity is a cell-level decision.

Action: extend `dregg_cell::AuthRequired` with
`Custom { vk_hash: [u8; 32] }`. The cell's permissions can demand
"this action's authorization must be `Authorization::Custom` with
predicate.kind's hash equal to vk_hash."

### §10.5. Does `Custom` interact with sovereign witnesses?

Sovereign cells already have a witness-attached transition
(`SovereignCellWitness`, `turn/src/turn.rs:22-30`). A `Custom` auth
on a sovereign-cell turn means *two* proofs: the sovereign witness
(transition validity) and the custom auth (who-can-do-this).

This is fine — they're orthogonal: transition validity is "did the
state machine accept the transition"; auth is "is this caller
authorized to drive a transition." Two independent verifier calls,
two independent registry lookups, no coupling.

Open: does the AIR need to constrain that *the auth predicate
accepted* before *the transition is honored*? Today the executor
does this in serial (auth check first; transition apply second).
Algebraic binding (`SLOT-CAVEATS-DESIGN.md` Phase 5 analog) is
future work.

### §10.6. What about `Authorization::Custom` on cross-federation
bridge turns?

The bridge already has its own auth story (`PortableNoteProof`
spending proof + `AttestedRoot` cross-federation cert). A `Custom`
auth on a bridge turn would have to interact with the bridge's
cross-federation binding. Open question: do we even allow it?

Recommendation: **defer**. Bridge turns use bridge-specific
auth (today's path) until a concrete app demands cross-federation
`Custom`. The bridge is a privileged subsystem; opening it to
arbitrary `Custom` verifiers expands the trust surface.

### §10.7. Hash-format vs CBOR-format `descriptor` in the registry

The registry stores `AuthModeDescriptor`. Wire format: postcard?
JSON? CBOR? This is the same question `Cell` metadata answers
(postcard); align with that. Not interesting per se; recording
the decision for completeness.

### §10.8. Cost-table calibration

The §2.1 cost entries are gestures. Real numbers depend on the
specific verifier — temporal predicates over 100-step traces are
slower than 64-byte Ed25519. Calibration is a benchmarking task,
not a design call. Document the *shape* (per-kind cost) and
calibrate when each mode lands.

### §10.9. Should existing variants be dual-encoded as `Custom`?

Could `Signature` be available as *both* `Authorization::Signature(r, s)`
and `Authorization::Custom { … kind: Custom { vk_hash: ed25519_canonical } }`?

Recommendation: **no, ship a single canonical encoding per mode.**
Dual-encoding invites canonicalization bugs: two different bytes
can decode to "the same authorization"; equality checks must
canonicalize first; receipt-hash stability gets harder. Pick one;
the explicit variant wins for the built-ins.

---

## §11. Relationship to slot caveats

The two systems use the same `WitnessedPredicate` vocabulary but in
opposing roles.

### §11.1. Slot caveats: invariants on state

`StateConstraint::Witnessed(WP)` (per `PREDICATE-INVENTORY.md §3.5`)
asks: **given a (old_state, new_state, ctx), does the predicate
hold?** The predicate is an invariant evaluated at every
state-modifying effect; its truth conditions are "the state
transition has the right shape." A WP slot caveat might say
"every new value at slot 0 must satisfy a DFA acceptance over a
route table."

The slot caveat fires *during effect application* — after the
authorization gate has already passed.

### §11.2. Authorization: who-can-do-this-now

`Authorization::Custom { predicate, … }` asks: **given the action's
canonical signing message, does the predicate accept?** The
predicate witnesses an authorization condition; its truth condition
is "the caller is entitled to act."

The auth predicate fires *before any effect applies* — the gate is
"are you allowed to drive this transition at all."

### §11.3. Same vocabulary, different roles

The shared `WitnessedPredicate` shape (kind + commitment + input_ref
+ proof_witness_index) is identical. What changes is **what
`input_ref` resolves to**:

- For slot caveats, `input_ref` resolves to `slot_n`, a witness blob,
  or PI — values about the transition.
- For `Custom` auth, `input_ref` resolves to the canonical signing
  message bytes. (Strictly: a *new* `InputRef::SigningMessage`
  variant or equivalent — see §11.5.)

A predicate could in principle be used for either role — but a
sensible verifier is purpose-built for one. The role determines
which inputs are bound.

### §11.4. Composition: auth-as-caveat-on-action

What about a slot caveat that says "this state transition is only
valid if the action was authorized by mode X"? That's the
**composition** — but it's redundant with the auth gate, because the
auth gate already prevents non-X turns from reaching the effect-
application stage. The slot caveat would never observe the
"unauthorized turn" case (it's rejected earlier).

So `Custom` auth and `Witnessed` caveats compose by *layering* in
the executor pipeline (auth first → caveats second), not by
embedding one inside the other.

### §11.5. New `InputRef::SigningMessage`?

Per `PREDICATE-INVENTORY.md §3.2`, `InputRef` has variants
`Slot { index }`, `Witness { index }`, `PublicInput { pi_index }`,
`Sender`. For `Custom` auth, the input is "the canonical signing
message bytes."

Three options:

- (a) Add `InputRef::SigningMessage` — explicit, type-safe, matches
  the new role.
- (b) Encode the signing message as a `Witness` blob — generic, but
  loses the "this is the canonical message" structural marker.
- (c) Encode the signing message as a public input — most flexible,
  but requires the verifier's AIR to expose a signing-message PI
  position.

Recommendation: **(a)**. Auth's signing-message-as-input is a
first-class role; mark it as such. The executor's call to the
verifier passes a `PredicateInput::SigningMessage(&[u8])` rather
than reaching into a witness blob.

This is the one structural lift `Custom` requires in
`WitnessedPredicate` proper. It's small and self-contained.

### §11.6. Replay-side asymmetry

For slot caveats, the predicate's input is in cell state (slot
values) — already part of the chain replay. No new replay carry.

For `Custom` auth, the predicate's input is the signing message —
also already in the chain (the canonical message is computable
from the turn). No new replay carry.

Both roles are replay-friendly; the snapshot discipline from
`PREDICATE-INVENTORY.md §6.3` applies uniformly.

### §11.7. The economic case

The same registered verifier (a kind in the registry) can be reused
for both roles:

- A `temporal_dsl_v1` verifier registered once serves:
  - `StateConstraint::Witnessed(WP { kind: Temporal, … })` for slot
    caveats with temporal invariants.
  - `Authorization::Custom { predicate: WP { kind: Temporal, … } }`
    for temporal-unlocked auth.

One verifier; two roles. The registry is therefore the *only* place
the kind exists; the surface where it's invoked decides what input
it sees.

This is the load-bearing reason to share the vocabulary: every
verifier the platform ships is multi-role.

---

## §12. Summary and recommendation

`Authorization::Custom` is the natural extension of
`WitnessedPredicate` into the authorization role. The variant ships
with one shape:

```rust
Authorization::Custom { predicate: WitnessedPredicate }
```

routed through the same `AuthModeRegistry` shape as
`Effect::Custom`'s vk_hash registry. The descriptor lives in the
registry, not on the wire. The verifier's input is the canonical
signing message (new `InputRef::SigningMessage` to mark the
structural role).

The variant **coexists** with the explicit variants. Subsumption
hurts more than it helps:
- Primitives like `Signature` and `Breadstuff` lose their efficient
  encoding.
- Policy-laden variants like `Bearer` and `CapTpDelivered` accrete
  policy into verifiers, hiding it from the executor.
- The closed enum gives audit tools structural visibility that
  subsumption regresses.

The migration path is two phases (variant first; one or two apps
register modes), with the optional collapse phase being a
hypothetical to defer indefinitely.

Threat coverage carries forward from the existing variants because
the predicate's input is the canonical signing message — every
binding `Signature` enjoys, `Custom` enjoys. The new threats
(unsound app verifier, registry fork, descriptor lies) are
**governance-bounded**: app authors don't self-register; federations
admit modes via governance turns; the chain of trust runs from the
federation outward.

The recommendation: **land Phase 1 alongside the
`WitnessedPredicate` lift; pilot one app's `Custom` mode in
Phase 2 (compute-exchange's temporal unlock is the cleanest
candidate); leave the explicit variants in place; never schedule
Phase 3.**

---

## Cross-references

- `PREDICATE-INVENTORY.md` — `WitnessedPredicate` vocabulary
  (§3-4 of this doc).
- `SLOT-CAVEATS-DESIGN.md` — slot-caveat enum shape; the model
  for "ship closed enum first, defer DSL".
- `SLOT-CAVEATS-EVALUATION.md` — `Custom` discipline
  (§5.4 — adopted here for `AuthModeDescriptor`).
- `BOUNDARIES.md` — boundary contract vocabulary (§4 above).
- `AUDIT-protocol-composition.md` — current `Authorization` shape;
  `Unchecked` regression risk.
- `EXECUTOR-HONESTY-AUDIT.md` — T2/T6/T10/T11 (§8 above).
- `DESIGN-max-custom-effects.md` — the `Effect::Custom` vk-hash
  registry shape that `Authorization::Custom` mirrors.
- `EFFECT-VM-SHAPE-A.md` — compute-attested auth (§3.5)
  feasibility.
