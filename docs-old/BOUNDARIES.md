# BOUNDARIES.md — what's inside, what's outside, and what enforces it

**Date:** 2026-05-24. **Status:** study/design lane. Read-only on code.
**Companion audits:** `AUDIT-privacy.md`, `AUDIT-distributed-semantics.md`,
`AUDIT-protocol-composition.md`, `AUDIT-federation.md`,
`AUDIT-blocklace-consensus.md`, `AUDIT-nullifiers.md`,
`AUDIT-sovereign-witness-teeth.md`, `CELL-CRATE-REVIEW.md`,
`STAGE-7-GAMMA-2-PI-DESIGN.md`, `STARBRIDGE-APPS-PLAN.md`,
`WITNESSED-RECEIPT-CHAIN-DESIGN.md`.

The designer asked: in cryptographic distributed systems there is a
fundamental tension between participants *inside* (who know things by
construction) and participants *outside* (who can only see or verify
certain things). In dregg, where is that boundary? Is it implicit?

The honest answer is: the boundary is **implicit, plural, and
sometimes inconsistent**. There is no single declaration in the code or
the docs of who knows what. Multiple boundaries coexist; they
sometimes contradict; the codebase has been growing privacy-preserving
primitives at the periphery faster than it has been declaring,
centrally, who they exclude. This document does not propose a new type
system. It *names* the boundaries dregg already has, declares for each
subsystem who's inside, who's outside, and what primitive enforces the
boundary, and surfaces the inconsistencies.

The intent of this doc is descriptive, not prescriptive. The
codebase's value proposition includes a lot of correctly-built
primitives; the value at risk is that callers (apps, agents,
verifiers, the designer themself) may form mental models that don't
match the algebra. Naming the boundary is a precondition to noticing
when it slips.

---

## §1. The general tension

Cryptographic distributed systems are organised around two
populations: those who know a datum **by construction** (because they
generated it, they hold a private key, they were one of the signers,
they're in the committee, they ran the prover) and those who can only
relate to that datum through some interface — verify a signature,
check membership in a set, decode a ciphertext, accept a proof. The
former we'll call *inside*; the latter *outside*. The boundary is the
predicate that decides who's which.

This formulation has a long pedigree. Each of these is the same
question with different filling:

- **Zcash shielded pools** — note holders are inside the shielded
  pool; everyone else sees only commitments and nullifiers. The
  enforcing primitive is the *spending key* and the proof of
  knowledge thereof under Groth16. (Cf. Hopwood et al., the Zcash
  protocol specification.) Outsiders verify; insiders generate.
- **E-cash and blind signatures** — the holder of a coin (a signed
  random serial) is inside; the bank that issued the coin and the
  merchants who accept it are outside. The boundary is enforced by a
  blind-signature scheme. (Chaum 1982.)
- **Secure multi-party computation** — the protocol participants are
  inside the computation (each holds a share of the input); the
  output is published outside. The enforcing primitive is secret
  sharing + share-revelation. (Goldreich-Micali-Wigderson.)
- **Threshold signatures** — the committee members are inside the
  signing relation; anyone who verifies a signature is outside. The
  enforcing primitive is the joint algebra of the secret shares
  (Shamir + DKG, or for dregg, the per-party BLS keys composed via
  weighted-threshold aggregation).
- **Object capabilities and the E language** — only the holder of a
  reference is *inside* the right to invoke; reference unforgeability
  in the runtime enforces the boundary. Outsiders lack the reference
  entirely; there is no public namespace. (Miller's *Robust
  Composition*.)
- **Mix networks and onion routing** — inside a mix-circuit, each hop
  knows its predecessor and successor; outside the mix, an observer
  learns only the entry and exit aggregate distribution. The
  enforcing primitive is layered encryption + reordering.

The shared shape is that *the boundary is a predicate over knowledge*.
Inside means "has the secret, the key, the share, the proof witness,
or the runtime-unforgeable reference." Outside means "has only what
the primitive lets through" — usually a commitment, a verification
key, or a yes/no acceptance signal.

In a system like dregg, which tries to combine a dozen of these
primitives in one substrate, the question "where is the boundary"
fractures: there is one for each subsystem, and they are not always
nested. The rest of this document walks each one.

---

## §2. `dregg`'s boundaries (enumerated)

Each subsection states the boundary, who's inside, who's outside, the
enforcing primitive, the code site, and the failure mode if the
boundary is violated. We start with the boundaries that are most
load-bearing in production today and proceed outward.

### §2.1. Federation membership

**Boundary.** Who is a member of a given dregg federation (committee)
versus who is not.

**Inside.** The participants whose BLS keys are aggregated into the
committee's threshold key. They can each sign their share; they each
hold a regular BLS keypair (no DKG, no Shamir splitting). When a
supermajority sign over a body, they produce a `ThresholdQC` whose
BLS aggregate is constant-size (one G2 element + a tiny KZG witness).

**Outside.** Anyone with the committee's verifier key. They can
verify a `ThresholdQC` over a message; they cannot produce one. They
do not learn which members signed (the aggregate is anonymising
within the committee).

**Enforcing primitive.** Weighted-threshold BLS aggregate over
BLS12-381 with KZG-attested weights. Lib: `hints/` (real
`ark_bls12_381` pairing, real `hash_to_g2`, KZG via Ethereum trusted
setup or `OsRng` for tests). Aggregation: `FederationCommittee` at
`federation/src/threshold.rs:37`. Verification:
`committee.verify(qc, msg)` at `federation/src/threshold.rs`.
Constant-size attestation tested at line 482.

**Where in code.** `federation/src/threshold.rs`,
`federation/src/receipt.rs:122-227`, `federation/src/checkpoint.rs`,
`hints/src/lib.rs`, `hints/src/snark/mod.rs`.

**Failure mode.** A non-member who somehow obtained a member's BLS
secret can produce a share. The aggregate-verification still requires
threshold members (and the KZG attestation of weights) to compose,
but compromise of `f` members enables corruption proportional to
their weight. There is **no slashing**, no expel-on-equivocation
inside `federation/` — see `AUDIT-federation.md §9`. Equivocation is
detected at the *blocklace* layer (constitution.rs auto-eviction),
which is structurally a different boundary (§2.10).

**Inconsistency to name.** `federation_id` is currently a random
16-byte token (`node/src/genesis.rs:53-55`), not a commitment to the
committee. The pair `(federation_id, committee)` is conventional, not
algebraic. A `FederationReceipt::verify` call takes a `committee`
parameter and never checks `committee ↔ federation_id`. This is
`AUDIT-federation.md` finding F1; it means an outside-the-committee
party who can route a receipt could mislabel its `federation_id` and
the algebra would not notice. Lane D's fix derives
`federation_id = BLAKE3(committee_verifier_key, committee_epoch)`.

### §2.2. Cap-holder vs non-holder (swiss-number gating)

**Boundary.** Holders of a sturdy reference (a `DreggUri` containing a
swiss number) can enliven a capability; non-holders cannot.

**Inside.** Anyone in possession of the swiss bytes. The trust model
is bearer: "possession IS authorization" — `captp/src/lib.rs:11-13`.

**Outside.** Everyone else. Without the swiss bytes, no enliven path
succeeds.

**Enforcing primitive.** 32-byte unforgeable swiss number, registered
in a per-cell `SwissTable`, looked up at enliven time.
`SwissTable::enliven` at `captp/src/sturdy.rs:159-182`. No signature
check, no proof — just possession.

**Where in code.** `captp/src/sturdy.rs`, `captp/src/uri.rs:71-77`,
`wire/src/server.rs:2333,2350` (enliven handler),
`sdk/src/captp_client.rs:300-322` (the warning about
caller-supplied permissions).

**Failure mode.** Bearer secrets in a backup, log, pcap, or QR-photo
are bearer-equivalent forever (until the underlying swiss is
revoked). There is no rotation, no per-session derivation, no
forward secrecy. Any third party who *ever* sees the swiss bytes can
enliven from any host.

**Inconsistency to name.** The boundary is *not* the same as
"is this party in the federation that hosts the cell." A swiss-only
enliven goes through whichever node has the swiss table; cross-fed
routing is absent (`AUDIT-distributed-semantics.md §6`). The
boundary "this cell's authority is exercised by holders" is
substrate-thin: the swiss bytes are the boundary, and the boundary
mechanism does not know what federation it's enforcing for.

### §2.3. Turn-author vs observer (STARK soundness)

**Boundary.** Who actually witnessed the private state and effects of
a turn versus who only verifies a proof of it.

**Inside.** The actor — the holder of the cipherclerk's spending key, the
holder of the cell's preimage state, the prover with witness access
to the trace.

**Outside.** Anyone who later verifies the STARK proof against the
turn's public inputs. They learn nothing about the private columns of
the trace (the witness); they learn only that *some* witness existed
satisfying the AIR's constraints.

**Enforcing primitive.** STARK soundness. BabyBear + FRI; AIR is
`EffectVmAir` (`circuit/src/effect_vm.rs`). Public inputs include
`OLD_COMMIT`, `NEW_COMMIT`, `EFFECTS_HASH`, balance bookkeeping,
`TURN_HASH`, `EFFECTS_HASH_GLOBAL`, `ACTOR_NONCE`,
`PREVIOUS_RECEIPT_HASH`. Post-quantum (FRI), but only at the
*credential-presentation* level; the value commitments are
Pedersen-Ristretto and the seals are X25519 (i.e. **not**
post-quantum).

**Where in code.** `circuit/src/effect_vm.rs`,
`circuit/src/effect_vm/pi.rs`, `node/src/mcp.rs:181-215`
(`generate_effect_vm_proof`), `turn/src/witnessed_receipt.rs`,
`turn/src/executor.rs:3131-3249` (the proof-carrying path).

**Failure mode.** A buggy prover that emitted a valid-looking proof
for the *wrong* trace would silently widen the inside (because the
verifier would accept it). STARK soundness means this is
cryptographically infeasible at the level the AIR constrains, but it
is *not* infeasible at the level the AIR *does not* constrain — and
the audits surface multiple cases where the AIR does not constrain
something the docs claim: `destination_federation` is in the PI but
no constraint binds it (`AUDIT-nullifiers.md §5`); sovereign
witnesses have no PI slot (`AUDIT-sovereign-witness-teeth.md §3`);
cross-cell binding between per-cell proofs is non-algebraic today
(`AUDIT-protocol-composition.md` seam 9, addressed by
`STAGE-7-GAMMA-2-PI-DESIGN.md`).

**Inconsistency to name.** The boundary "the proof tells the verifier
only the public outputs" is honest at the AIR layer, but the
**`WitnessBundle` is shipped alongside** for scope-2 replay
(`WITNESSED-RECEIPT-CHAIN-DESIGN.md` §2). That bundle contains the
full trace — i.e. the bundle audience and the proof audience are
different populations, and there is no current membership predicate
on the bundle (`§3.4` below).

### §2.4. Sealed message recipient vs world

**Boundary.** Who can decrypt a sealed message (a `SealedBox`).

**Inside.** Holder of the `unsealer_secret` X25519 private key.

**Outside.** Anyone else, including someone who saw the box on the
wire, someone who knows the recipient's `SealerPublic`, the wire/TLS
intermediaries, the federation node. They learn that *a* seal
happened, addressed to *that* `pair_id`, of *that* size, at *that*
time — but not the plaintext.

**Enforcing primitive.** X25519 ephemeral DH + ChaCha20-Poly1305
AEAD + BLAKE3-derive_key KDF + a BLAKE3 commitment binding (cap_hash,
ephemeral_public, nonce). Per-message ephemeral sender keypair gives
sender-side forward secrecy (per message, not per session); the
recipient's static `unsealer_secret` is the long-term secret.
Definition at `cell/src/seal.rs`.

**Where in code.** `cell/src/seal.rs:57-70` (struct), `:169-192`
(seal), `:212-217` (verify_seal). Plus the corresponding
`AUDIT-privacy.md §3.1` walk-through.

**Failure mode.** Compromise of `unsealer_secret` decrypts *all
prior* sealed boxes to that pair (no forward secrecy on the
recipient side). `pair_id` (line 60-61) deterministically identifies
the recipient — anyone who has seen the `SealerPublic` can link
every seal to that recipient. The size of the ciphertext is not
padded; timing is not randomised.

**Inconsistency to name.** The trust-model bullet
"forward secrecy" in `README.md` reads as session-level FS. It is
not: it is per-message sender-ephemeral FS only. Compromise of the
recipient's static key reveals all prior content.

**Inconsistency #2 — `allowed_effects` round-trip.** The sealed
plaintext encodes the inner `CapabilityRef`'s breadstuff +
expires_at but **does not encode `allowed_effects`**
(`CELL-CRATE-REVIEW.md §seal.rs`). Sealing a faceted cap
(`FACET_TRANSFER_ONLY`) and unsealing it produces an *unfaceted*
cap. This widens the inside on unseal. The boundary "you can unseal"
implicitly includes "you receive an unfaceted cap," which is not
what callers intend.

### §2.5. Cell state field visibility — `FieldVisibility`

**Boundary.** `cell/src/state.rs:13-26` defines
`FieldVisibility::{Public, Committed, SelectivelyDisclosable}`.

**Inside (Cleartext).** The federation node — i.e. **the hosted-cell
executor sees every field in cleartext**. The visibility flag is a
parallel array that controls only what `public_field_view()` returns
to external readers. Cell state lives as a
`[FieldElement; STATE_SLOTS]` of 32-byte values, written by index in
tight executor loops (`turn/src/executor.rs:4640-4641`,
`cell/src/state.rs:42-43`).

**Outside (Commitment-inside).** Anyone querying the public state
view of a `Committed` field sees a 32-byte hash, not the value. For
`SelectivelyDisclosable`, the hash plus a future per-predicate ZK
opening.

**Outside (Out-of-band).** Network observers see only whatever
crosses the wire.

**Enforcing primitive.** `public_field_view` at
`cell/src/state.rs:286-291`. The commitment-side primitive is
BLAKE3 (cleartext) and Poseidon2 (in-circuit). The hash + visibility
flag are advisory — the cleartext lives in the array next to them.

**Where in code.** `cell/src/state.rs:13-49, 286-291`,
`turn/src/executor.rs:4640-4641`.

**Failure mode.** Anyone who reads the executor's memory (or its
process logs, or its persistent ledger db) reads cleartext for every
field, regardless of the visibility tag. The visibility tag is a
**publication policy**, not a confidentiality primitive.

**Inconsistency to name.** This is the most common misreading of
dregg's privacy story. `FieldVisibility::Committed` reads as
"hidden field." It is hidden from **external readers via
`public_field_view`** — and only there. The executor, the host node,
and anything mid-pipeline with ledger-read authority all see
cleartext. Documented honestly at `cell/src/state.rs:42-43`
(comment: *"`fields[]`, `field_visibility[]`, and `commitments[]`
remain public arrays because the executor mutates them by index in
tight loops"*), but easy to miss.

### §2.6. Sovereign cell holder vs host executor — intended vs implemented

**Boundary (intended).** A sovereign cell *holder* knows the cell's
preimage state and proves transitions; the federation node holds
only the 32-byte commitment.

**Boundary (implemented today, witness path).** The host *executor*
sees the cell's full state every time a sovereign turn is
submitted, because the witness path injects the cleartext cell
state into the hosted ledger for the duration of the turn.

**Inside (intended).** The cell owner / agent. The federation holds
only `sovereign_commitments[cell_id] = [u8; 32]`.

**Inside (implemented).** Both: the agent (who provides the
witness) and the executor (which receives the witness as
`SovereignCellWitness { cell_state, state_proof }` and applies it
to the in-memory hosted ledger before forest execution —
`turn/src/executor.rs:3258-3330`).

**Outside.** Network observers, other federations, off-process
verifiers. They see only the post-commitment.

**Enforcing primitive (intended).** STARK proof binding
`OLD_COMMIT == sovereign_commitments[cell_id]` and
`NEW_COMMIT == turn.execution_proof_new_commitment`, plus the rest
of `compute_turn_identity_pi`. This is the *proof-carrying* path at
`turn/src/executor.rs:3131-3249`, which has algebraic teeth and
genuine executor-blindness.

**Enforcing primitive (implemented today, default path).** The
witness path. `SovereignCellWitness` is a preimage opener: the agent
sends the full `cell_state` along with the turn, and the executor
checks `cell_state.state_commitment() == stored_commitment` (step 3
of the four-check list at `AUDIT-sovereign-witness-teeth.md §2`).
No signature, no actor-binding, no AIR involvement, no PI slot for
sovereign witness.

**Where in code.** `turn/src/turn.rs:22-30` (`SovereignCellWitness`),
`turn/src/executor.rs:3258-3330` (witness path),
`turn/src/executor.rs:3131-3249` (proof path).

**Failure mode.** In the witness path, a malicious executor can
re-execute the effects however it wants — the AIR does not
constrain anything, and the post-state is computed by the executor
itself. The post-state commitment is honest by construction (the
executor recomputed it), but the *authorisation of the transition*
is not bound to the agent. Documented at
`AUDIT-sovereign-witness-teeth.md §4` (comparison with
`PeerStateTransition`, which DOES carry a signature, sequence
number, and optional STARK).

**Inconsistency to name.** This is the boundary the designer
mentioned in the prompt: the intended boundary is "host executor
doesn't see cleartext"; the implemented boundary is "host executor
sees cleartext during the witnessed turn, but doesn't persist it."
The *value* of being sovereign in the witness path is therefore
"the federation does not store your state," not "the federation
does not learn your state." Lane P and the soundness sweep are
addressing this (proof-carrying default, witness path retired).
The peer-exchange analogue is structurally stronger; the sovereign
witness is the weakest form of state attestation in the codebase.

### §2.7. WitnessedReceipt scope-1 vs scope-2

**Boundary.** Who holds the proof+PI alone (scope 1) versus who
additionally holds the trace bundle to re-derive scope 2.

**Inside (scope 1, proof-only audience).** Anyone with
`(proof_bytes, public_inputs, air_name)`. They can call
`dregg::verifier::verify_effect_vm_proof` and accept/reject.

**Inside (scope 2, trace replay).** Anyone with the proof + the
`WitnessBundle` (trace rows + witness_hash). They can re-derive the
trace, recompute PI, and re-prove from scratch. They learn the
private trace columns.

**Outside.** Anyone without either.

**Enforcing primitive.** STARK proof for scope 1; the
`WitnessBundle` (trace_rows + witness_hash) for scope 2.
`turn::WitnessBundle::inline_from_trace` in
`node/src/mcp.rs:201-203`.

**Where in code.** `WITNESSED-RECEIPT-CHAIN-DESIGN.md`,
`turn/src/witnessed_receipt.rs`,
`node/src/mcp.rs:181-215` and surrounding generators.

**Failure mode.** There is **no membership predicate on scope-2
audience today**. The `WitnessedReceipt` is a JSON artifact;
anyone who has the file has scope-2. The design doc names this
explicitly: "the user is not asking for universal third-party
replay; they are asking for a sufficient artifact for someone we
choose to trust later." The choice of who to trust is operational,
not cryptographic.

**Inconsistency to name.** The proof's "inside" (the prover, the
trace witness) and the bundle's "inside" (anyone with the bundle
file) are different populations. The proof's audience is potentially
everyone (verifier-side, public PI); the bundle's audience is
the prover plus whoever the prover chose to share with. No
mechanism enforces or even names this.

**Reframe (2026-05-25).** Per `HOUYHNHNM-COMPARISON.md`'s closing
insight, the WitnessedReceipt chain *is* dregg's canonical persistence
stream — not an auxiliary observability log. State is *derived* from
the receipt stream; the persistent database (`dregg_persist`) is a
cache. This reframes the scope-1/scope-2 boundary as a *replication-
of-persistence* boundary: scope-2 holders can reconstruct the
persistence layer from the wire; scope-1 holders can only verify it.
The operator-side retention discipline (`dregg_node::config::
RetentionPolicy`, default `Forever`) declares which suffix of the
canonical stream this operator commits to *serving*, and the wire-
level `WireMessage::RequestReceipt` / `ReceiptResponse` carries the
"I pruned this; here is the attestation that covers it" shape so
cross-member queries remain answerable without conflating
"never-existed" with "I-dropped-it." See `turn/src/turn.rs` module
docs.

### §2.8. `peer_exchange` two-party vs world

**Boundary.** Bilateral state transitions between two sovereign
cells, signed Ed25519, optionally proof-carrying — without going
through the federation's ordering.

**Inside.** Alice and Bob (the two peers). They each hold the
other's known public key, the chained `(old_commitment,
new_commitment)`, the monotonic sequence, the timestamp, and
optionally the STARK proof bytes.

**Outside.** Everyone else. They do not see the state transitions
unless one of the two parties chooses to publish.

**Enforcing primitive.** Ed25519 signature over `(old, new,
effects_hash, timestamp, sequence)` using `verify_strict`. Monotonic
sequence rejection of replays. Optional STARK verification via
`EffectVmAir` (feature-gated `zkvm`).

**Where in code.** `cell/src/peer_exchange.rs:35-303`.

**Failure mode.** If a third party obtained Alice's signing key,
they could forge transitions. If the two peers don't share an
authenticated channel for bootstrap, they cannot trust each other's
pubkeys. The STARK path is `Option<Vec<u8>>` — without it (or
without the `zkvm` feature), only signature + sequence integrity
holds; the actual state-transition validity is unverified.

**Inconsistency to name.** This is a **federation-bypass**
boundary. Two cells running peer-exchange skip consensus entirely.
The `peer_exchange` audit point: only Alice and Bob see the
transitions, the rest of the federation learns nothing, *and* the
federation cannot reconcile the resulting state with its own
attested roots. If Alice and Bob both also have hosted-cell
identities in the federation, the federation's state-commitment
view of their cells will diverge from the peer-exchange chain
unless either side publishes a sovereign turn.

### §2.9. Blocklace consensus participant vs external verifier

**Boundary.** Who is part of the BFT consensus, who only consumes
its finalised output.

**Inside.** Constitution participants: `Constitution.participants`,
each running its own strand (per-creator monotonic `seq`) of the
blocklace DAG. They produce signed blocks, gossip, run `tau` to
compute the total order, hold the local view, detect equivocation
at receive time, vote on amendments, eat the H-rule.

**Outside.** Anyone consuming a *finalised prefix*. They see
ordered blocks (Ed25519-signed, content-addressed BLAKE3) and trust
that the prefix is the same prefix everyone else computed under the
BFT assumption (n ≥ 3f+1).

**Enforcing primitive.** Cordial Miners `tau` ordering function over
the signed blocklace DAG. Ed25519 signatures + BLAKE3 content
addressing + per-creator-seq monotonicity + equivocation detection
+ constitutional auto-eviction. `blocklace/src/finality.rs`,
`blocklace/src/ordering.rs`, `blocklace/src/constitution.rs`.

**Where in code.** `blocklace/src/finality.rs:75-89` (signed
blocks), `:599-650` (CRDT merge), `:657-670` (equivocation),
`blocklace/src/ordering.rs:410-482` (`tau`), `:184-200` (approves),
`:240-278` (super-ratification), `blocklace/src/constitution.rs`.

**Failure mode.** Inside: equivocation by ≥ `f+1` colluding members
violates the BFT assumption. The two-block proof remains the
slashing evidence but it cannot un-finalise an already-finalised
prefix. Outside: a verifier with only the finalised prefix has no
way to detect that two honest nodes disagreed about the prefix
(`AUDIT-blocklace-consensus.md` open question 5). There is no
fork-choice rule above blocklace.

**Inconsistency to name.** The boundary "consensus inside"
implies attested membership; in practice, the attested-root path
(BLS-signed `AttestedRoot` covering Merkle roots) is **not wired
to a specific blocklace point** (gap D in
`AUDIT-blocklace-consensus.md §2`). So an external verifier sees a
finalised prefix from blocklace and an attested root from
federation, with no algebraic link between them. The dual-Block-type
seam (`blocklace_sync.rs:381-426`) strips signatures when converting
finality→ordering view, which is operationally safe (finality is
source of truth) but brittle.

### §2.10. Bridge: originating-fed + destination-fed vs world

**Boundary.** Who is party to a cross-federation note bridge.

**Inside.** Two federations (source A, destination B) plus the
holder of the note. The source federation produces an `AttestedRoot`
over the burn state. The note holder produces a STARK
`PortableNoteProof` whose public inputs include the nullifier, the
attested source root, the destination_federation, value, and asset
type. Destination B verifies the STARK, checks the nullifier hasn't
been bridged before (via `BridgedNullifierSet`), checks the
attested root is in its `known_federations` registry, and mints the
note.

**Outside.** Everyone else. They see only the bridge envelope's
public fields and the destination's mint event.

**Enforcing primitive.** STARK proof + Pedersen-style note
commitment + nullifier (BLAKE3 of `commitment || spending_key ||
creation_nonce`) + AttestedRoot (BLS or Ed25519-fallback) +
`BridgedNullifierSet` insertion at the destination. Four-phase
envelope (`BridgePhase::{ Locked, Witnessed, Finalized, Refunded }`)
with monotonic phase log. `cell/src/note_bridge.rs`.

**Where in code.** `cell/src/note_bridge.rs:78-97, 326, 391-447,
1230-1233`, `turn/src/executor.rs:5020-5036` (`BridgeMint`),
`turn/src/executor.rs:5074-...` (`finalize_bridge`).

**Failure mode.** If `destination_federation` is in the PI but not
algebraically bound by the AIR, a proof addressed to A can be
replayed at B (`AUDIT-nullifiers.md §5`; the docstring at
`note_bridge.rs:1230-1233` flags this as a TODO). If the
destination's `known_federations` map is misconfigured (i.e. it
trusts the wrong committee key for federation A), an unrelated
attacker can forge attestations. The bridge anonymity set in
low-volume windows trivially deanonymises by elimination
(`AUDIT-privacy.md §10`).

**Inconsistency to name.** The bridge claims source-federation
binding via `AttestedRoot`, but `AttestedRoot` itself doesn't carry
the source `federation_id` in its `signing_message` (`types/src/
lib.rs:308`). It carries only the merkle roots, height, and
timestamp. The binding between root and federation-id is the
verifier's responsibility — same pattern as
`FederationReceipt`'s tag-but-don't-sign-the-tag problem
(`AUDIT-federation.md §5, §10 F1, F3`).

### §2.11. Blinded credential prover vs verifier (presentation)

**Boundary.** A holder of an anonymous credential proves possession
of a credential satisfying a Datalog rule, without revealing which
credential, which delegation chain, or which federation member
issued.

**Inside.** The credential holder. They hold the credential bytes
(serial + claims + signature) plus a per-presentation random
`presentation_randomness`.

**Outside (verifier).** Whoever checks the presentation proof. They
learn one bit (rule-satisfied or not), or in the "selective
disclosure" mode, the holder's chosen subset of facts.

**Enforcing primitive.** Blinded-leaf STARK over a federation-known
Merkle tree (`BlindedMerklePoseidon2StarkAir`); per-presentation
randomness for multi-show unlinkability; presentation nullifier
(`chain/src/credential.rs:226-239`) for sybil resistance per
action-domain.

**Where in code.** `bridge/src/present.rs:1229`, `chain/src/
credential.rs:226-239`, presentation infrastructure in
`bridge/`.

**Failure mode.** Multi-show unlinkability is bounded by the
BabyBear birthday bound (~2^15.5 — `AUDIT-privacy.md §12`). Issuer
unlinkability holds *within* a federation but reveals *which*
federation (`AUDIT-privacy.md §10` point 3). Cross-federation
linkability is therefore open.

**Inconsistency to name.** The README's "Trusted | Selective
Disclosure | Fully Private" table reads as if it describes the
**whole dregg stack**'s privacy mode. It describes only this
boundary — the credential-presentation proof's verifier learnings.
The surrounding turn, the gossip-broadcast intent, the cleartext
executor state, and the wire IP all still leak.

### §2.12. Sealed-box pair (intent matching) vs observer

**Boundary.** Two intent-publishers who matched via a sealed
pair_id can correspond off the public intent gossip, without an
outside observer learning that they matched.

**Inside.** The two intent owners who exchanged sealed pair_ids.
They hold the `pair_id` and the matching unsealer secrets.

**Outside.** The gossip network (publishes the intents themselves
in cleartext per `intent/src/lib.rs:55-56`). They see the intents
and the sealed pair_ids; they do not see the unsealed contents.

**Enforcing primitive.** Sealer/unsealer (§2.4 primitive). Plus the
threshold-encrypted-intent skeleton at
`intent/src/trustless.rs` — which is currently a placeholder
(no concrete threshold cryptosystem chosen, `share: [u8; 32]` is an
opaque blob — `AUDIT-privacy.md §9.2`).

**Where in code.** `intent/src/sse.rs`, `intent/src/lib.rs:520-559`
(stake nullifiers), `intent/src/trustless.rs:184-217`.

**Failure mode.** Intents themselves are public; only the matched
pair is sealed. The matching predicate (cclerk-local Datalog) runs
inside the cclerk — so the cclerk operator sees both sides of the
matching surface. SSE keyword tokens are domain-separated BLAKE3
keyed hashes; they leak keyword-equality across publishers using
the same SSE key.

**Inconsistency to name.** The README claims "privacy-preserving
marketplace." `docs/intent-privacy-assessment.md` (the internal
audit) opens with *"Short answer: No."* The boundary that *exists*
is "intent body sealable to a chosen recipient"; the boundary that
*does not* is "the marketplace itself is private" — intents are
posted publicly.

### §2.13. CapTP session participants vs non-session

**Boundary.** Two peers who have completed a `CapHello` handshake
share a `CapSession` epoch; their subsequent messages are
session-keyed.

**Inside.** Two peers with a live `CapSession`. They share an
epoch number; their pipelined messages reference promise ids that
mean things only inside this session.

**Outside.** Anyone not in the session. They cannot decode the
intra-session promise ids; they cannot impersonate the other peer.

**Enforcing primitive.** `CapSession` with epoch (the wire-level
identifier); TLS confidentiality of the underlying transport
(`wire/src/connection.rs` rustls), per-role auth tier
(`wire/src/auth.rs`), hardening rate-limit
(`wire/src/hardening.rs`).

**Where in code.** `captp/src/session.rs`,
`wire/src/server.rs:2278-2282` (`CapHello`),
`wire/src/server.rs:2509-2607` (`PresentHandoff`).

**Failure mode.** Most CapTP wire behaviour is *not* end-to-end
wired. `PipelinedMsg` is accept-and-discard at both ends
(`AUDIT-distributed-semantics.md §2` and `AUDIT-protocol-composition.md`
seam 3). `LiveRef::send` queues locally but never dispatches.
Disconnect leaves stale sessions; nothing breaks promises on TCP
close. The boundary "session-inside" is well-typed but
operationally porous: an attacker who can see a TLS-decrypted
stream (mid-pipeline node) can see the cleartext envelopes.

**Inconsistency to name.** The CapTP envelope is *cleartext over
TLS*. Sealed capabilities protect the high-value payload (the cap
bytes) but not the metadata (who is talking to whom about what
cap-id). The trust-model docstring at `wire/src/lib.rs:8-15` is
honest about this. The CapTP-inside boundary is metadata-leaky to
any peer with TLS-decrypt access.

### §2.14. `Authorization::CapTpDelivered` certificate vs anyone

**Boundary.** A receiver of a `HandoffCertificate` who can validate
it and produce a `HandoffPresentation` vs anyone else.

**Inside.** The recipient named in the cert (`recipient_pk`). They
hold a signing key that proves possession of the matching secret.

**Outside.** Anyone who only sees the cert in flight (QR-photo,
email, snoop). Without the recipient's private key, they cannot
produce a valid `HandoffPresentation`.

**Enforcing primitive.** `HandoffCertificate` signed by the
introducer + `HandoffPresentation` signed by the recipient.
Domain-separated `b"dregg-handoff-cert-v1"` and
`b"dregg-handoff-present-v1"`. Cert binds
`target_federation || target_cell || recipient_pk || permissions ||
allowed_effects || expires_at || max_uses || nonce || swiss`.
Presentation binds nonce + target_cell + target_federation.
Verification at `captp/src/handoff.rs:366-414` checks: introducer
sig → recipient sig → introducer-is-known →  expiry → swiss-enliven.

**Where in code.** `captp/src/handoff.rs:104-134, 295-336,
366-414`, `wire/src/server.rs:2509-2571`.

**Failure mode.** The wire handler accepts `introducer_pk` from the
wire message and trusts it — there's no `FederationId → PublicKey`
registry to cross-check that the supplied pk derives from the
cert's `cert.introducer`. (`AUDIT-distributed-semantics.md` GAP-3.)
`HandoffError::ReplayDetected` is defined but never raised; no
nonce-seen ledger exists; replay defence reduces to `max_uses`
decrement at swiss enliven.

**Inconsistency to name.** The SDK side hardcodes
`target_federation = self.config.federation_id`
(`sdk/src/captp_client.rs:482-483`), so the only certs the SDK can
*build* are "introducer == target" local certs — the true
Alice→Bob→Carol three-party shape is not constructable
client-side, though the receiver side would accept it
(`AUDIT-distributed-semantics.md` GAP-1).

---

## §3. Inconsistencies surfaced today

The boundary problems we have actually hit, named succinctly:

### §3.1. `FieldVisibility::Committed` hides from external readers but not from the executor

The visibility flag is a publication-policy tag, not a confidentiality
primitive. The cleartext lives in `[FieldElement; STATE_SLOTS]` next
to the tag, and the executor reads and writes the cleartext value by
index. The boundary `Committed` claims to enforce is "non-cap-holder
external readers see only a hash"; it does **not** include "the
executor sees only a hash."

This is the canonical example the designer raised. The mismatch with
the designer's mental model is that `Committed` reads like an algebraic
hiding property (commit-and-reveal); in implementation it is a
formatting choice on the external view. Documented honestly at
`cell/src/state.rs:42-43`. The audits surface it again at
`AUDIT-privacy.md §5` and `CELL-CRATE-REVIEW.md` (under `state.rs`,
P1-2 commitment staleness note).

### §3.2. Sovereign cells intended to hide state from the executor; actual implementation does not

The witness path (`SovereignCellWitness`) provides cleartext cell
state to the host executor on every turn. The federation persistently
stores only the commitment, but during the turn the executor reads
and re-executes against the cleartext. The boundary "executor doesn't
see your state" is **deferred** to the proof-carrying path
(`turn/src/executor.rs:3131-3249`), which is the alternative, not the
default. Per `AUDIT-sovereign-witness-teeth.md §8`: *"Sovereign
witnesses are not algebraically constraining. They are a
federation-side bookkeeping handshake."*

Lane P and the soundness sweep are addressing this by retiring the
witness path in favour of proof-carrying turns. Until then, the
boundary is operationally "the executor sees but doesn't persist,"
not "the executor doesn't see."

### §3.3. Sealed cap drops `allowed_effects` on unseal

`cell/src/seal.rs::deserialize_capability` sets `allowed_effects:
None` always. Sealing a `FACET_TRANSFER_ONLY` cap and unsealing it
produces an unfaceted cap. The boundary "you unseal" implicitly
became "you receive an unfaceted cap." This is a quiet
authority-amplification surface. The soundness sweep is fixing this
(v3 sealed-plaintext format includes `allowed_effects`).

### §3.4. `WitnessedReceipt` scope-2 has no membership predicate

The bundle (trace_rows + witness_hash) ships as a JSON artifact.
Anyone with the file has scope-2 — i.e. the private trace columns.
There is no membership predicate, no sealing for the bundle, no
audit-key signature. The audience for scope-1 (proof) and scope-2
(replay) are different populations and the protocol does not
distinguish them. `WITNESSED-RECEIPT-CHAIN-DESIGN.md §2` is honest:
"a sufficient artifact for someone we choose to trust later."

### §3.5. `FederationId` and `committee_pubkeys` decoupled

Pre-Lane-D, `federation_id` was a random 16-byte token, not a
commitment to the committee. The boundary "this federation attested
this" was conventional; the verifier had to pick the right
`FederationCommittee` from local state and trust the
`federation_id` tag. Lane D's fix derives
`federation_id = BLAKE3(committee_verifier_key, committee_epoch)`,
making the binding algebraic. `AUDIT-federation.md §10` F1 names
this; same shape recurs in `FederationReceipt.federation_id`
(F4 — `committee_epoch` is serialized but unverified).

### §3.6. `bytes_to_promise_id` 32→8 truncation (and similar)

The boundary "this is the same cell across federations / proofs /
contexts" relied on a non-collision-resistant 8-byte fingerprint.
Same shape recurs throughout: `field_element_to_bb` truncates 32 →
4 bytes (`turn/src/executor.rs:1839-1849`), peer_exchange
commitments used a 4-byte projection before the
`canonical_32_to_felts_4` Stage-1 widening. The fix is uniform —
widen to enough field elements to recover security level
(`bytes32_to_babybear` = 8 BabyBears, ~248 bits).

### §3.7. CapTP-routed Turns use `Authorization::Unchecked`

`wire/src/captp_routing.rs:48` constructs CapTP turns with
`Authorization::Unchecked`. The justification (lines 30-42) is "the
cryptographic legitimacy was already established off-band" — the
swiss enliven happened, the handoff cert verified, etc. The
boundary `Unchecked` claims is "nothing checked"; the actual story
is "checked by a different mechanism upstream." The executor's
`grep-guard against Unchecked` (Stage 8 P2.E-H) needs an explicit
carve-out list, and that list is currently informal.

Plus: these Unchecked Turns are pushed to `pending_captp_turns` and
**never drained** (`AUDIT-distributed-semantics.md` GAP-12,
`AUDIT-protocol-composition.md` seam 3). Even if drained, the
executor would reject them (`Authorization::Unchecked` is
uniformly an error). The mirror invariant "every CapTP mutation has
a corresponding on-chain receipt" is structurally aspired but
operationally not closed.

### §3.8. Mode-flag boundary vs. actor-entitlement boundary

The Effect-VM AIR has a `mode_flag` (RESERVED bits 8..9) tracking
"this cell is sovereign." `AUDIT-sovereign-witness-teeth.md §3.2`
calls out the confusion: the flag is a *property of the cell*
("this cell is now sovereign") not a *property of the actor*
("this actor is entitled to act on the sovereign cell"). The AIR
enforces the former; it does not check the latter at all.
Permission/cap checks for sovereign-cell actions happen at the
executor's `verify_authorization` step (post-witness-injection),
not in the AIR.

### §3.9. Two equivocation definitions in blocklace

`finality.rs::detect_equivocation` defines equivocation as
"same `(creator, seq)`, different content." `ordering.rs::
has_equivocation_in_past` defines it as "same `(creator, round)`,
two distinct blocks." These are different equivalence classes — a
Byzantine node can monotonically bump `seq` across forks (no seq
reuse) but produce two blocks at the same round.
`AUDIT-blocklace-consensus.md §4` calls this gap B. The
"equivocation-inside" set differs between the two layers; the
constitutional auto-eviction at the third layer
(`constitution.rs::auto_evict_equivocator`) consumes only the
finality-layer flavour of proof.

---

## §4. Per-subsystem "boundary contract"

For each major subsystem, one paragraph stating the boundary
contract — who is inside, who is outside, what enforces, what
specifically does not. This is the API contract for boundary
declarations going forward.

### §4.1. CapTP

**Inside.** Holders of swiss numbers (bearer-inside) and recipients
named in `HandoffCertificate`s (attested-inside). Each
`CapSession` has its own per-epoch inside set.

**Outside.** Anyone else, including TLS-decrypting mid-pipeline
nodes who see envelopes in cleartext.

**Enforces.** Bearer possession of swiss + Ed25519 handoff cert/
presentation signatures + session-epoch validation at the wire.

**Does not enforce.** Cross-federation routing of enliven (no
router); replay of `max_uses == None` certs (no nonce ledger);
disconnect → broken-promise cascade (not wired); end-to-end
delivery of pipelined messages (`LiveRef::send` queues locally,
wire discards). The "session-inside" is well-typed at the
data-structure level and operationally porous at the network
level.

### §4.2. Federation

**Inside.** `FederationCommittee` members + KZG-attested weights.

**Outside.** Anyone with the committee's verifier key.

**Enforces.** Weighted-threshold BLS aggregate signature
(BLS12-381 + KZG-attested weights). Constant-size `ThresholdQC`.
Domain-separated signing messages. Ed25519 fallback aggregate.

**Does not enforce.** Slashing (none); expulsion (delegated to
blocklace constitution); algebraic binding between `federation_id`
and committee (currently conventional; Lane D fix in flight);
`committee_epoch` is decorative (F4); `FederationReceipt`
production from `TurnReceipt` (the lifting seam is empty —
`AUDIT-protocol-composition.md` seam 6); blocklace-finality
binding into `AttestedRoot` (F3).

### §4.3. Blocklace

**Inside.** `Constitution.participants` running per-creator strands
of the DAG.

**Outside.** Anyone consuming finalised prefixes.

**Enforces.** Cordial Miners `tau` ordering; Ed25519 + BLAKE3
content addressing; equivocation detection (seq-based at receive,
round-based in `tau`); constitutional auto-eviction; H-rule on
threshold changes; CRDT-friendly `merge`.

**Does not enforce.** Fork choice above `tau` (none); algebraic
binding to `AttestedRoot` (gap D); the four-level `FinalityLevel`
(vestigial — gap E); the unified-vs-disjoint equivocation rule
(gap B). `Ordered` finality is never reached in production paths.

### §4.4. Turn/Executor

**Inside.** The actor (signing cclerk) and the host executor. The
executor sees cleartext for every hosted cell during turn execution.

**Outside.** Anyone consuming the resulting `TurnReceipt`,
`WitnessedReceipt`, or `FederationReceipt`.

**Enforces.** Ed25519 turn signature (over the v1 canonical
message); replay protection via monotonic nonce per cell; balance
conservation (with Pedersen+Schnorr+Bulletproof on the
ValueCommitment path); STARK proof via `EffectVmAir` (for
proof-carrying turns).

**Does not enforce.** Coverage of `sovereign_witnesses`,
`execution_proof`, `custom_program_proofs`, `conservation_proof` by
the v1 signing message (P2-10 — `sdk/src/cipherclerk.rs:3895-3906`); the
boundary between turn-author and host executor remains porous for
hosted cells (the host sees everything); cross-cell algebraic
binding (`STAGE-7-GAMMA-2-PI-DESIGN.md` Phase 1).

### §4.5. WitnessedReceipt

**Inside (scope-1, proof audience).** Anyone with the proof + PI +
air name.

**Inside (scope-2, trace audience).** Anyone with the bundle
file.

**Outside.** Anyone without either.

**Enforces.** STARK proof verifiability (scope-1); trace-PI
consistency on re-derivation (scope-2 honest-mirror check).

**Does not enforce.** Membership predicate on the scope-2
audience; binding between bundle and any specific receiver; the
turn-level v3 hash vs the cipherclerk's v1 signing-message disagree
(P2-10).

### §4.6. Cell

**Inside (cap-holders).** Holders of `CapabilityRef`s into the
cell. They can exercise the rights named by `allowed_effects` ×
`permissions`.

**Inside (cell owner).** Holder of the cell's signing key.
For sovereign cells, also the holder of the preimage state.

**Outside.** Anyone querying the public state view, anyone reading
the Merkle root.

**Enforces.** Permission lattice (`AuthRequired::is_narrower_or_equal`),
attenuation discipline, facet bitmask narrowing
(`is_facet_attenuation`), revocation channel checks (O(1)),
verifier-side cascading via CDT (`derivation.rs`).

**Does not enforce.** Field-level confidentiality against the host
executor (§3.1); `ExtendedFacet` parameterised constraints are
defined but never consumed; sealed-cap `allowed_effects` round-trip
(§3.3); CDT-revocation-trips-channel link (§3 cross-cutting:
two revocation mechanisms exist disjointly).

### §4.7. Storage (BlindedQueue, NoteTree, etc.)

**Inside.** Holder of the commitment preimage + randomness +
spending key.

**Outside.** The queue operator. Sees commitments going in,
nullifiers coming out; (claim) cannot link them when
`/consume-private` is used.

**Enforces.** Commitment hiding (when producer includes
randomness), nullifier as one-way function over (commitment ||
spending_key || creation_nonce).

**Does not enforce.** Anti-flooding at `/commit`
(`blinded_endpoint.rs`); actual ZK proof verification at
`/consume-private` (currently `if proof.is_empty() { invalid }` —
trust-the-prover stub); network-level linkability (operator sees
caller IP).

### §4.8. Wire

**Inside.** Endpoints of a TLS connection.

**Outside.** Network observers (between hops; before TLS terminates).

**Enforces.** TLS confidentiality + integrity; per-role auth
tiers; per-peer hardening token bucket; heartbeat liveness;
graceful shutdown.

**Does not enforce.** Metadata privacy (IP, timing, size visible);
multi-hop privacy (intermediate node decrypts); CapTP envelope
encryption beyond TLS; mix-network properties (no Sphinx/Tor/Dandelion).

### §4.9. Privacy/Sealing

**Inside.** Sender (ephemeral DH key holder) and recipient
(`unsealer_secret` holder).

**Outside.** Everyone with TLS-decrypted access — they see the
`pair_id` and the ciphertext size and timing.

**Enforces.** X25519 + ChaCha20-Poly1305 confidentiality;
per-message sender-ephemeral forward secrecy; BLAKE3-bound commitment
of (cap_hash, ephemeral_public, nonce).

**Does not enforce.** Recipient anonymity from observers (pair_id
is deterministic); recipient-side forward secrecy (static
`unsealer_secret`); ciphertext padding; `allowed_effects` round-trip
(§3.3); post-quantum (X25519).

### §4.10. Intent

**Inside (intent body).** Whoever can decrypt the intent's seal
(or, eventually, holds enough threshold shares).

**Inside (intent match).** The two cipherclerks that locally evaluated
the Datalog and matched.

**Outside.** Gossip network. Sees intent bodies (currently
public per `intent/src/lib.rs:55-56`), SSE keyword tokens, stake
nullifiers.

**Enforces.** Per-epoch stake-nullifier set (`gossip.rs`);
SSE keyword tokens (BLAKE3 of `(keyword, epoch)`); commit-reveal
fulfillment with 60s expiry; cclerk-local Datalog matching.

**Does not enforce.** Threshold-encrypted intent body
(`intent/src/trustless.rs` is a skeleton; no cryptosystem chosen);
intent matching unlinkability across epochs; gossip metadata
privacy.

### §4.11. Bridge

**Inside.** Source-federation committee (attests root) +
destination-federation committee (verifies + mints) + note holder
(produces STARK).

**Outside.** Anyone else. They see the envelope's public fields.

**Enforces.** STARK soundness over `(nullifier, root,
destination_federation, value, asset_type)` PI;
`BridgedNullifierSet` insertion at destination; `AttestedRoot`
trust at destination; phase log monotonicity (`Locked → Witnessed
→ Finalized | Refunded`).

**Does not enforce.** `destination_federation` algebraic binding
inside the AIR (currently in PI but no constraint —
`AUDIT-nullifiers.md §5`); source-federation_id binding in
`AttestedRoot.signing_message` (`§3.5` here); cross-federation
anonymity in low-volume windows.

---

## §5. Naming proposal (vocabulary, not a type system)

Without proposing a new type system, this is the vocabulary the
codebase should use when declaring boundary contracts going
forward.

### §5.1. The four populations

- **Cleartext-inside.** Participants who see the plaintext datum.
  Example: a cell's `Public` field is cleartext-inside for
  everyone who can read the public state view. A hosted-cell
  state is cleartext-inside the host executor.

- **Commitment-inside.** Participants who see the commitment but
  not the value. Example: a `Committed` field's hash is
  commitment-inside the external public state view. A sealed
  capability's commitment is commitment-inside anyone with the
  cap_hash.

- **Acceptance-inside.** Participants who see only proof of
  acceptance — yes/no. Example: a verifier of a STARK
  presentation proof learns the rule was satisfied. A
  `ThresholdQC` verifier learns the message was attested.

- **Out-of-band.** Participants who learn nothing — they are
  outside the boundary entirely.

These are not disjoint: a single party can be cleartext-inside one
subsystem and out-of-band another. The four labels are *per-datum,
per-subsystem* and do not aggregate into a global trust level.

### §5.2. Rustdoc convention (discipline, not type)

Every public type with a privacy story should document, in `///`
comments:

```rust
/// Boundary contract:
/// - Cleartext-inside:  <population>
/// - Commitment-inside: <population>
/// - Acceptance-inside: <population>
/// - Out-of-band:       <population>
/// Enforced by: <primitive>
/// Failure mode if violated: <description>
```

This is not a new type. It is editorial discipline. The benefit is
that an api-doc reader (or a code reviewer) can scan a type's
docstring and see the boundary explicitly, instead of inferring it
from primitive choices or trust-model footnotes.

A few concrete first-targets for this convention:

- `Cell` (`cell/src/cell.rs`) — boundary differs Hosted vs Sovereign,
  and the sovereign case differs further between proof-carrying and
  witness paths.
- `FieldVisibility` (`cell/src/state.rs:13-26`) — the canonical
  case where `Committed` reads as algebraic but isn't against the
  executor.
- `SealedBox` (`cell/src/seal.rs`) — including the recipient
  pair_id linkability caveat.
- `SovereignCellWitness` (`turn/src/turn.rs:22-30`) — including
  "the host executor *does* see this cleartext during the turn."
- `WitnessedReceipt` (`turn/src/witnessed_receipt.rs`) —
  including the scope-1 vs scope-2 audience asymmetry.
- `BridgedNullifierSet` / `PortableNoteProof` —
  including the `destination_federation` PI-but-not-constrained
  caveat.
- `AttestedRoot` (`types/src/lib.rs:199-218`) — including
  the missing federation-id and blocklace-finality binding.
- `EncryptedTurn` (`turn/src/encrypted.rs`) — including
  "the privacy property is designed and locally tested but not
  delivered in production."

---

## §6. Boundaries that compose

Some boundaries chain. A sealed message *to* a cap-holder who's
*in* a federation produces three nested boundaries:

```
out-of-band
    \
     federation (cleartext-inside committee, acceptance-inside outside)
       \
        cap-holders (cleartext-inside swiss bearers / handoff recipients)
          \
           sealed-recipient (cleartext-inside unsealer holder)
              \
               cell-owner (cleartext-inside private fields)
```

When boundaries nest like this, the **innermost** boundary is the
operative one for the protected datum. Anyone outside the innermost
nesting sees what the next-outer boundary permits.

When boundaries **intersect** — e.g. a datum is exposed via two
different mechanisms, each with its own boundary — the **smaller**
intersection is the boundary's effective inside (the parties who
satisfy *both* memberships).

When boundaries **union** — e.g. a datum is sealable to either of
two recipients, or unlockable by either of two keys — the **larger**
union is the effective inside.

**Concrete composition examples in dregg:**

- A sovereign cell's state is *commitment-inside* the federation
  (only the commitment is persisted), but *cleartext-inside* the
  host executor during the witnessed turn. The boundary
  "executor blind" requires the proof-carrying path, where the
  AIR's `OLD_COMMIT == sovereign_commitments[cell_id]` constraint
  is the operative inside. (§2.6.)

- An intent sealed to two matched parties is *commitment-inside*
  the gossip network (sealed pair_id), *cleartext-inside* the two
  matched cipherclerks, and *acceptance-inside* the gossip's stake
  nullifier verification. (§2.12.)

- A bridge transfer is *cleartext-inside* the note holder,
  *commitment-inside* the source federation's `AttestedRoot`,
  *acceptance-inside* the destination federation's STARK
  verification + nullifier set, and *out-of-band* for everyone
  else. (§2.10.)

- A CapTP-routed delivery from federation A to federation B with
  a handoff certificate is *cleartext-inside* the swiss bearer at
  A, *cleartext-inside* the handoff recipient at B, and
  *acceptance-inside* the wire validation at B's edge. The cap's
  payload (if sealed) is further commitment-inside everyone who
  isn't the unsealer holder. (§2.4, §2.14.)

The naming proposal in §5 lets us spell these compositions
explicitly: "a sovereign-cell field that is `Committed` and lives
under a proof-carrying turn is commitment-inside both the
federation and the host executor, and out-of-band everyone else."

---

## §7. Boundaries that conflict

The cases where two boundaries make incompatible claims:

### §7.1. `FieldVisibility::Committed` vs. host executor

The `Committed` boundary claims commitment-inside everyone outside
the cap-holder set. The host executor's *actual* access claims
cleartext-inside the host executor. These conflict: the claim
"the field is committed" is true against external readers and false
against the executor. The mitigation is documentation (`state.rs:42-43`)
and the long-term path is sovereign cells in proof-carrying mode.
(§3.1.)

### §7.2. Sovereign cell vs. host (witness path)

The sovereign cell boundary claims "executor doesn't see cleartext."
The witness path's actual behaviour says "executor sees cleartext for
the duration of the turn." Conflict: the sovereign property is
operationally "doesn't persist," not "doesn't see." Lane P and
soundness sweep are migrating to the proof-carrying path where
the boundary is honoured algebraically. (§3.2.)

### §7.3. Seal vs. facet

The seal boundary claims "you unseal and receive the cap as
attenuated." The unseal's actual behaviour drops `allowed_effects`,
producing an unfaceted cap. Conflict: the boundary "you receive
what was sealed" widens on unseal. (§3.3.)

### §7.4. `FederationReceipt.federation_id` vs. body_hash

The federation receipt's `federation_id` tag claims the body was
attested by *that* federation. The QC actually signs only
`body_hash`, which does not include `federation_id` or
`committee_epoch`. Conflict: the boundary "this federation attested
this" is conventional, not algebraic. (§3.5.)

### §7.5. CapTP-routed turn `Authorization::Unchecked` vs. executor

The wire builds CapTP turns with `Unchecked`, claiming "checked
upstream." The executor rejects `Unchecked` uniformly. Conflict:
either Unchecked is admitted (boundary widened — executor accepts
turns whose authority it can't itself verify), or the wire's
upstream-check claim has no on-chain mirror (boundary stays
inconsistent — turns pushed to `pending_captp_turns` and never
drained). Both: the queue is never drained today, so the situation
is "harmless because dead," not "harmless because consistent."
(§3.7.)

### §7.6. Two equivocation definitions in blocklace

Finality-layer equivocation (same `(creator, seq)`) and
ordering-layer equivocation (same `(creator, round)`) are different
predicates. A Byzantine pattern caught by one may not be caught by
the other. Conflict: the "equivocation-inside" set differs between
the two layers. (§3.9.)

### §7.7. Proof boundary vs. witness-bundle boundary

The proof boundary (scope-1) claims acceptance-inside-only — the
verifier learns yes/no plus public PI, nothing else. The
witness-bundle boundary (scope-2) claims cleartext-inside-only-to-the-replayer.
These different boundaries ship as the same `WitnessedReceipt`
JSON artifact with no audience-discrimination mechanism. Conflict:
the proof's "outside" can become the bundle's "inside" if anyone
hands them the bundle. (§3.4.)

---

## §8. Open questions for designer

Things the codebase does not unambiguously answer.

1. **Are the `cleartext-inside` / `commitment-inside` /
   `acceptance-inside` / `out-of-band` labels worth committing to
   as the codebase's vocabulary?** If yes, the rustdoc convention
   in §5.2 becomes a contributor expectation; if no, an
   alternative vocabulary (or a typed pattern) is needed.

2. **Should `FederationId` be a commitment to the committee?**
   `AUDIT-federation.md` open question 1. The boundary "this
   federation attested this" needs to be algebraic if cross-fed
   bridges are to be third-party-verifiable.

3. **Is the sovereign-cell witness path deprecated?** If yes,
   the migration plan needs to name every site that still builds
   a `sovereign_witnesses`-populated turn (`node/`,
   `app-framework/`, `apps/`, `demo-agent/`, `teasting/`,
   `intent/`). If no, the boundary "executor-blind" needs an
   explicit caveat that it applies only to the proof-carrying
   path.

4. **Who is authorised to hold a `WitnessedReceipt` bundle?**
   Today: anyone with the file. Is the boundary an operational
   choice (signed audit-key gate) or a cryptographic one
   (sealed bundle, addressed to a chosen verifier)? The
   former is cheaper; the latter aligns with the rest of dregg's
   sealing primitives.

5. **What is the deployment plan for `EncryptedTurn`?** The
   `turn/src/encrypted.rs` module is well-tested in isolation but
   not consumed by the executor. The boundary "federation orders
   turns without seeing them" depends on this module being wired
   in.

6. **What's the cross-cell binding plan beyond Stage 7-γ.2 Phase
   1?** `STAGE-7-GAMMA-2-PI-DESIGN.md` is concrete for the PI-only
   shape. Phase 2 (joint aggregation AIR) is sketched. The
   boundary "cross-cell consistency is algebraic" matters for
   bridge-boundary trust — see §9 below.

7. **Should CDT revocation and revocation channels be linked?**
   Today two disjoint revocation mechanisms exist: `derivation.rs`
   (verifier-side CDT) and `revocation_channel.rs` (executor-side
   O(1) lookup). A CDT revocation does not trip a channel.
   `CELL-CRATE-REVIEW.md §revocation` open question 8.

8. **Does the network-layer privacy plan
   (`docs/design-network-privacy.md`) move from plan to
   implementation in this cycle?** The boundary "network metadata
   hiding" is the largest unmitigated leak; everything else is
   over-claimed by comparison.

9. **For the trustless intent engine, which threshold
   cryptosystem is the target?** The placeholder in
   `intent/src/trustless.rs` types `share: [u8; 32]` opaquely.
   Without selecting a concrete scheme, the boundary
   "no party reads before collective decryption" is a typed
   intent, not a delivered property.

10. **Is the boundary "host executor is trusted" an explicit
    deployment assumption, or a temporary state?** Hosted cells
    expose every field in cleartext to the host. The privacy
    story for *any* hosted-cell app currently hinges on operator
    honesty plus TLS plus the federation's good faith.

11. **Should the witness-bundle audience be sealable?**
    `WitnessedReceipt::sealed_bundle` would be a natural
    primitive — encrypt the trace bundle under a chosen
    audit-key pubkey, ship the scope-1 verifiable proof alongside.
    The proof is publicly verifiable; the bundle is acceptance-
    inside the audit-key holder. This compose naturally with
    §2.4's sealing primitive.

12. **Does the README's "Privacy Model" table need rewriting?**
    The table reads as describing the whole stack; it describes
    only the credential-presentation proof's verifier-learnings.
    See §2.11 here and `AUDIT-privacy.md §13` open question 1.

13. **What is the source-of-truth for "is this `FederationId` in
    `known_federations`?"** The wire layer accepts an
    `introducer_pk` from the wire message and trusts it; the
    cert's `cert.introducer` field is a `FederationId`. The
    `FederationId → PublicKey` registry is missing
    (`AUDIT-distributed-semantics.md` GAP-3). The boundary
    "this federation introduced this cert" is currently soft.

---

## §9. Connection to slot caveats + γ.2

Two work-streams interact with the boundary algebra in ways worth
naming:

### §9.1. Slot caveats v1+

If we add a "private slot" caveat
(`SLOT-CAVEATS-DESIGN.md`-style), the boundary contract for a
slot-caveat is:

- **Cleartext-inside:** the cap holder + the slot evaluator
  (executor, today).
- **Commitment-inside:** anyone holding the slot's commitment
  hash.
- **Acceptance-inside:** anyone verifying a ZK proof that the
  caveat was satisfied.
- **Out-of-band:** everyone else.

A "private slot" only meaningfully reduces the cleartext-inside
population if the **slot evaluator is removed from it** — i.e. if
the caveat is evaluated under a ZK predicate, not by the host
executor reading cleartext. Otherwise the caveat is privacy-
preserving against external readers (commitment-inside) and
honest about the executor's access, which is the same posture as
`FieldVisibility::Committed`. The slot caveat would benefit from
the rustdoc convention in §5.2 from day one.

### §9.2. γ.2 cross-cell binding

If γ.2 lands the PI-only Phase 1 (`STAGE-7-GAMMA-2-PI-DESIGN.md`),
the cross-cell boundary becomes:

- **Cleartext-inside (joint).** The actor + the executor (for
  hosted cells). They see the full bilateral effect data.
- **Commitment-inside (joint).** Anyone holding the
  `transfer_id` / `grant_id` / `intro_id` and the matching per-cell
  PI roots. They can pairwise-verify that the two per-cell proofs
  describe the same bilateral effect.
- **Acceptance-inside.** Anyone verifying either per-cell proof
  alone. They learn only the per-cell statement.

The change γ.2 introduces is that the *commitment-inside* set
gains algebraic teeth: today the executor's say-so glues the two
proofs; under γ.2 a canonical hash (`transfer_id`) and PI
accumulator (`OUTGOING_TRANSFER_ROOT` ↔ `INCOMING_TRANSFER_ROOT`)
provide the binding. This is the bridge-boundary trust slope
inverting in the right direction.

Phase 2 (joint aggregation AIR) would further reduce the
"executor in the cleartext-inside set for the binding fact" —
the AIR's joint constraint would itself algebraically witness the
binding, removing the executor from the trust path for cross-cell
consistency. That is the future statement of the boundary; today
it is forward-looking.

---

## §10. Connection to Studio/Starbridge

Studio runs an in-browser node via `wasm/src/runtime.rs`. The
runtime is a real `dregg_sdk::AgentCipherclerk` + real
`dregg_cell::Ledger` + real `dregg_turn::TurnExecutor` etc., all
in browser linear memory.

The boundary "in-browser" affects the cleartext-inside /
commitment-inside cuts thus:

- **The browser is the host executor.** Anything that is
  cleartext-inside the host executor (hosted-cell fields,
  sovereign-witness preimages during the turn, etc.) is
  cleartext-inside the browser process. JavaScript code on the
  page can call into wasm and read state.

- **The browser is not the federation.** A wasm node does not
  hold BLS shares; it cannot produce `ThresholdQC`s. It is
  acceptance-inside the federation boundary at best — it accepts
  attested roots, it cannot mint them. `dregg_federation` does
  not cross-compile to wasm32 (per `STARBRIDGE-APPS-PLAN.md
  §1.2`), so federation operations are remote-only.

- **Browser-to-browser sealing is real.** X25519 + ChaCha20-Poly1305
  in `cell/src/seal.rs` works in wasm. Two browsers can be
  cleartext-inside a sealed channel without a federation
  intermediary. This is the substrate the `peer_exchange`
  primitive (§2.8) sits on for sovereign-cell direct exchange.

- **Browser-as-prover.** The wasm crate exports
  `stark::prove`/`verify`. A browser can be the cleartext-inside
  proof generator (holds the trace witness) and ship the
  acceptance-inside proof + commitment-inside scope-2 bundle to
  the audience of its choice.

- **Browser-as-verifier.** Symmetrically, a browser can verify a
  STARK without holding the witness — i.e. it can be
  acceptance-inside without entering cleartext-inside. Studio's
  Explorer surface is structurally this: read-only federation
  view, verifies attestations.

- **Starbridge writes.** When Starbridge takes write authority to
  a live federation node (per `site/STUDIO.md`), the browser
  becomes a cap-holder (§2.2) and gains cleartext-inside access
  to whatever the held caps unlock. The boundary is the user's
  local key custody — same as native CLIs.

The relevant policy question Starbridge raises: **whose audit-key
holds the witness bundle?** A browser-as-prover that ships a
`WitnessedReceipt` to a remote audience is in the same posture as
§3.4 (no membership predicate on bundle audience). For Starbridge's
"power-user viewport" use case, this is acceptable. For any
federation-grade audit flow that Starbridge might enable, the
bundle should be sealable (§8 open question 11).

---

## §11. Reading guide

This document is descriptive — it doesn't push code changes. For
contributors who want to act on it:

- **If you are adding a new public type with a privacy or
  authentication story**, adopt the rustdoc convention in §5.2.
  Spell out who is cleartext-inside, commitment-inside,
  acceptance-inside, and out-of-band. Spell out the enforcing
  primitive and the failure mode.

- **If you are reading code with a privacy claim**, walk the four
  populations explicitly. The frequent mismatch in dregg is that
  the docstring describes the boundary against external readers
  while the relevant adversary in the deployment is the executor
  or a mid-pipeline node.

- **If you are reviewing a `# Privacy` claim in a README or
  design doc**, ask which of the boundaries in §2 the claim is
  about. Most claims that read as global are about §2.11 (the
  credential-presentation proof boundary) and apply far less
  broadly than the prose suggests.

- **If you are designing a new subsystem**, before writing code
  draft the boundary contract paragraph (§4 shape). State what
  the enforcing primitive does *and what it does not*. The "does
  not" half is the part that has been costing us in audits.

The intent of this doc is to make the boundaries dregg already
has explicit and consistent in our vocabulary. It is not a
type-system proposal. It is naming.

---

## §12. Cross-references

- `AUDIT-privacy.md` — privacy primitives × claims × delivery matrix.
- `AUDIT-distributed-semantics.md` — CapTP, three-party handoff, GC,
  promise pipelining, session boundaries.
- `AUDIT-protocol-composition.md` — the 10 seams between layers.
- `AUDIT-federation.md` — the federation primitives + the four
  meanings of "federation."
- `AUDIT-blocklace-consensus.md` — the Cordial Miners
  implementation, equivocation, finality.
- `AUDIT-nullifiers.md` — the 11+ nullifier shapes and their
  audiences.
- `AUDIT-sovereign-witness-teeth.md` — sovereign cell boundary,
  witness vs. proof paths.
- `CELL-CRATE-REVIEW.md` — every file in `cell/`, what's
  load-bearing vs. unconsumed.
- `STAGE-7-GAMMA-2-PI-DESIGN.md` — cross-cell algebraic binding,
  Phase 1.
- `WITNESSED-RECEIPT-CHAIN-DESIGN.md` — scope-2 replay semantics.
- `STARBRIDGE-APPS-PLAN.md` — in-browser runtime, post-`apps/`
  userspace.
- `EXECUTOR-HONESTY-AUDIT.md` — the broader frame for
  "executor sees X but proves Y."
- `DESIGN-commitment-framework.md` — the typed `Commitment<T>`
  dual-form binding (BLAKE3 ↔ Poseidon2).

End.
