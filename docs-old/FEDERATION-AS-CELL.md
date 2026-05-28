# Federation as a (weird, large) Cell

**Status:** design study; read-only on code. Companion to
`CROSS-CELL-COORDINATION.md`, `FEDERATION-UNIFICATION-DESIGN.md`,
`AUDIT-federation.md`, `AUDIT-blocklace-consensus.md`,
`AUDIT-distributed-semantics.md`, `SLOT-CAVEATS-DESIGN.md`,
`SOVEREIGN-WITNESS-AIR-DESIGN.md`, `STAGE-7-GAMMA-2-PI-DESIGN.md`,
`WITNESSED-RECEIPT-CHAIN-DESIGN.md`.

The question this doc is for: **is a federation conceptually a cell with
a committee instead of an owning key, a programmable consensus rule
instead of slot caveats, and a ledger of cells instead of a slot array?**

The TL;DR — written first so it can be read alone:

> A federation is *structurally homomorphic* to a cell at six of nine
> axes and *structurally distinct* at three (state shape, nonce shape,
> program-vs-process). The right move is to introduce a unifying
> `Principal` *trait* (or thin newtype-wrapped enum) that both implement,
> not to collapse them into one type. The unification buys: (a) a single
> CapTP delivery rule that works at either scale; (b) a single
> `state_commitment` interface for cross-Principal binding; (c) a single
> caveat / authorization vocabulary for both. The unification does *not*
> buy: erasing the cell-vs-federation distinction at the storage or
> consensus layer — those distinctions are real and load-bearing.
>
> Migration: **layered overlay first** (add `Principal` trait without
> touching the underlying types). Revisit collapse only after Silver
> Vision lands and we have lived with the trait for some months.

The rest of the doc earns that conclusion.

---

## §1. The homomorphism, axis by axis

The brief proposes a 9-row mapping. I'll walk each, give evidence in
favor, give counter-evidence, and resolve.

### 1.1 `owning_key: Ed25519` ↔ `committee_pubkeys: Vec<BLS pubkey>`

**Cell:** Each cell has a single Ed25519 public key
(`cell::cell::Cell::public_key`); the cell's owning principal signs
turns and authorizes mutations via `Authorization::Signature`.

**Federation:** A federation is a committee of Ed25519 (or BLS)
keys; quorum certificates aggregate signatures over a threshold
(`federation::types::FederationCommittee`, `AttestedRoot::quorum_signatures`,
`AttestedRoot::threshold_qc`).

**Homomorphism strength:** Strong, modulo arity. A cell's owning key
is a *committee of one*; a federation's committee is a *generalization*
to N keys with a threshold. The "solo federation" case
(`FEDERATION-UNIFICATION-DESIGN.md §1`) already collapses to "committee
of one, threshold = 1" — which is *isomorphic to a cell's owning-key
authority*.

**Counter-evidence:** the *signing operation* differs. A cell's owning
key produces one Ed25519 signature; a federation's committee produces
either many Ed25519 signatures or one aggregated BLS signature. The
verifier path is different.

**Resolution:** the *authority abstraction* is "a thing that can
authorize a transition." Both are special cases of:
```
enum Authority {
    SingleKey(Ed25519PublicKey),
    Threshold {
        members: Vec<PublicKey>,
        threshold: u32,
        // optional: BLS aggregate for constant-size QC
        bls_committee: Option<FederationCommittee>,
    },
    Custom(WitnessedPredicate),  // ← multisig as predicate
}
```
The cell case is `SingleKey`; the federation case is `Threshold` with
N≥2; multisig cipherclerks / "small federations" are `Threshold` with
2≤N≤~16. Custom encompasses everything else.

This is *the* unification axis. It's already partially in tree:
`Authorization::Signature` ↔ `Authorization::Custom { predicate: ...
multisig vk ... }` realize the first and third variants; the
threshold variant is implicit in federation receipt verification but
not surfaced as an authority *type*.

### 1.2 `id = H(owning_key)` ↔ `federation_id = H(committee_pubkeys)`

**Cell:** `CellId = BLAKE3(public_key || token_id)`
(`cell::id::CellId::derive_raw`, `cell::derivation`).

**Federation:** `FederationId = BLAKE3("dregg-fed-id-v1", sorted_members,
epoch)` (`federation::identity::derive_federation_id_with_epoch`).

**Homomorphism strength:** Very strong. Both ids are *commitments to
the authority*, not random tags. The federation case adds `epoch`
because committees rotate; the cell case adds `token_id` because cells
are partitioned into token domains. Both produce content-addressed,
order-independent identifiers.

**Counter-evidence:** the cell case includes `token_id` (which is *not*
authority data), and the federation case includes `epoch` (which *is*
authority-state — the committee at this moment). These are different
*non-authority* mix-ins.

**Resolution:** factor the id derivation as:
```
id = H("dregg-principal-id-v1", authority, scope)
```
where `scope` is the cell-vs-federation discriminator plus any
non-authority mix-ins (`token_id` for cells, `epoch` for federations).
This is mechanical: both existing derivations are special cases.

### 1.3 `state: Vec<FieldElement>` ↔ `attested_root` (Merkle over ledger)

**Cell:** State is a small fixed vector — 8 field slots + nonce + balance
(`cell::state::CellState`, `STATE_SLOTS = 8`). The whole vector fits in a
single AIR row's worth of public input.

**Federation:** "State" is the *entire ledger of cells*, summarized by
`AttestedRoot::merkle_root` (a Merkle root over all cells in the
federation). Unbounded in cardinality; the Merkle root is the
constant-size commitment.

**Homomorphism strength:** Conceptually strong; structurally distant.
Both represent "the principal's current state," and both produce a
*commitment* to that state. But the underlying data shapes differ by
orders of magnitude (8 slots vs. unbounded Merkle tree).

**Counter-evidence:** A federation's state is *itself a collection of
cells*. The Merkle leaves are cell-state commitments. So a federation's
state is recursively constituted from its constituent principals'
states. A cell's state is *not* further decomposable. This is the
fundamental size-of-state asymmetry.

**Resolution:** the *abstraction* is `state_commitment: [u8; 32]`.
Both have one; the producer-side mechanics differ:

- Cell: `state_commitment = Poseidon2(state_slots || nonce || balance)`
  (one hash).
- Federation: `state_commitment = MerkleRoot(cell_state_commitments)`
  (one Merkle aggregation).

A unified `Principal::state_commitment() -> [u8; 32]` is type-correct
and well-defined; the variance lives in the implementation, not the
interface.

This is also the deepest *structural* point of the homomorphism:
**a federation's state IS a Merkle aggregation of cell states.** A
federation is a "principal whose state is a Merkle ledger of other
principals' state-commitments." This is recursive by construction; §2
exploits this.

### 1.4 `program: CellProgram` (slot caveats) ↔ blocklace ordering rules

**Cell:** `CellProgram::Predicate(Vec<StateConstraint>)` declares slot
caveats — invariants that every state transition must preserve.
Static, predicate-only.

**Federation:** the "program" is the blocklace's ordering and finality
rules (Cordial Miners DAG ordering, supermajority finality,
equivocation policy via `GovernedReferenceGroup` in
`blocklace::constitution`). Dynamic, process-oriented.

**Homomorphism strength:** *Weak.* This is the place where the analogy
strains hardest.

**Counter-evidence:**

- A cell's program is a *predicate* over state. It can be evaluated
  point-wise; given a candidate transition, the predicate either
  accepts or rejects. There is no notion of "running the program."
- A federation's consensus rule is a *process*. It is not a predicate
  that accepts or rejects a state; it is a multi-round protocol with
  message passing, voting, leader selection, and finality. The
  "is this state valid" question is a function of the *history of
  messages*, not the state alone.

This distinction matters: slot caveats can be checked by a static
verifier with no state beyond the cell's previous and proposed
commitments. Blocklace finality requires reasoning about the
quorum certificate, the DAG structure, the round numbering, etc.

**Resolution attempt 1 — "factor out the static fragment":** Some
blocklace invariants *are* static-predicate-shaped:
- "the finality round only increases" → `StateConstraint::Monotonic`
  on a `finality_round` slot.
- "the committee changes only via an authorized epoch transition" →
  `StateConstraint::Custom(epoch_transition_vk)`.
- "no two blocks at the same (creator, sequence) coexist" →
  `StateConstraint::Equivocation` (would need a new variant; checking
  this requires set-of-prior-blocks, which is fine for a
  federation's program but not for a cell's).

These are *invariants on federation state-at-rest*. They are
expressible as slot caveats on a federation-as-cell viewpoint. **But
they are not the totality of the consensus rule.** The dynamic
parts — message dissemination, leader election, view-change — are
*not* state predicates.

**Resolution attempt 2 — "the consensus rule has a static-predicate
fragment and a process fragment":** the unified abstraction
acknowledges both. A `Principal::program` returns *the predicate
fragment*; the process fragment is lifted out into a separate
`ConsensusEngine` type that owns the blocklace.

This is the path I think we should take. §4 makes it concrete.

### 1.5 `nonce: u64` ↔ epoch / round / DAG depth

**Cell:** Each cell has a strictly-monotonic nonce
(`cell::state::CellState::nonce`); every turn bumps it by one. Total
order, single sequence.

**Federation:** The closest analog is `(committee_epoch,
finality_round)`. But the *order* of turns within a federation is a
DAG (blocklace), not a sequence. There is no single `next_nonce` for
the federation.

**Homomorphism strength:** Weak.

**Counter-evidence:** the cell's nonce is the *unique identifier
of the cell's next action*. There is no analogous "the federation's
next action" — multiple cells are simultaneously producing turns, and
the blocklace partial-orders them.

**Resolution:** factor the abstraction at the *Principal* level into
two distinct concepts:

- `Principal::action_counter` — for single-actor principals (cells),
  this is the nonce. For federations, this is undefined (the
  federation doesn't take "actions"; its constituent cells do).
- `Principal::progress_marker` — for single-actor principals, this
  is also the nonce. For federations, this is `(epoch,
  finality_round, attested_root)`. It is the answer to "at what
  point in this principal's history are we?"

These are not the same axis. A cell's nonce conflates them
(every action advances the marker); a federation's epoch and
round advance independently of (and aggregate over) individual
cell actions.

**Open question, returned below in §3:** is the lack of a federation-
level "action counter" actually a problem, or just a difference?
I'll argue it's a difference, not a problem.

### 1.6 Single-key authorization ↔ Threshold-sig authorization

Covered in §1.1. The authority abstraction subsumes both.

### 1.7 Cell-to-cell CapTP ↔ Cross-federation CapTP

**Cell:** CapTP delivery between cells within a federation:
`Authorization::CapTpDelivered` on the receiving turn carries the
introducer (a federation pubkey) and the sender (recipient_pk from
the handoff cert) signatures.

**Federation:** Cross-fed CapTP is the *same wire shape* —
`HandoffCertificate` carries the introducing federation's pubkey
plus the receiving entity's pubkey
(`captp::handoff`, `AUDIT-distributed-semantics.md §2-3`). The
delivery on the receiving federation produces a turn that ratifies.

**Homomorphism strength:** Strong.

The CapTP layer is *already* unified: a `HandoffCertificate` doesn't
care whether the introducer's federation is "this one" or "another
one"; both produce certs the receiver verifies the same way. This is
arguably the most successful unification already in tree.

**Counter-evidence:** none of consequence. The trust path differs
(intra-fed: blocklace ordering closes the loop; cross-fed: AttestedRoot
chains close the loop), but the *cert layer* is uniform.

**Resolution:** confirm this and lift `Authorization::CapTpDelivered`
to the `Principal` abstraction. Today it works at both scales without
modification, but the verifier code paths are duplicated; unification
reduces that.

### 1.8 `WitnessedReceipt` chain ↔ AttestedRoot chain

**Cell:** Each cell maintains a chain of `WitnessedReceipt`s, each
referencing the prior via `previous_receipt_hash`. This is the
cell's per-actor turn log
(`WITNESSED-RECEIPT-CHAIN-DESIGN.md`).

**Federation:** Each federation produces a chain of `AttestedRoot`s
(each `height` ↑ 1) signed by a threshold of the committee. This is
the federation's state-commitment log.

**Homomorphism strength:** Strong.

Both are "monotonic chains of state-commitments with authority
attestations." A cell's WR chain attests "cell X moved from state
C_i to C_{i+1} via turn T_{i+1}." A federation's AttestedRoot chain
attests "federation F moved from state R_i to R_{i+1} at height
{i+1}."

**Counter-evidence:** the *contents* of each link differ. A WR
carries the full `Turn` and per-cell proof; an AttestedRoot carries
only the Merkle root + height + quorum signatures. The WR is
operationally complete (the receiver can replay); the AttestedRoot
is summary-only.

**Resolution:** factor as `Principal::state_commitment_chain()`. The
chain shape is uniform (`prev_hash, new_commitment, attestation`);
the per-link payload differs by Principal kind. A cell's link is a
*WitnessedReceipt*; a federation's link is an *AttestedRoot*.

The cross-Principal binding (§6, also see `CROSS-CELL-COORDINATION.md
§4.2`) is the same primitive at either scale: a chain reference plus
an authority verification.

### 1.9 `peer_exchange` (sovereign bypass) ↔ (?) direct cross-fed

**Cell:** `cell::peer_exchange::PeerStateTransition` lets two cells
exchange signed state transitions without the federation in the trust
path.

**Federation:** there is *no analog* today. Cross-federation
communication routes through cross-fed CapTP via the bridge / known
federations registry; there is no "two federations exchange attested
roots directly without an intermediary" path.

**Homomorphism strength:** Asymmetric — the analog doesn't exist on
the federation side.

**Should it?** Two federations *could* exchange `AttestedRoot`s
directly: an attested root is self-verifying (signature against
committee + epoch). The cross-fed bridge currently routes everything
through the bridge cells / observer model, but a *direct* federation-
to-federation handshake (one federation accepts another federation's
attested roots into its `KnownFederations` registry, mutually) is the
cross-fed analog of `peer_exchange`.

This is the *peer_exchange-at-federation-scale* gap. It is not
algebraically deep; it's a missing surface. Adding it would consist
of:
- A signed inter-federation message: "I am federation `F_A`; here is
  my AttestedRoot at height `h`."
- A receiving federation's `KnownFederations::accept_root()` that
  verifies and stores it.

**Resolution:** confirm the gap; flag as future work; do not
introduce in the current `Principal` proposal.

### 1.10 Summary table, augmented

| Axis | Cell | Federation | Homomorphism | Unify via |
|------|------|------------|--------------|-----------|
| Authority | `owning_key: Ed25519` | `committee_pubkeys + threshold` | Strong | `Authority` enum |
| Id | `H(public_key, token_id)` | `H(members, epoch)` | Very strong | `Principal::id` |
| State | `Vec<FieldElement>` (small) | Merkle root over ledger | Conceptual | `Principal::state_commitment` |
| Program | Slot caveats (predicate) | Blocklace rules (process) | Weak | Predicate fragment via `Principal::program`; process via `ConsensusEngine` |
| Counter | `nonce` (sequence) | `(epoch, round, root)` (DAG marker) | Weak | Two distinct concepts on `Principal` |
| Authorization | Single Ed25519 sig | Threshold QC | Strong | `Authority` enum (same as row 1) |
| CapTP | Cell-to-cell | Cross-fed | Strong (already unified) | Confirm and lift to `Principal` |
| State-commitment chain | `WitnessedReceipt` chain | `AttestedRoot` chain | Strong | `Principal::commitment_chain` |
| Federation-bypass | `peer_exchange` | (missing) | Asymmetric | Future: cross-fed direct exchange |

**Reading of the table:** 6 of 9 axes have strong-or-stronger
homomorphism. 2 are weak (program, counter) but resolve with shape
factoring. 1 is asymmetric (peer_exchange) and points to a real but
deferrable gap.

---

## §2. Implications if we adopt this view fully

Suppose we commit. What follows?

### 2.1 Multi-key cells are small federations

A cell with a multisig authorization (`Authorization::Custom { predicate:
... BlindedSet ... }`) is *already* a small federation: it has a
committee (the multisig signer set), a threshold (M), an id
(`H(public_key, token_id)` — but `public_key` is conventionally
the multisig group's aggregate or root identifier), and a state
(its slots).

Today this is encoded via `Authorization::Custom` + a
`WitnessedPredicate`. Under the unified view, it would be encoded as
`Authority::Threshold { members, threshold, ... }` directly on the
cell. This is more direct and avoids one layer of indirection.

**Concrete win:** the `governed-namespace` cell could declare its
threshold authority structurally rather than enforcing it via a
`Cases` program + Custom auth witness. The verifier could read the
authority from the principal type and apply it uniformly.

**The faceted-caps composition:** today, `cell::facet::Facet` and
`cell::capability::CapabilitySet` partially express the "multi-key
cell" idea — different capabilities have different reach. The
proposal in §4 makes this orthogonal: facets are about *what
capabilities are exercisable*; authority is about *who can authorize
the cell's own actions*. They don't conflict.

### 2.2 Federation = cell with committee + program

Restated: a federation is a `Principal` with `authority = Threshold`,
`state_commitment = MerkleRoot(...)`, `program = (blocklace static
fragment, plus process running elsewhere)`. The recursion is real:
a federation's state is a ledger of cells, each of which is itself
a `Principal`.

**Recursive nesting becomes possible.** A *federation of federations*
(a "super-federation") would be a `Principal` whose state is a
Merkle aggregation of federation-level `AttestedRoot`s. This is the
shape of the proposed cross-federation registry, hoisted to a
principal-in-its-own-right.

We don't have a use case for super-federations today. But the
abstraction is *consistent*; it doesn't break by allowing them.

### 2.3 Slot caveats on federations

If federations are `Principal`s with state, they can have *slot
caveats*. Examples:

- "This federation's threshold can only increase" — `StateConstraint::
  Monotonic` on the `threshold` slot.
- "This federation's committee size is bounded" — `StateConstraint::
  RangeBound` on the `committee_size` slot.
- "This federation's epoch only advances" — `StateConstraint::
  Monotonic` on `epoch`.

These are *new invariants* the existing federation model doesn't
enforce structurally (they live as conventions in the constitution).
Lifting them to slot caveats would make them first-class.

**Caveat:** the federation's state today is `AttestedRoot`-summarized,
not slot-by-slot. To apply slot caveats on a federation, we would
need to model the federation's state as a *fixed-shape vector of
slots* alongside the unbounded Merkle ledger. This is mechanical
(the constitution already has these fields) but is real work.

### 2.4 CapTP delivery uniform at either scale

The `Authorization::CapTpDelivered` variant doesn't care whether
the introducer is a federation or a cell. Today it accepts an
`introducer_pk` that is conventionally a federation key; making
this uniform across both cell and federation introducers is a
minor change (the cert's `introducer` field already accepts a
generic 32-byte id).

**Concrete win:** a cell can introduce another cell to a third
party without involving the federation in the cert chain. The
delegation chain becomes uniform: any `Principal` can introduce.
The existing handoff protocol supports this; it just needs the
abstraction to acknowledge it.

### 2.5 `AttestedRoot` is the federation-level state commitment

This is the framing payoff. An `AttestedRoot` *is* `Principal::
state_commitment()` for a federation. The current code already
treats it this way conceptually; the unification makes it explicit
in the type system.

The bridge layer (`bridge::midnight_observer`) consumes attested
roots as the federation's state evidence. Under the unified view,
it is consuming `Principal::state_commitment()` for a federation
Principal — which is exactly the same shape as another part of
the bridge that consumes a cell's `state_commitment`.

---

## §3. Where the analogy breaks (be specific)

I owe an honest accounting. Here are the irreducibles.

### 3.1 State shape and cardinality

A cell's state is `Vec<FieldElement>` of fixed length 8 (plus nonce
+ balance). A federation's state is an unbounded Merkle aggregation
over the entire cell ledger. The abstraction `state_commitment ->
[u8; 32]` papers over this, but the producer code is fundamentally
different:

- The cell can recompute its state commitment in constant time.
- The federation must traverse a Merkle tree (or maintain an
  incremental Merkle structure) to update its commitment.

Anything that wants to *read* a cell's state directly can; anything
that wants to read a federation's state must hold a Merkle proof
against the root or scan the ledger.

**Implication for unification:** the `Principal` trait can expose
`state_commitment()`, but it cannot uniformly expose `state_slot(i)`
without an additional Merkle-membership proof for federations.
This is fine; the trait can have an `state_slot_with_proof(i, proof)`
that takes optional witness data, and cells implement it trivially
while federations implement it with proof verification.

### 3.2 Sequential nonce vs. DAG progress

A cell has a single sequential nonce; every turn bumps it. A
federation has *no single sequence*: many cells produce turns
simultaneously, ordered by the blocklace into a DAG. There is no
"the federation's next action."

**Implication for unification:** `Principal::nonce()` is not
meaningful for federations. We must split this conceptually.
`Principal::progress_marker()` (returns `(epoch, height, root)`
for federations, `nonce` for cells) is fine; *action counter* is
cell-only.

This is the place where I'd resist the temptation to overshoot.
Some refactors will want a uniform "what is the next nonce" — and
will be unable to express it for federations. The right answer is
"federations don't have action nonces; they have *constituent cells*
with action nonces. To get the next nonce of cell X in federation F,
ask cell X."

### 3.3 Owning-key signs single actions; committee threshold-signs aggregated state roots

A cell's owning key signs *individual turns*. A federation's
committee threshold-signs *state roots*, not individual turns.
Individual turns are signed by the executor (some federation
member acting on behalf of the cell whose action it is); the
committee's role is to *finalize* via supermajority over the
blocklace, then attest to the rolled-up state root.

**Implication for unification:** the `Authority::Threshold` variant
must specify *what is signed*. Cell turns: the canonical signing
message per-action. Federation state roots: an `AttestedRoot`'s
canonical encoding. These are different message types.

A unified `Authority::verify(message: &[u8]) -> bool` works at both
scales — the *abstraction* is "verify a signature over a message" —
but the *messages* are different. The trait is still sound; it's
just that callers must construct the right message.

### 3.4 Cell programs are deterministic finite predicates; consensus rules are processes

The deepest distinction. A `CellProgram` evaluates to accept/reject
on a candidate transition; it has no internal state, no message
passing, no rounds. The blocklace's finality logic is a *running
protocol*: receive blocks from peers, accumulate acknowledgments,
declare finality when supermajority criteria are met. It is not
expressible as a predicate over state-at-rest.

**Implication for unification:** the program-level homomorphism is
*partial*. We can lift the *static fragment* of the consensus rule
(monotonicity invariants, equivocation policy as set-of-prior
checks, etc.) to slot caveats. The dynamic fragment lives outside
the `Principal` abstraction in a separate `ConsensusEngine` type.

This is the same factorization classical database theory makes
between *invariants* (predicate on state) and *transactions*
(procedure that mutates state respecting invariants). Cells have
trivial transactions (one Turn per nonce); federations have
non-trivial transactions (Cordial Miners DAG ordering).

The unification is real but bounded.

---

## §4. The unified `Principal` abstraction

Concrete sketch. Names are placeholders; semantics are the contract.

### 4.1 Shape

```rust
pub trait Principal {
    /// Stable, content-addressed identifier.
    fn id(&self) -> PrincipalId;

    /// The authority that authorizes mutations of this principal's state.
    fn authority(&self) -> Authority<'_>;

    /// Current state commitment (Poseidon2 hash for cells; Merkle root
    /// for federations).
    fn state_commitment(&self) -> [u8; 32];

    /// Static-predicate fragment of this principal's invariants.
    /// For cells: their `CellProgram`'s slot caveats. For federations:
    /// the static fragment of their consensus rule (monotonic epoch,
    /// monotonic finality round, etc.).
    fn program_predicate(&self) -> &ProgramPredicate;

    /// Progress marker: at what point in this principal's history we are.
    /// For cells: `Marker::Sequence(nonce)`.
    /// For federations: `Marker::DagAt { epoch, height, root }`.
    fn progress_marker(&self) -> Marker;

    /// Chain of state commitments produced by this principal.
    /// For cells: `WitnessedReceipt` chain.
    /// For federations: `AttestedRoot` chain.
    fn commitment_chain_tip(&self) -> CommitmentLink;
}

pub enum Authority<'a> {
    SingleKey {
        public_key: &'a [u8; 32],
        sig_alg: SigAlg,  // Ed25519 today, postquantum later
    },
    Threshold {
        members: &'a [PublicKey],
        threshold: u32,
        bls_committee: Option<&'a FederationCommittee>,
    },
    Custom {
        predicate: &'a WitnessedPredicate,
    },
}

pub enum Marker {
    Sequence(u64),                                       // cells
    DagAt { epoch: u64, height: u64, root: [u8; 32] },   // federations
}

pub enum CommitmentLink {
    Receipt(WitnessedReceipt),     // cells
    Root(AttestedRoot),            // federations
}

pub struct PrincipalId([u8; 32]);
// derived as H("dregg-principal-id-v1", authority_canonical, scope)
```

### 4.2 What this buys

**At the type-system level:**

- A function that takes any `impl Principal` works at either scale.
  `verify_state_commitment_against_authority(p, sig)` is the same
  code path for cells and federations.
- The CapTP `Authorization::CapTpDelivered` variant can be re-typed
  to accept a `Principal` introducer, which is currently encoded
  but not enforced.
- The `intent::cross_fed` shape can be re-typed in terms of
  `Principal` instead of having parallel code paths for
  "intra-fed" and "cross-fed."

**At the documentation level:**

- The audits (`AUDIT-federation.md`, `AUDIT-cell.md`,
  `AUDIT-distributed-semantics.md`) develop the same vocabulary
  independently; the trait gives them a shared one.
- Multi-cell tutorials no longer need a "...and by the way, a
  federation is similar but different" footnote.

**At the implementation level:**

- The recursive nesting is type-correct, even if we don't use it
  yet.
- Future cross-Principal binding (γ.2 extended to federations as
  participants) gets a natural place to live.

### 4.3 What it does not change

- No collapse of the underlying types. `Cell` stays `Cell`;
  `Federation` stays `Federation`. The trait is a viewing lens.
- No new effect kind. The existing effect alphabet is unchanged.
- No change to the per-Turn AIR shape. Per-cell proofs stay
  per-cell.
- No change to the blocklace's consensus implementation. The
  `ConsensusEngine` type owns it; `Principal` exposes only the
  output.

---

## §5. Migration story

Two viable paths, three timing recommendations.

### 5.1 Path A: layered overlay

Add `Principal` trait + implementations for `Cell` and `Federation`
without modifying their internal shape. Callers that want the
unified view import the trait; callers that don't see no change.

**Pros:**
- Zero-risk; trait is additive.
- Can land in a single PR per consuming module.
- Lets us *evaluate* the abstraction in practice before committing.

**Cons:**
- The two underlying types remain duplicated. We don't get the
  type-system payoff of "one fewer type to keep in sync."
- The trait introduces an indirection layer that callers must
  navigate.

### 5.2 Path B: major refactor (collapse into one type)

Introduce `Principal` as a concrete enum:
```rust
pub enum Principal {
    Cell(CellInner),
    Federation(FederationInner),
}
```
Replace all uses of `Cell` and `Federation` with this enum;
delete the separate types.

**Pros:**
- Type-system reflects the unified mental model.
- One canonical principal type across the codebase.
- Cross-Principal logic becomes truly uniform.

**Cons:**
- High-risk refactor; touches everything from storage to RPC.
- Existing storage formats serialize `Cell` and `Federation`
  separately; collapsing requires migration.
- Callers that legitimately only care about "this is a cell, not
  a federation" lose static type discrimination.
- The blocklace's per-federation logic gains a runtime-dispatch
  cost.

### 5.3 Recommended ordering

1. **Now (Q-current):** *Just write the design doc* (this one). Do
   not modify code.
2. **Post-Silver-Vision:** Path A (layered overlay). The Silver
   Vision E2E work (`SILVER-VISION-E2E-VERIFICATION.md`) is
   currently in flight and would be disrupted by a new abstraction.
   Let it land first.
3. **Post-Silver-Vision + 1 quarter:** evaluate. If the trait has
   simplified the cross-Principal code paths and is actually used,
   consider Path B. If the trait is a wart that nobody invokes, drop it.

This is the conservative path. It also gives the best information
gain: we learn whether the abstraction is *actually useful* before
committing to the refactor.

---

## §6. Implications for γ.2

The cross-cell coordination story (`CROSS-CELL-COORDINATION.md`)
becomes a special case of cross-`Principal` coordination.

### 6.1 Cross-cell γ.2 and cross-federation AttestedRoot binding

Today these are separate machinery:

- γ.2 binds cells: per-cell PI accumulators + canonical id derivation.
- Cross-fed binding: AttestedRoot signature + KnownFederations
  registry.

Under the unified view, both are *cross-Principal commitments*. A
unified primitive:
```
struct PrincipalCommitmentBinding {
    principal_id_A: PrincipalId,
    principal_id_B: PrincipalId,
    binding_id: [u8; 32],  // canonical effect id
    commitment_A: [u8; 32],  // state_commitment of A post-effect
    commitment_B: [u8; 32],  // state_commitment of B post-effect
    authority_A: AuthorityAttestation,
    authority_B: AuthorityAttestation,
}
```

For cell-cell: this reduces to γ.2 Phase 1's pairwise binding.
For federation-federation: this is the cross-fed handshake (signed
attested roots on each side, plus binding-id linking the underlying
events).
For cell-federation: this is the bridge layer's lock/unlock proof
(cell-side: the lock event's γ.2 binding; federation-side: the
attested root containing the lock).

This is *more general than γ.2 today*, but not by adding a new
algebraic primitive — by *re-typing* γ.2's existing primitive in
terms of `Principal`.

### 6.2 The accumulator on `outgoing_*_root` could bind cross-federation transfers

γ.2's `OUTGOING_TRANSFER_ROOT` accumulator absorbs `(transfer_id,
peer_cell_id, amount_lo, amount_hi)` per row. If `peer_cell_id` is
generalized to `peer_principal_id`, the same accumulator binds
cross-federation transfers (treating the destination federation as a
`Principal`).

This is the cleanest direction for "γ.2 cross-fed Phase 1.5"
(`STAGE-7-GAMMA-2-PI-DESIGN.md §4.6` flags it as future work). The
Principal abstraction makes the generalization obvious.

### 6.3 Bridge nullifier set as a special Principal

The bridge's nullifier set is a long-lived state object whose
program is "no nullifier may appear twice." Under the unified view,
it is:
```
Principal {
    authority: Authority::Threshold { ... bridge federation committee ... },
    state_commitment: H(nullifier_set_merkle_root),
    program_predicate: ProgramPredicate::Append { uniqueness: Required },
    progress_marker: Marker::DagAt { ... },
}
```

This makes the bridge nullifier set first-class. It is a
*federation-like principal* with a *cell-like program* (append-only
with uniqueness invariant). The hybrid is fine; the trait
accommodates it.

---

## §7. Implications for blocklace

Blocklace is the federation-`Principal`'s "program runtime" — the
process-fragment alluded to in §3.4.

### 7.1 Could blocklace's per-block invariants be expressed as `StateConstraint`s?

Partially. Let me enumerate.

**Yes (static-predicate-shaped):**
- Finality round monotonicity: `StateConstraint::Monotonic` on
  `finality_round`.
- Block sequence per creator: `StateConstraint::Monotonic` on each
  creator's `(creator_id, sequence)` slot — would need a multi-
  dimensional monotonicity variant, or a per-creator slot vector.
- Authorized creator set: `StateConstraint::SenderAuthorized` (with
  `AuthorizedSet::BlindedSet { committee_root }`) on every block-
  appending operation.

**Yes (with extensions):**
- Equivocation policy ("no two blocks at same (creator, sequence)"):
  this is a *non-membership* invariant against an unbounded set
  (all prior blocks). It is expressible as `StateConstraint::Custom`
  with a witnessed-predicate that proves non-membership in the prior
  blockset. The cell-level non-membership primitive exists
  (`circuit::non_membership`). Lifting to federation-scale is mechanical.

**No (process-shaped):**
- Cordial Miners supermajority finality: the rule that a block is
  final iff a supermajority of subsequent blocks acknowledges it.
  This is not a predicate on state; it is a function of the
  *future* DAG history. No `StateConstraint` captures it.
- Liveness / dissemination: blocks must eventually be delivered.
  Not a state predicate; a network/availability property.
- View / round advancement: implicit in the DAG depth; no static
  predicate.

### 7.2 The process / predicate gap formalized

Define:
- **Predicate invariants:** properties of the state-at-rest. "The
  state satisfies P." Checkable by a static verifier given the
  state.
- **Process invariants:** properties of the trajectory. "The state
  was produced by running protocol Q." Checkable only by replaying
  Q or accepting a proof-of-replay (e.g., a recursive STARK over
  the protocol's transitions).

Slot caveats handle predicate invariants. Blocklace's consensus
rule includes both kinds; only the predicate fragment is liftable.

The process fragment is not without recourse — *a recursive STARK
over the blocklace's transitions* would, in principle, allow
encoding "the state was produced by running Cordial Miners" as a
verifiable claim. This is the
`STAGE-7-PLUS-DESIGN.md` direction: chain-IVC of per-turn proofs
proves "the federation's state was reached by a valid sequence of
turns." Extending this to "the federation's state was reached by a
valid Cordial Miners run" is a heavier lift but on the same
spectrum.

For now, the practical answer: **predicate invariants via slot
caveats; process invariants via blocklace machinery (out-of-AIR);
optional future bridging via chain-IVC.**

---

## §8. Open questions for the designer

The architectural calls that I think only you can make.

### 8.1 Path A or Path B?

Layered overlay (low risk, lower payoff) or major refactor (high
risk, higher payoff)?

My vote: **Path A first**, evaluate, possibly Path B later. But
Path A has a real cost — adding a trait without using it
extensively is a kind of dead weight. If we go Path A and then
don't actually adopt it, we will have generated bytecode for no
benefit.

A *third option*, which I lean toward over both: **don't introduce
`Principal` as a trait or enum yet. Instead, write *this doc* and a
few targeted refactors that hand-roll the unification at specific
seams** (e.g., re-type `Authorization::CapTpDelivered`'s introducer
field; widen γ.2's `peer_cell_id` to `peer_principal_id` for
cross-fed Phase 1.5). The trait can come *after* we've seen those
seams converge.

### 8.2 Is `MerkleMembership`-against-federation-state already half of the answer?

`WitnessedPredicate::MerkleMembership` lets a cell prove
"this leaf is in this Merkle root." If the Merkle root is a
federation's `AttestedRoot::merkle_root`, then this predicate is
*already* "prove I am a cell in this federation."

If so, then the federation-Principal abstraction is half-implemented:
the federation-as-state-commitment-root is already a verifiable
thing for arbitrary cells (modulo a `WitnessedPredicate` proof). The
remaining work is the *authority* abstraction (threshold vs. single
key) and the *progress marker* abstraction.

**This is the easiest path:** don't introduce `Principal` as a new
type; introduce the *missing pieces* (a unified `Authority` shape,
a unified `progress_marker` accessor) and let `MerkleMembership` /
existing primitives carry the rest.

### 8.3 What is the canonical cross-Principal binding shape?

If cell-cell γ.2 binding and federation-federation AttestedRoot
exchange are facets of the same primitive, what is the canonical
shape? My §6.1 sketch (`PrincipalCommitmentBinding`) is one
possibility, but I'm not sure it's the right one. Specifically:

- Should it be a *single* artifact carrying both sides' attestations
  (clean, but requires both sides to coordinate)?
- Should it be *two* artifacts (one per side) that a third party
  joins (the γ.2 verifier model — works at any cardinality)?
- Should it be a *Merkle inclusion in a global state* (the
  AttestedRoot model — works at federation scale, less elegant at
  cell scale)?

The γ.2 verifier model (two artifacts, joined by canonical id) is
the most general; I'd start there.

### 8.4 What is the right shape for "process invariants"?

§7.2 identifies the predicate/process gap. Some open paths:

- **Continue keeping process invariants out-of-AIR.** Blocklace
  Rust code enforces them; the `Principal::program_predicate` is
  predicate-only.
- **Lift process to per-block AIR.** Every blocklace block carries
  a proof of "I respect Cordial Miners rules." Heavier but more
  uniform.
- **Lift process to chain-IVC.** A single recursive STARK proves
  the entire blocklace history is rule-respecting. The
  `STAGE-7-PLUS-DESIGN.md` direction, applied to consensus rather
  than per-turn execution.

These are independent of the federation-as-cell question, but the
unification framework will shape *where* we put the answer.

### 8.5 Should `peer_exchange`'s federation analog exist?

§1.9 flagged the gap. The use case: two federations want to
exchange attested roots directly without an intermediary, the
same way two cells exchange `PeerStateTransition` directly.

Trust implication: each federation's committee is its own root of
trust. The receiver federation must already trust the sender's
committee (via prior `KnownFederations` registration).

I don't see harm in adding this; I don't see urgent demand either.
Flag for after Silver Vision.

### 8.6 What about facets and partial-authority cells?

Today `cell::facet::Facet` carries the "partial authority over a
cell" idea — a facet capability lets the holder exercise some but
not all of the cell's authorized actions. Under the unified
view, facets are *delegated sub-authorities*: a cell with N facets
is like a federation with N sub-committees each owning a fragment
of the authority.

This is suggestive but not crisp. The federation-as-cell mapping
treats *authority* as a single root (threshold or single key). The
faceted-cap model treats authority as a *lattice* (multiple
delegate sub-authorities). Both are real; reconciling them is its
own design.

### 8.7 Where does `governed-namespace`-style hosted-app belong?

A `governed-namespace` cell is a cell with a complex
`CellProgram::Cases` program that enforces M-of-N committee
votes on mutations. Under the unified view, this is a *cell-shaped
principal with federation-shaped authority*: state is small (slot
vector), but authority is a threshold committee.

This is fine — the `Authority::Threshold` variant accommodates it
— but it means cells and federations are not partitioned by
"single-key vs. threshold-auth." Both can be either. The real
distinction is *state shape* (small vector vs. unbounded ledger)
and *progress shape* (sequence vs. DAG).

This subtlety strengthens the case that the right unification is
the `Authority` enum (the most-unifiable axis), not the cell-as-
federation type collapse.

---

## §9. Verdict

The federation-as-cell mapping is real and useful, but the right
intervention is **surgical, not architectural**:

1. **Lift the `Authority` abstraction** to a unifying enum across
   single-key and threshold-and-custom. This is the most-unifiable
   axis and the one with the most leverage. Do this first.

2. **Confirm and document the `AttestedRoot` ↔ `state_commitment`
   homomorphism.** Let `WitnessedPredicate::MerkleMembership` carry
   the cross-Principal membership claims. No new types.

3. **Don't introduce `Principal` as a trait or enum yet.** Wait
   until the surgical changes converge enough that a unifying
   abstraction would carry meaningful weight.

4. **Keep blocklace's process invariants out-of-AIR for now**;
   revisit chain-IVC consensus proofs after Silver Vision.

5. **Treat slot caveats on federations as a real follow-up** — the
   static-predicate fragment of consensus rules wants slot-caveat
   shape (monotonic epoch, monotonic round, bounded threshold).
   This is a self-contained piece of work, ~1 sprint.

The one-line architectural recommendation, restated:

> **Lift `Authority` to a unifying enum across single-key, threshold,
> and custom; let `MerkleMembership` carry the rest of the
> federation-as-state-commitment-root story; defer the `Principal`
> trait/type until those surgical changes show convergence.**

The unification is *coming*. Forcing it before the seams converge
buys the wrong abstraction. Letting it emerge from converging seams
buys the right one.

---

## §10. Closing

Cells and federations are *almost* the same shape. Six axes are
strongly homomorphic; two are weakly homomorphic but factorable;
one (peer_exchange's federation analog) is a real gap.

The wrong way to act on this is to immediately collapse the types.
The right way is to make the *interfaces* increasingly uniform —
authority abstraction, state-commitment exposure, CapTP at either
scale — until the underlying types are nearly interchangeable. Then,
*if* it still helps, collapse.

The companion question — whether γ.2's pairwise binding is enough —
is answered in `CROSS-CELL-COORDINATION.md`. The answer there
(yes, pairwise is enough, gaps are ergonomic) reinforces the answer
here: if the algebraic primitive set is closed, the structural
unification is *helpful* but not *load-bearing*. We don't need to
unify to make γ.2 work; γ.2 works because pairwise composition over
a closed primitive set suffices.

The federation-as-cell view is a *consolidating lens*. It is not
a *prerequisite* for any current work, and it is not a
*correctness* concern; it is a *clarity* concern. Apply with
proportionate energy.
