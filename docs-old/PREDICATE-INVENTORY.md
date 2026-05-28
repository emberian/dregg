# PREDICATE-INVENTORY — every predicate in dregg, and a unification

**Date:** 2026-05-24. **Status:** study/design. Read-only on code; one new
`.md`. **Companion docs:** `SLOT-CAVEATS-DESIGN.md`,
`SLOT-CAVEATS-EVALUATION.md`, `BOUNDARIES.md`,
`DFA-RATIONALIZATION-DESIGN.md`,
`STORAGE-REFLECTIVITY-RBG-DFA-AUDIT.md`,
`AUDIT-distributed-semantics.md`, `AUDIT-privacy.md`,
`AUDIT-nullifiers.md`, `CELL-CRATE-REVIEW.md`,
`AUDIT-sovereign-witness-teeth.md`, `WITNESSED-RECEIPT-CHAIN-DESIGN.md`,
`STAGE-7-GAMMA-2-PI-DESIGN.md`.

The designer's question: dregg grew a **lot** of predicate-shaped things,
in many subsystems, with overlapping but not identical shapes. Slot
caveats (21 variants); per-action `Preconditions`; capability caveats
inherited from biscuit/macaroon ancestry; faceted-cap constraints; DFA
acceptance as a routing predicate; temporal predicates over receipt
chains; STARK-attested membership proofs; bilateral conservation;
cross-federation bridge nullifier predicates; intent matching; etc.

Some of these subsume each other. Some don't. The witness-attached ones
(those that ship a STARK proof along with a commitment and an input)
**all look like the same algebraic object** wearing different field
names. This document inventories every kind, classifies them, and
proposes a single `WitnessedPredicate` shape that subsumes the
witness-attached subset without losing the structural distinctions of
the others.

The strong claim under this study: **`WitnessedPredicate` is the missing
abstraction that makes STORAGE-AS-CELL-PROGRAMS a *migration* rather
than a *port***. Every storage primitive (CapInbox, ProgrammableQueue,
PubSubTopic, BlindedQueue, RelayOperator) is some composition of
predicates that already exist in the inventory. The unification lets a
new primitive plug in without per-kind plumbing.

---

## §0. TL;DR

There are **about 30 distinct predicate kinds** scattered across the
tree, plus a handful of half-finished or stubbed ones. They cluster
into:

- 4 **static post-state predicates** (FieldEquals/Gte/Lte/SumEquals).
- 17 **transition / contextual / temporal slot caveats** (the eval
  vocabulary in `cell::program::StateConstraint`, post-Lane-G).
- 3 **per-action preconditions** (slot equals, slot zero, nonce at
  least) — duplicate surface, see §1.
- 4 **capability authority predicates** (allowed_effects, facet
  constraints, swiss-table membership, AuthRequired ordering).
- 4 **temporal/biscuit caveats** (macaroon TimeBefore/After/Action/
  Resource, with first-party / third-party / bind-to-parent split).
- 3 **routing / DFA-style** (DFA acceptance, longest-prefix path
  match, MatchSpec structural patterns).
- 2 **conservation** (intra-cell `SumEquals` + cross-cell `BoundDelta`,
  plus Pedersen-Schnorr-Bulletproof `ConservationProof`).
- 4 **cross-fed / replay** (bridge `destination_federation`,
  nullifier non-membership, `AttestedRoot` threshold sig,
  `BridgedNullifierSet` insertion).
- ~7 **witness-attached** (DFA matched, temporal predicate, blinded
  Merkle, blinded-set membership, peer_exchange transition_proof,
  `BridgePredicateProof`, `WitnessedReceipt` scope-2 replay, plus the
  empty-slot `StarkMembership` removed from capability_proof).

The first six clusters compose; the **witness-attached** cluster
unifies under a single shape:

```rust
struct WitnessedPredicate {
    kind: WitnessedPredicateKind,      // DFA, Temporal, BlindedMembership, …
    commitment: [u8; 32],              // route-table root / DSL hash / set root / …
    input_ref: InputRef,               // from slot / from action witness / from PI
    proof_witness_index: u8,           // where the proof sits in the action's witness vec
}
```

Each kind registers a verifier; the registry is the only thing that
grows when new kinds land. `StateConstraint::DfaMatched`,
`StateConstraint::TemporalPredicate`,
`Precondition::WitnessedPredicate`, and
`CapabilityCaveat::WitnessedPredicate` all collapse to
`... { witnessed: WitnessedPredicate }`.

The **non-witnessed** kinds (per-action preconditions, slot caveats
that don't carry a proof, capability authority predicates, conservation
in cleartext, federation-aggregate-sig predicates) **do not collapse**
into this. They stay as their own enums. The unification is a chisel,
not a paintbrush. §3.6 names the kinds that resist unification and why.

---

## §1. The full predicate inventory

Every predicate-shaped thing in dregg, with site, role, witness/STARK,
replay semantics, and BOUNDARIES.md vocabulary.

Legend:
- **Author / Verifier**: who declares the predicate vs. who evaluates.
- **STARK?**: `Y` if there's a real AIR enforcing it; `(Y)` if there's
  an AIR but it isn't wired into the executor's enforcement loop;
  `N` if executor-side only.
- **W?** (witness-attached): `Y` if the action / receipt carries a
  proof bytes blob bound to a commitment.
- **Replay**: how the predicate behaves under
  `WitnessedReceipt`-scope-2 re-derivation.
- **Boundary**: per `BOUNDARIES.md` §5 vocabulary
  (cleartext-inside / commitment-inside / acceptance-inside /
  out-of-band).

### §1.1. `StateConstraint` (slot caveats — 21 variants)

Site: `cell/src/program.rs:223-397`. The lifted-enum from
`SLOT-CAVEATS-DESIGN.md` (Lane G) and `SLOT-CAVEATS-EVALUATION.md`.

| Variant | Predicates over | STARK | W? | Replay | Boundary |
|---|---|:-:|:-:|---|---|
| `FieldEquals { i, v }` | `new[i] == v` | N | N | snapshot | cleartext-inside fed; commitment-inside externals via `public_field_view` |
| `FieldGte { i, v }` | `new[i] >= v` | N | N | snapshot | same |
| `FieldLte { i, v }` | `new[i] <= v` | N | N | snapshot | same |
| `SumEquals { idx, v }` | sum of slots == v | N | N | snapshot | same |
| `WriteOnce { i }` | once-set then frozen | N | N | snapshot | same |
| `Immutable { i }` | `new[i] == old[i]` | N | N | snapshot | same |
| `Monotonic { i }` | `new[i] >= old[i]` | N | N | snapshot | same |
| `StrictMonotonic { i }` | `new[i] > old[i]` | N | N | snapshot | same |
| `BoundedBy { i, w }` | new[i] may change only if `old[w]!=0` | N | N | snapshot | same |
| `FieldDelta { i, δ }` | `new[i] == old[i] + δ` | N | N | snapshot | same |
| `FieldDeltaInRange { i, lo, hi }` | `new[i] - old[i] ∈ [lo,hi]` | N | N | snapshot | same |
| `FieldGteHeight { i, off }` | `new[i] >= height + off` | N | N | snapshot height | same |
| `FieldLteHeight { i, off }` | `new[i] <= height + off` | N | N | snapshot height | same |
| `SumEqualsAcross { in, out }` | intra-cell flow conservation | N | N | snapshot | same |
| `SenderAuthorized { set }` | sender ∈ allow-list (Merkle or Blinded) | (Y) future | (Y) future | snapshot set root | depends on `AuthorizedSet` variant (Public ⇒ cleartext; Blinded ⇒ commitment-inside fed) |
| `CapabilityUniqueness { slot }` | cap-set root encodes ≤1 live cap | N | N | snapshot | cleartext-inside fed |
| `RateLimit { max, dur }` | per-sender mutation rate | N | N | snapshot count | cleartext-inside fed |
| `RateLimitBySum { i, max_sum, dur }` | windowed sum cap | N | N | snapshot sum | cleartext-inside fed |
| `TemporalGate { nb, na }` | `height ∈ [nb,na]` | N | N | snapshot | cleartext-inside fed |
| `PreimageGate { i, kind }` | `H(preimage) == slot[i]` | N | N | snapshot | preimage is cleartext-inside the sender, commitment-inside everyone else |
| `MonotonicSequence { i }` | `new[i] == old[i] + 1` | N | N | snapshot | cleartext-inside fed |
| `AllowedTransitions { i, list }` | `(old[i], new[i])` ∈ list | N | N | snapshot | cleartext-inside fed |
| `TemporalPredicate { i, dsl_hash }` | attached `TemporalPredicateProof` | Y | **Y** | snapshot dsl_hash | acceptance-inside verifier |
| `BoundDelta { ls, peer, ps, rel }` | bilateral conservation γ.2 | (Y) future | future | snapshot | depends on γ.2 wiring; commitment-inside each cell's fed |
| `AnyOf { variants }` | single-level disjunction | N | N | snapshot | per-variant |
| `Custom { ir_hash, descriptor, reads }` | DSL-authored | N | N | snapshot ir_hash | cleartext-inside DSL author |

**That's 27 named rows, 21 of which are the canonical "21 variants" in
the eval doc** (the table here separates `RateLimit` / `RateLimitBySum`,
`AnyOf` / `Custom`, and lists `TemporalPredicate` as one row, which gives
the same 21 count).

### §1.2. `Preconditions` (per-action; cell/turn duplicate surface)

Site 1: `cell/src/preconditions.rs:1-336` — `Preconditions`,
`CellStatePrecondition`, `NetworkPrecondition`, `TimeRange`.

Site 2: `turn/src/preconditions.rs:1-162` — *ergonomic builder*
`Precondition::{SlotEquals, SlotZero, NonceAtLeast}` that lowers to the
cell-side struct.

| Variant | Predicates over | STARK | W? | Replay | Boundary |
|---|---|:-:|:-:|---|---|
| `cell_state.nonce == n` | exact nonce | N | N | snapshot | cleartext-inside fed |
| `cell_state.min_nonce >= n` | monotonic floor | N | N | snapshot | same |
| `cell_state.min_balance >= b` | balance floor | N | N | snapshot | same |
| `field_equals: [(i, v)…]` | slot value match | N | N | snapshot | same |
| `proved_state == bool` | sovereign-mode flag | N | N | snapshot | same |
| `network.min_height / max_height` | height window | N | N | snapshot | cleartext-inside fed |
| `valid_while: TimeRange` | timestamp window | N | N | snapshot | same |

The **two sites are not orthogonal**: `turn::preconditions::Precondition`
is a *lowering target* for `cell::Preconditions::cell_state`. The
duplicate is a tax (§4.1 candidate to collapse).

### §1.3. Capability authority (cell/src/capability.rs, cell/src/facet.rs)

| Predicate | Site | Over | STARK | W? | Replay | Boundary |
|---|---|---|:-:|:-:|---|---|
| `allowed_effects: EffectMask` | `capability.rs:36` | bitmask AND with action's effect bit | N | N | snapshot | cleartext-inside cap-holder |
| `AuthRequired::is_narrower_or_equal` | `permissions.rs` | lattice attenuation | N | N | snapshot | cleartext-inside CDT-walker |
| `FacetConstraint::MaxTransferAmount(max)` | `facet.rs:264` | `amount <= max` | N | N | snapshot | cleartext-inside fed |
| `FacetConstraint::AllowedTargets(set)` | `facet.rs:268` | `target ∈ set` | N | N | snapshot | cleartext-inside fed |
| `FacetConstraint::RateLimit { max, cur }` | `facet.rs:272` | `cur < max` | N | N | snapshot | cleartext-inside fed |
| `FacetConstraint::Budget { remaining }` | `facet.rs:282` | `amount <= remaining` | N | N | snapshot | cleartext-inside fed |
| `is_facet_attenuation(parent, child)` | `facet.rs` | bitmask subset | N | N | snapshot | cleartext-inside CDT-walker |
| `is_at_least_as_tight(parent_c, child_c)` | `facet.rs:336` | per-variant tighten check | N | N | snapshot | same |
| Swiss-table enliven | `captp/sturdy.rs:159` | possession of 32-byte swiss | N | N | n/a | cleartext-inside swiss holder |
| Handoff cert verification | `captp/handoff.rs:366` | Ed25519 introducer + recipient sigs | N | N | snapshot | cleartext-inside named recipient |

`ExtendedFacet::constraints` is **defined but never consumed** by
production paths (per `CELL-CRATE-REVIEW.md`). Lives but doesn't bite.

### §1.4. Biscuit / macaroon caveats

Site: `macaroon/src/caveat.rs`, `macaroon/src/action.rs`,
`macaroon/src/resource.rs`, `macaroon/src/caveat_3p.rs`.

Macaroons are dregg's biscuit-lineage component: tokens whose chained
caveats predicate over an `Access` struct.

| Predicate | Site | Over | STARK | W? | Replay | Boundary |
|---|---|---|:-:|:-:|---|---|
| `Caveat::prohibits(access)` trait | `caveat.rs:50` | trait-object polymorphic | N | N | snapshot | cleartext-inside discharge verifier |
| `Action(u8)` access | `action.rs:16` | bitmask action vs required | N | N | snapshot | same |
| `ResourceSet<I, M>::prohibits` | `resource.rs:98` | per-id action mask | N | N | snapshot | same |
| `ThirdPartyCaveat` | `caveat_3p.rs:35` | discharge token from external authority | N | N | snapshot (discharge fetched out-of-band) | cleartext-inside discharge issuer |
| `BindToParentToken` | `caveat.rs:45` | HMAC chain back to parent | N | N | snapshot | cleartext-inside chain |
| `WireCaveat { type, body }` | `caveat.rs:73` | opaque MsgPack body keyed by type ID | N | N | snapshot | per-type |
| `CaveatType` ID-range registry | `caveat.rs:27-45` | platform / user-reg / user-defined / 3p / bind-to-parent | N | N | n/a | n/a |

**This is the closest thing in the tree to a registry-based polymorphic
predicate system today.** The macaroon caveat trait is *the* pattern the
unification design proposes for `WitnessedPredicate` kinds.

### §1.5. DFA / routing / matching predicates

| Predicate | Site | Over | STARK | W? | Replay | Boundary |
|---|---|---|:-:|:-:|---|---|
| `wire::dfa_router::Router::classify` | `wire/dfa_router.rs:98` | bytestring vs DFA table | (Y) `circuit::dsl::circuit:1711-1941` | (Y) AIR exists, not wired | snapshot route root | route-table-author cleartext; verifier acceptance-inside |
| `apps/governed-namespace::routes::RoutingTable::classify` | `apps/governed-namespace/src/routes.rs:1-287` | longest-prefix match | N | N | snapshot | same |
| `rbg::routing::Pattern → Nfa → Dfa` | `rbg/src/routing.rs:1-1346` (workspace-excluded) | full regex incl. intersection | Y (real AIR + trace gen) | Y | snapshot | same |
| `rbg::routing::TopicFilter` | `rbg/src/routing.rs` | gossip topic patterns | (Y) via DFA AIR | (Y) | snapshot | same |
| `intent::matcher::MatchSpec` | `intent/src/lib.rs:347-373`, `intent/src/matcher.rs` | structural Datalog over `(action, resource, app_id, …)` + `compound` AND | N | N | snapshot | cclerk-local cleartext-inside |
| `intent::Constraint::Custom { pred, val }` | `intent/src/lib.rs:339` | named string predicate | N | N | snapshot | matcher cleartext-inside |
| `intent::PredicateRequirement` | `intent/src/lib.rs:179` | "fulfiller must prove `attribute ≷ threshold`" | Y (via `BridgePredicateProof`) | **Y** | snapshot dsl_hash | acceptance-inside verifier |

The DFA "acceptance" — *did this bytestring drive the DFA into an accept
state* — is a **predicate** in the same sense as a slot caveat:
declared statically (via a route table commitment), checked dynamically
(via a `RouteTarget::*` accept-map lookup), and (since `circuit::dsl::
circuit:1711-1941`) STARK-verifiable. It just happens to have a different
input domain (a bytestring) than slot caveats (`(old_state, new_state,
ctx)`).

### §1.6. Witness-attached / proof-bearing predicates (the unification target)

| Predicate | Site | Commitment | Input | Proof | STARK | Replay |
|---|---|---|---|---|:-:|---|
| `StateConstraint::TemporalPredicate { i, dsl_hash }` | `cell/program.rs:360` | `dsl_hash` | action witness slot `i` | `TemporalPredicateProof` | Y | snapshot dsl_hash |
| `circuit::temporal_predicate_dsl::TemporalPredicateProof` | `circuit/src/temporal_predicate_dsl.rs:348` | threshold + num_steps + (initial,final) state root | hidden `values[]` | STARK over GTE/LTE/GT/LT/NEQ/InRange | Y | snapshot witness shape |
| `StateConstraint::SenderAuthorized { BlindedSet { commitment } }` | `cell/program.rs:97-98` | Poseidon2 set commitment | sender pk | non-revocation proof (planned) | (Y) | snapshot commitment |
| `StateConstraint::BoundDelta { peer, …, rel }` | `cell/program.rs:370` | `peer_cell` id | peer slot delta | γ.2 cross-cell aggregator (planned) | (Y) future | snapshot |
| `cell::peer_exchange::PeerStateTransition::transition_proof` | `cell/peer_exchange.rs:62` | (cell_id, old_commit, new_commit, effects_hash) | trace columns | `EffectVmAir` STARK | Y | n/a (chain-local) |
| `cell::note_bridge::PortableNoteProof` | `cell/note_bridge.rs:87` | nullifier, attested source root, destination_federation, value, asset_type | spending witness | `NoteSpendingAir` STARK | Y | snapshot attested root |
| `cell::note_bridge::BridgedNullifierSet` membership predicate | `cell/note_bridge.rs:243` | set root | nullifier | "is in set?" | N today (executor-side) | snapshot |
| `bridge::present::BridgePresentationProof` | `bridge/src/present.rs:149` | federation issuer Merkle root | hidden credential + facts | `BlindedMerklePoseidon2StarkAir` + `PresentationAir` | Y | snapshot federation root |
| `bridge::present::BridgePredicateProof` | `bridge/src/present.rs:3033` | `fact_commitment = Poseidon2(fact_hash, state_root)` | hidden `private_value: u32` | `PredicateProof` (GTE/LTE/GT/LT/NEQ/InRange) | Y | snapshot fact_commitment |
| `cell::value_commitment::ConservationProof` | `cell/value_commitment.rs:347` | inputs/outputs Pedersen sum | excess blinding | Schnorr | N (Schnorr; not STARK) | snapshot |
| `cell::value_commitment::BulletproofRangeProof` | `cell/value_commitment.rs:605` | Pedersen commitment | private value | Bulletproof | N (Bulletproof) | snapshot |
| `cell::value_commitment::FullConservationProof` | `cell/value_commitment.rs:694` | conservation + range | … | combined | N | snapshot |
| `cell::capability_proof::CapabilityProof` (SignedAttestation) | `cell/capability_proof.rs:49` | holder_commitment + cap_slot | sig over (target, perms, slot, expiry, ts) | Ed25519 | N | snapshot holder_commitment |
| `cell::capability_proof::StarkMembership` | (REMOVED — `capability_proof.rs:79-83`) | Merkle root | cap slot | (was) STARK | — | — |
| `turn::WitnessedReceipt` scope-2 | `turn/src/witnessed_receipt.rs` | `witness_hash` | trace rows (`Vec<Vec<u32>>`) | `EffectVmAir` STARK | Y | replay-derived |
| `chain::credential::EvmCredentialProof` (locally verified) | `chain/src/credential.rs:191` | EVM bridge state root | hidden cred | external proof | (Y external) | snapshot bridge root |
| `intent::trustless::SealedTurn` (winning solution) | `intent/src/trustless.rs:250` | batch_root + intent_set | hidden bids | solver STARK (planned/partial) | (Y) future | snapshot batch_root |

That's **15 named witness-attached predicates** with structurally
identical shapes. They are what `WitnessedPredicate` (§3) unifies.

### §1.7. Federation / consensus aggregate-signature predicates

| Predicate | Site | Over | STARK | W? | Replay | Boundary |
|---|---|---|:-:|:-:|---|---|
| `AttestedRoot` threshold sig | `types/src/lib.rs:281-309` | committee verifier key, BLS aggregate | N (cryptographic, but not STARK) | aggregate sig | n/a | acceptance-inside any verifier with committee vk |
| `FederationReceipt::verify` | `federation/src/receipt.rs:122` | committee + body hash | N | sig | n/a | same |
| `ThresholdQC` (constant-size BLS) | `federation/src/threshold.rs:37` | committee threshold + KZG attest | N (BLS pairing) | aggregate | n/a | same |
| `BridgedNullifierSet::contains` non-membership predicate | `cell/note_bridge.rs:243` | set | nullifier | "is not in set" | N | snapshot | acceptance-inside fed |

These are not "witness-attached" in the `WitnessedPredicate` sense:
they are signature predicates, not proof-carrying-knowledge predicates.
The shape `verify(commitment, message) -> bool` is similar but the
algebra is multi-party-signature, not STARK soundness. §3.6 keeps these
separate.

### §1.8. Storage primitive predicates

Site: `storage/src/programmable.rs` (`QueueConstraint` — the
pre-lift vocabulary), now aliased to
`cell::program::StateConstraint` (post-Lane-G Phase 1).

| Variant (legacy `QueueConstraint`) | Already-lifted to `StateConstraint`? |
|---|---|
| `SenderAuthorized { set_root }` | yes (`StateConstraint::SenderAuthorized`) |
| `ContentPattern { pattern }` | partially — DSL or DFA classification; see §8 |
| `MinDeposit { amount }` | yes — `StateConstraint::FieldGte` against a deposit slot |
| `MaxSize { max }` | yes — `StateConstraint::FieldLte` against a length slot |
| `RateLimit { max, dur }` | yes (`StateConstraint::RateLimit`) |
| `MonotonicSequence` | yes (`StateConstraint::MonotonicSequence`) |
| `TemporalGate { nb, na }` | yes (`StateConstraint::TemporalGate`) |
| `PreimageGate { commitment }` | yes (`StateConstraint::PreimageGate`) |
| `Custom { expr }` | yes (`StateConstraint::Custom`) |

The Phase-1 alias is in `storage/src/programmable.rs:36`:
```rust
SimpleStateConstraint as LiftedSimpleConstraint,
StateConstraint as LiftedQueueConstraint,
```

**Net:** queue constraints are no longer their own predicate kind —
they are a *specific composition* of `StateConstraint`s declared on
a queue cell. (`ContentPattern` is the lone open seam: it wants a DFA
or DSL classifier, both already in the inventory.)

### §1.9. DSL backend predicate shapes

Site: `dregg-dsl/src/{gen_air,gen_kimchi,gen_plonky3}.rs`.

The `#[dregg_caveat]` attribute compiles a Rust function body of
`require!(…)` calls into an IR (`ConstraintIr`) and then per-backend
artifacts:

| `RequirementKind` | Site | What it predicates | Backend |
|---|---|---|---|
| `LessEqual / GreaterEqual / Equal / NotEqual` | `dregg-dsl/ir.rs:144` | scalar compare | AIR, Kimchi, Plonky3 |
| `Membership { set, element }` | ir.rs:154 | in-memory set membership | AIR |
| `BitRange { value, bits }` | ir.rs:156 | `v < 2^N` via bit-decomp | AIR |
| `MerkleAtPosition { root, leaf, pos, sibs, depth }` | ir.rs:163 | Poseidon2 Merkle inclusion | AIR + Kimchi |
| `Poseidon2Hash { inputs, output }` | ir.rs:174 | `output == Poseidon2(inputs)` | AIR + Kimchi |

These are the **atomic predicate primitives** that DSL-authored
caveats lower to. They are not used at the executor level directly;
they're emitted into per-circuit AIRs. Their bit-equivalent at
verifier-side is "this caveat function's `ir_hash` produced these
constraint rows; the trace satisfies them."

### §1.10. Miscellaneous / one-off predicates

- **Stealth address ownership** (`cell/src/stealth.rs:178`
  `check_ownership`): "view_private_key + spend_pubkey jointly own
  this address." Cleartext-inside the view-key holder.
- **Oblivious-transfer correctness** (`cell/src/oblivious_transfer.rs`):
  "the OT receiver got exactly one of two values, sender doesn't know
  which." Protocol predicate, not an enum variant. Cleartext-inside
  the OT-receiver; acceptance-inside the OT-sender.
- **Nullifier non-membership** (general, not just bridge):
  `cell/src/nullifier_set.rs`. "this nullifier has not been spent
  before." Acceptance-inside the spend verifier.
- **`Authorization::Signature` vs `::Proof` vs `::Unchecked` vs
  `::CapTpDelivered`** (`turn/src/action.rs`): each variant is itself
  a predicate kind ("the actor proved authority via mechanism X").
  See `BOUNDARIES.md §3.7`. The `Unchecked` carve-out is a hole the
  soundness sweep is patching.
- **Conditional turn predicates** (`turn/src/conditional.rs`): "this
  turn fires only if the named predicate evaluates true." Composes
  slot caveats, height checks, peer-cell views.
- **`turn::escrow::EscrowCondition`** (`turn/src/escrow.rs`): release
  conditions on escrowed values (timeout, multisig, oracle attest).
- **`turn::obligation::Obligation`** (`turn/src/obligation.rs`):
  deferred-discharge predicates (must execute X by deadline).
- **`turn::presence_discharge::PresenceCaveat`** (`turn/src/
  presence_discharge.rs:27`): "this party was present in the
  blocklace at round R."

These are predicate-shaped but most are app-level building blocks
that compose primitives from §1.1-§1.6. They don't add new algebraic
shapes; they re-use them.

---

## §2. Taxonomy — grouping by axis

The same predicate sits at different points along multiple axes.

### §2.1. Author / verifier locality

- **Local (one cell, one node — fed-mediated).** Slot caveats
  (§1.1). The cell's federation node evaluates against its own copy
  of the cell state. `FieldEquals`, `WriteOnce`, `Monotonic`, etc.
  Per-action `Preconditions` (§1.2) live here too.
- **Bilateral (two cells — peer-mediated).** `BoundDelta` (cross-cell
  γ.2 conservation), `peer_exchange::PeerStateTransition`. The
  predicate's witness comes from one party; the other verifies
  against its locally-held peer view.
- **Federation (committee — quorum).** `AttestedRoot::has_quorum`,
  `FederationReceipt::verify`, `ThresholdQC` aggregate. The
  predicate is "this body was attested by enough committee members."
- **Cross-fed (multiple committees).** Bridge `PortableNoteProof`'s
  `destination_federation` predicate; `BridgedNullifierSet`
  insertion at the destination side; `AttestedRoot.blocklace_block_id`
  binding (Lane D fix). The predicate spans *two* committees and
  requires both verifiers to be on the same algebraic page.
- **Subscription / gossip (one-to-many).** Temporal predicates over
  receipt-chain roots (§1.6); intent gossip topic-filter classification
  (§1.5 — DFA-mediated); `intent::PredicateRequirement` proven
  against the matched counterparty's state root.
- **CapTP / object-cap exercise.** Capability authority predicates
  (§1.3); `CapabilityProof` (signed-attestation peer-cap exercise).
  Author = cap holder; verifier = target cell's host.

### §2.2. Witness attachment

- **Static** — declared once, verifier checks against current state.
  `FieldEquals`, `WriteOnce`, `Immutable`, `Monotonic`, …
  `allowed_effects`, `FacetConstraint::*`.
- **Witnessed** — verifier checks witness data against a commitment.
  `PreimageGate` (witness = preimage), `MonotonicSequence` (witness =
  next seq number), `BoundDelta` (witness = peer state).
- **Proof-attested** — STARK / Bulletproof / Schnorr proof attached.
  `TemporalPredicate`, `BlindedMerkle`-backed
  `BridgePresentationProof`, `BridgePredicateProof`,
  `PortableNoteProof`, `PeerStateTransition.transition_proof`,
  `ConservationProof`, `BulletproofRangeProof`.

### §2.3. Time scope

- **Per-action** — `Preconditions` (`cell::Preconditions`).
  Evaluated *before* effects run, against the pre-state.
- **Per-slot transition** — `StateConstraint` (slot caveats).
  Evaluated *after* state-modifying effects, against the post-state
  (and old-state for transition variants).
- **Per-receipt-chain N-step** — `TemporalPredicateAir` (the
  37-column DSL AIR). Evaluated over the sequence of values across
  the last N receipts in a chain.
- **Cross-time / snapshot-time** — `SLOT-CAVEATS-EVALUATION.md`
  finding 3: replay-sensitive constraints
  (`FieldGteHeight / FieldLteHeight / SenderAuthorized` with a
  slot-held root) **snapshot their external state at receipt-time**
  so scope-2 replay is deterministic. The replayer reads the
  snapshot from the receipt, not from its own live chain.

### §2.4. Privacy boundary (per BOUNDARIES.md vocabulary)

- **Cleartext-inside.** The federation node sees every slot caveat's
  inputs (`FieldEquals`, `Monotonic`, …); see `BOUNDARIES.md §2.5`.
  The cclerk sees its own preconditions and held caps.
- **Commitment-inside.** External readers of `public_field_view`
  (committed fields). `BlindedSet` membership: the cell knows only a
  Poseidon2 commitment to the allow-list. Sealed cap recipient sees
  the cap; observers see only the `pair_id` and ciphertext.
- **Acceptance-inside.** STARK verifiers (`TemporalPredicateProof`,
  `BridgePresentationProof`, `BridgePredicateProof`, …). The
  verifier learns only `accept` or `reject` modulo the public inputs.
- **Out-of-band.** Anyone who doesn't hold the swiss / unsealer /
  cert / proof / commitment. Default audience for everything that
  isn't explicitly named.

Per-predicate boundary contracts are listed in §1's tables and again
in §5 below.

---

## §3. The `WitnessedPredicate` unification

### §3.1. The shared shape

Walk the witness-attached rows in §1.6 with fresh eyes. Every one of
them has:

1. A **commitment** — a 32-byte hash binding the predicate's
   "shape" (DFA route table root, temporal predicate DSL hash,
   Merkle root, set root, fact commitment, AttestedRoot, peer cell
   id…).
2. An **input** — possibly from the cell's slot, possibly from the
   action's witness slot, possibly a public input to the proof
   (PI).
3. A **proof** — STARK bytes (sometimes Bulletproof, sometimes
   Schnorr — but the shape is "verifier-callable bytes blob").
4. A **verifier** — a function `(commitment, input, proof) → {accept,
   reject}`.

This is precisely the shape `dregg` already has for the macaroon
caveat trait (§1.4) — except that macaroon caveats are
*polymorphic-over-Access* and these are
*polymorphic-over-(commitment,input,proof)*.

### §3.2. The proposed type

```rust
/// A predicate enforced by attaching a witness/proof bound to a
/// commitment.
///
/// Independent of the *kind* of predicate (DFA acceptance, temporal
/// over receipts, blinded set membership, …): the executor verifies
/// by dispatching to the kind's registered verifier, passing the
/// commitment, the resolved input, and the proof bytes.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WitnessedPredicate {
    /// Which predicate algebra applies (DFA, Temporal, BlindedMembership,
    /// MerkleMembership, PedersenEquality, Custom { vk_hash }, …).
    pub kind: WitnessedPredicateKind,

    /// The commitment binding the predicate's shape and audience.
    /// Each kind's verifier interprets this — for DFA it's the route
    /// table root; for Temporal it's the DSL hash; for BlindedMembership
    /// it's the Poseidon2 set root; for MerkleMembership it's the leaf
    /// Merkle root.
    pub commitment: [u8; 32],

    /// Where the input comes from.
    pub input_ref: InputRef,

    /// Index into the action's `witness_blobs` vec naming which proof
    /// bytes feed the verifier. (Lets one action carry multiple
    /// witnessed predicates, each pointing at its own proof.)
    pub proof_witness_index: u8,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum InputRef {
    /// Read from the cell's state slot at this index.
    Slot { index: u8 },
    /// Read from the action's witness blob at this index (separate
    /// from the proof blob; the witness can be cleartext while the
    /// proof is the ZK shell).
    Witness { index: u8 },
    /// Public input — the verifier reads from the proof's own PI vec.
    PublicInput { pi_index: u8 },
    /// The sender's identity. (For sender-bound witnessed predicates
    /// like `BlindedSenderAuthorized`.)
    Sender,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum WitnessedPredicateKind {
    /// DFA-bytestring acceptance per `wire::dfa_router` / RBG compiler.
    Dfa,
    /// Temporal predicate over N receipts per
    /// `circuit::temporal_predicate_dsl`.
    Temporal,
    /// Poseidon2 Merkle membership against the cell's set root.
    /// (Subsumes the old `StarkMembership` placeholder once a real
    /// gadget lands.)
    MerkleMembership,
    /// Poseidon2 commitment to a set; non-revocation / non-membership
    /// proof against the blinded commitment.
    BlindedMembership,
    /// `BridgePredicateProof` — Gte/Lte/Gt/Lt/Neq/InRange over a
    /// committed fact attribute.
    BridgePredicate,
    /// Pedersen equality / range — `ConservationProof` /
    /// `BulletproofRangeProof` for the cleartext-inside-Pedersen path.
    PedersenEquality,
    /// Custom — verifier key hash names a registered AIR / verifier.
    /// Sibling to `Effect::Custom`'s `vk_hash` pattern (per
    /// `DESIGN-max-custom-effects.md`).
    Custom { vk_hash: [u8; 32] },
}
```

### §3.3. The registry

The verifier for each kind is a registered function pointer (or trait
object):

```rust
pub trait WitnessedPredicateVerifier: Send + Sync {
    fn verify(
        &self,
        commitment: &[u8; 32],
        input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError>;

    fn kind(&self) -> WitnessedPredicateKind;
    fn name(&self) -> &'static str;
}

pub struct WitnessedPredicateRegistry {
    // closed enum kinds → static verifier impls
    builtins: BTreeMap<WitnessedPredicateKind, &'static dyn WitnessedPredicateVerifier>,
    // Custom { vk_hash } → app-registered verifier
    custom: BTreeMap<[u8; 32], Arc<dyn WitnessedPredicateVerifier>>,
}
```

This **mirrors the macaroon `CaveatType` registry exactly** (§1.4):
fixed range for platform-reserved kinds, open range for
user-registered, an explicit `Custom { vk_hash }` escape that
mirrors `Effect::Custom`.

### §3.4. How current types collapse

After the unification:

- `StateConstraint::TemporalPredicate { witness_index, dsl_hash }`
  → `StateConstraint::Witnessed(WitnessedPredicate {
       kind: Temporal,
       commitment: dsl_hash,
       input_ref: InputRef::Witness { index: witness_index },
       proof_witness_index: …,
  })`
- `StateConstraint::SenderAuthorized { BlindedSet { commitment } }`
  → `StateConstraint::Witnessed(WitnessedPredicate {
       kind: BlindedMembership,
       commitment,
       input_ref: InputRef::Sender,
       proof_witness_index: …,
  })`
- `StateConstraint::BoundDelta { … }` — *partially.* The
  γ.2-aggregated bilateral conservation needs both peers' commitments;
  it's structurally a *pair* of `WitnessedPredicate`s plus a
  match-loop. (§3.6 case.)
- `RouteTarget::*` accept-map lookup in
  `wire::dfa_router::Router::classify` becomes
  `WitnessedPredicate { kind: Dfa, commitment: table_root, … }`
  invocable from any predicate-bearing surface (slot caveat,
  precondition, capability caveat).
- `BridgePredicateProof` already has the shape; it becomes a
  `WitnessedPredicate { kind: BridgePredicate, commitment:
  fact_commitment, … }`.
- `PortableNoteProof.spending_proof` becomes a `WitnessedPredicate
  { kind: Custom { vk_hash: note_spending_air_vk }, commitment:
  attested_root_hash, … }`. The bridge keeps its `BridgePhase` /
  `BridgeEnvelope` machinery; the **inner proof predicate**
  unifies.
- `PeerStateTransition.transition_proof` becomes a
  `WitnessedPredicate { kind: Custom { vk_hash: effect_vm_air_vk
  }, commitment: BLAKE3(cell_id, old, new, effects_hash), … }`.
- `CapabilityProof::SignedAttestation` is **not** a
  `WitnessedPredicate` in this scheme — it's an *Ed25519 signature
  predicate*, more like `AttestedRoot` than like a STARK. §3.6.

### §3.5. The composition surface

Three places gain a `WitnessedPredicate` slot:

```rust
// 1. Slot caveats — replace TemporalPredicate variant with a generic
//    witnessed wrapper.
pub enum StateConstraint {
    // … all current variants …
    Witnessed(WitnessedPredicate),
}

// 2. Per-action preconditions — add a witnessed clause to the existing
//    cell-state / network / time wrappers.
pub struct Preconditions {
    pub cell_state: Option<CellStatePrecondition>,
    pub network: Option<NetworkPrecondition>,
    pub valid_while: Option<TimeRange>,
    /// New: witness-attached preconditions (DFA-classified message,
    /// temporal predicate over chain, blinded membership proof, …).
    pub witnessed: Vec<WitnessedPredicate>,
}

// 3. Capability caveats — let cap holders carry a `WitnessedPredicate`
//    constraint ("this cap only matches if you can produce a proof
//    that satisfies WP"). Sibling to FacetConstraint::* but
//    proof-bearing.
pub enum CapabilityCaveat {
    FacetConstraint(FacetConstraint),
    Witnessed(WitnessedPredicate),
}
```

(The exact field names are sketch — the point is the placement.)

### §3.6. What the unification *loses*

Predicate kinds that **do not** fit `WitnessedPredicate` cleanly, and
why:

1. **Per-action `Preconditions` static atoms** (slot equals, slot zero,
   nonce at least, height window, time range). No commitment, no proof.
   They're cleartext-inside-fed pure predicates. Forcing them through
   `WitnessedPredicate` adds 32 bytes of zeroes commitment plus an
   empty proof — wasted bandwidth and audit noise. Keep them as
   `Preconditions` fields.

2. **Static slot caveats** (`FieldEquals`, `FieldGte`, `WriteOnce`,
   `Monotonic`, `Immutable`, `BoundedBy`, `FieldDelta`, …). Same as
   above. No commitment beyond the slot index; no proof beyond the
   slot's value. Keep as `StateConstraint` variants.

3. **Capability authority lattice** (`AuthRequired`,
   `allowed_effects`, `is_narrower_or_equal`, `is_facet_attenuation`).
   These are *order-theoretic* predicates — questions about lattice
   relationships, not about witnesses. The verifier checks bitmask
   subset, not proof bytes. Don't collapse.

4. **Conservation in cleartext** (`SumEquals`, `SumEqualsAcross`)
   stays in `StateConstraint`. The **Pedersen-curtain
   `ConservationProof`** *does* fit `WitnessedPredicate` (kind:
   `PedersenEquality`), but the cleartext intra-cell shapes don't.
   Both exist in parallel; they're the same mathematical statement
   evaluated at different boundaries.

5. **`BoundDelta` cross-cell γ.2.** The bilateral predicate is "this
   cell's delta in slot `local_slot` equals (or is opposite to) the
   peer's delta in `peer_slot`." It's *two* `WitnessedPredicate`s
   that have to match plus an aggregation step. The match loop is
   not the predicate; the *pair* is. §3.5 above doesn't model this
   cleanly. Either:
   - (a) keep `BoundDelta` as a first-class `StateConstraint` variant
     and have the γ.2 aggregator produce its own match-receipt;
   - (b) introduce `WitnessedPredicate::CrossCell { local: WP, peer:
     WP, relation }` — a second-order shape.
   Recommendation: (a). The cross-cell match-loop is too high-level
   to flatten into the per-predicate registry.

6. **Federation aggregate signatures** (`AttestedRoot::has_quorum`,
   `ThresholdQC`, `FederationReceipt::verify`). The algebra is
   multi-party-signature, not STARK. The "proof" is a BLS aggregate;
   the "input" is the message digest; the "commitment" is the
   committee key. Could be modeled as
   `WitnessedPredicate { kind: ThresholdSig, commitment: cmt_key,
   … }`, but the verifier signature is so different
   (pairings, KZG, weights) that lumping it in with FRI-STARK is
   misleading. Keep separate.

7. **Macaroon caveats.** Already have their own polymorphic registry
   (`CaveatType` IDs + trait object). They are *first-party* caveats
   over `Access`, not over `(commitment, input, proof)`.
   `ThirdPartyCaveat` plus discharge is *almost* `WitnessedPredicate`
   (the discharge token is the "proof"), but the abstraction layer is
   wrong: macaroons live in the token-presentation pipeline, not at
   the executor. Keep parallel.

8. **`MatchSpec` (intent matching).** Structural — typed-field
   comparisons, recursive `compound: Option<Vec<MatchSpec>>`. Not
   bytestring-shaped; doesn't fit a `commitment + input + proof`
   trio. Already argued in `DFA-RATIONALIZATION-DESIGN.md §6.1`.
   Keep separate.

9. **CapTP swiss enliven / handoff cert validation.** The "predicate"
   here is *possession*, not knowledge of a witness. Bearer secrets
   vs. proof-of-knowledge are different boundary types
   (`BOUNDARIES.md §2.2 vs §2.3`). Keep separate.

10. **Network / time preconditions** (`NetworkPrecondition::min_height`,
    `valid_while: TimeRange`). Cipherclerk-side cleartext context; no
    commitment story. Already part of `Preconditions`.

**Summary:** `WitnessedPredicate` cleanly subsumes the
**proof-attested** column of §2.2, plus the **commitment-inside**
sub-row of "witnessed" where the witness is a Merkle / blinded proof.
It does **not** absorb static cleartext predicates, lattice predicates,
aggregate-signature predicates, structural matchers, or
bearer-possession predicates. That's ~15 kinds collapsing under one
roof, ~15 staying parallel. The unification is honest.

---

## §4. Composition rules — what plugs in where

### §4.1. Surfaces that gain `WitnessedPredicate`

After the lift:

- **`StateConstraint::Witnessed(WP)`** — slot caveats may include any
  registered witnessed predicate kind (subsumes the current
  `StateConstraint::TemporalPredicate`).
- **`Preconditions::witnessed: Vec<WP>`** — per-action preconditions
  may include witness-attached clauses (DFA-classified message,
  temporal-predicate over chain, blinded-membership against a slot
  root, …).
- **`CapabilityCaveat::Witnessed(WP)`** — capability caveats may
  encode "this cap only fires when the holder presents a proof that
  matches WP" (the natural extension of `FacetConstraint::*` to
  witness-bearing predicates).
- **Intent `PredicateRequirement`s** — already-witness-attached
  (they require a `BridgePredicateProof` from the matched
  counterparty); migrate to carry a `WitnessedPredicate` directly.
- **`RouteTarget::Userspace { kind, payload }`**
  (per `DFA-RATIONALIZATION-DESIGN.md §4`) — userspace destinations
  may encode a `WP` constraint to gate the route.

### §4.2. Composition with γ.2 (cross-cell)

The cross-cell `BoundDelta` predicate (§3.6 case 5) is **bilateral**:
two cells each carry one `StateConstraint::BoundDelta`, and the γ.2
aggregator produces a single match-receipt binding both halves.

The clean shape is:

- Each cell's `StateConstraint::BoundDelta` *declares* the bilateral
  predicate.
- The aggregator (`STAGE-7-GAMMA-2-PI-DESIGN.md`) is the *verifier*
  that produces a γ.2 receipt — itself a `WitnessedPredicate { kind:
  Custom { vk_hash: gamma_2_air_vk }, commitment:
  BLAKE3(local_cell, peer_cell, slots, relation), input: pair of
  receipts, proof: γ.2 STARK }`.

So `BoundDelta` is **declared per-cell** and **proven via a
`WitnessedPredicate`** at the aggregation step. Both shapes coexist.

### §4.3. Duplicate surfaces that should collapse

Two cases where two predicate shapes are reaching for the same role:

1. **`cell::Preconditions` ↔ `turn::preconditions::Precondition`** (§1.2).
   The turn-side enum is a *builder* for the cell-side struct. After
   the `WitnessedPredicate` lift, both gain the same `witnessed: Vec<WP>`
   field. Recommendation: **fold `turn::preconditions::Precondition`
   into a `cell::Preconditions::builder()` method**; the enum becomes
   redundant. Net change: deletion-heavy.

2. **`storage::QueueConstraint` ↔ `cell::StateConstraint`** (§1.8).
   Already aliased Phase-1 (Lane G). The Phase-2 collapse of
   `storage::programmable` into "a cell whose program is
   `CellProgram::Predicate(...)`" is the natural completion
   (`SLOT-CAVEATS-DESIGN.md §5` Option C).

3. **`facet::FacetConstraint::RateLimit` ↔ `StateConstraint::RateLimit`** —
   the latter is per-cell-per-sender, the former is per-cap-holder.
   Different scopes; **keep separate** but the *implementation* could
   share a `RateLimitEnforcer` helper.

### §4.4. The dispatcher composition

Per `DFA-RATIONALIZATION-DESIGN.md §5`, the natural pipeline is:

```
incoming request
    │
    ▼
DFA classify (a WitnessedPredicate { kind: Dfa }) ─► RouteTarget
                                                       │
                                                       ▼
                                    Dispatcher (extracts caveats)
                                                       │
                                                       ├── may attach further WPs
                                                       │   (precondition lift)
                                                       ▼
                                                  TurnExecutor
                                                       │
                                                       ├── Preconditions::evaluate
                                                       │    (including any WPs)
                                                       ├── apply effects
                                                       ├── StateConstraint::evaluate
                                                       │    (including Witnessed variants)
                                                       ▼
                                                   Receipt
```

Each evaluator points at the **same registry** for verifier lookup.
A new `WitnessedPredicateKind` plugs in at the registry; **no code
changes** in the slot-caveat, precondition, or capability-caveat
surfaces.

---

## §5. Composition with the boundary vocabulary

Per-kind boundary contracts (using `BOUNDARIES.md §5.1`'s
cleartext-inside / commitment-inside / acceptance-inside / out-of-band).

### §5.1. DFA acceptance (`WitnessedPredicate { kind: Dfa }`)

- **Cleartext-inside:** route-table-author (knows the
  `(Pattern, RouteTarget)` pairs); input-presenter (knows the
  bytestring).
- **Commitment-inside:** anyone who knows only the route-table-root
  `commitment`. They can verify a classification matches the
  commitment without seeing the patterns.
- **Acceptance-inside:** STARK verifier — learns only that the trace
  drove the DFA to an accept state with the named target.
- **Out-of-band:** everyone else.

Note: the DFA's "zero-knowledge over both pattern and input" lives
in the AIR (`circuit/src/dsl/circuit.rs:1711-1941`); the route table
itself is constitution-bound (`GovernedRouter`) and
commitment-inside.

### §5.2. Temporal predicate (`WitnessedPredicate { kind: Temporal }`)

- **Cleartext-inside:** the holder of the chain values (the cell
  owner, or the receipt-chain author).
- **Commitment-inside:** anyone with the DSL hash + initial/final
  state roots.
- **Acceptance-inside:** STARK verifier — learns
  `predicate_type ∧ threshold ∧ num_steps` from the public inputs;
  learns nothing about the per-step `values[]`.
- **Out-of-band:** anyone without the proof.

### §5.3. `WriteOnce`, `Monotonic`, `FieldEquals`, etc.

- **Cleartext-inside:** the federation node (hosts the cell, sees
  every slot value).
- **Commitment-inside:** external readers of `public_field_view` for
  `Committed` slots.
- **Acceptance-inside:** n/a (no proof).
- **Out-of-band:** network observers without `public_field_view`
  access.

Trivial — the federation already sees the cell state cleartext, so
the slot caveat's predicate inputs are all federation-visible.

### §5.4. `PreimageGate`

- **Cleartext-inside:** the action sender (knows the preimage).
- **Commitment-inside:** anyone with the cell's slot at
  `commitment_index` (sees the hash, not the preimage).
- **Acceptance-inside:** verifier (sees the action; observes the
  preimage during turn-application, then hashes it once).
- **Out-of-band:** anyone without the action body.

Note: this is a *short-lived* cleartext exposure — the preimage is
revealed at turn-application time, then no longer secret. This is
the boundary `BOUNDARIES.md §2.5` calls "the executor sees but
doesn't persist" minus the persistence.

### §5.5. `BlindedSet` membership

- **Cleartext-inside:** the set author (knows the full member list);
  each member individually knows their own membership.
- **Commitment-inside:** the federation (sees only the Poseidon2 set
  root).
- **Acceptance-inside:** the STARK verifier of the non-revocation
  proof.
- **Out-of-band:** everyone else.

This is the **only** slot caveat variant today where the federation
is *commitment-inside* rather than cleartext-inside the predicate's
state. Important property for sovereign-cell governance: the cell's
allow-list can be private to its author.

### §5.6. Bridge `PortableNoteProof`

- **Cleartext-inside:** the note holder (knows value, asset, source,
  destination, spending key).
- **Commitment-inside:** the source federation (sees the `AttestedRoot`
  binding); the destination federation (sees the nullifier).
- **Acceptance-inside:** the destination's STARK verifier
  (`destination_federation`, nullifier, root, value, asset_type
  are PI).
- **Out-of-band:** anyone without the envelope.

`BOUNDARIES.md §2.10`.

### §5.7. `PeerStateTransition.transition_proof`

- **Cleartext-inside:** Alice and Bob (the two peers).
- **Commitment-inside:** Anyone with `(cell_id, old, new,
  effects_hash)` but no proof — they know that *a* transition
  happened, not what effects.
- **Acceptance-inside:** the STARK verifier (if proof present).
- **Out-of-band:** the rest of the federation, who never see the
  transition until one of the two peers publishes a sovereign turn.

`BOUNDARIES.md §2.8`.

### §5.8. Macaroon caveats (first-party)

- **Cleartext-inside:** the token holder + the verifying server.
- **Commitment-inside:** anyone with the HMAC chain (can re-verify
  given the secret).
- **Acceptance-inside:** discharge gateways (for third-party).
- **Out-of-band:** observers.

### §5.9. Federation `AttestedRoot`

- **Cleartext-inside:** committee members (each holds their share).
- **Commitment-inside:** anyone with the committee verifier key.
- **Acceptance-inside:** anyone who checks the aggregate sig.
- **Out-of-band:** anyone without the verifier key.

---

## §6. Open design questions

These are the calls the inventory implies but doesn't decide.

### §6.1. Where does `WitnessedPredicate` live?

Three candidates:

- **`cell::program`.** Most natural for the slot-caveat case. But
  `Preconditions` (cell-side) and capability caveats also need it, so
  it can't be tucked inside `program`.
- **`turn::`.** All the surfaces that *use* WP (preconditions,
  caveats, action witnesses) live in `turn`. But the
  `StateConstraint::Witnessed` variant is in `cell::program`.
- **`dregg-cell::predicate`** (a new module within `dregg-cell`,
  no new crate). Companion to `cell::program::StateConstraint`,
  `cell::preconditions::Preconditions`, and (future)
  `cell::capability::CapabilityCaveat`. All three sites import from
  the same place; the registry is module-local.
- **New `dregg-predicate` crate.** Heaviest option. Forces
  dependency direction `cell, turn, intent → dregg-predicate`, which
  is a clean DAG but adds a workspace member for a single-purpose
  abstraction.

**Recommendation:** `cell/src/predicate.rs` (new module inside
`dregg-cell`). The `WitnessedPredicate` type and the
`WitnessedPredicateRegistry` live there; `StateConstraint::Witnessed`,
`Preconditions::witnessed`, and `CapabilityCaveat::Witnessed` all
reference the same type. No new crate; no new edition mixing.
Sibling to `cell::predicate` is `cell::program` (slot caveats) and
`cell::preconditions` (per-action) — three small modules, one
algebra.

### §6.2. Kind registry shape

- **Closed enum.** Simplest. `WitnessedPredicateKind::{Dfa, Temporal,
  MerkleMembership, BlindedMembership, BridgePredicate, PedersenEquality,
  Custom { vk_hash }}`. New built-in kinds require an enum addition
  (touches all match arms). The `Custom` variant absorbs everything
  else app-side.
- **Trait object polymorphism.** Each kind is a `Box<dyn
  WitnessedPredicateVerifier>`. Maximally flexible but loses the
  serialization-friendliness — `WitnessedPredicate` needs to be
  `Serialize + Deserialize`, and trait objects aren't trivially so.
- **`vk_hash`-keyed registry.** Closer to `Effect::Custom`'s shape per
  `DESIGN-max-custom-effects.md`: every kind is keyed by a 32-byte
  verifier-key hash. App-side and platform-side coexist; the registry
  resolves the hash to a static dispatch. Backward-compatible: built-in
  kinds register their own `vk_hash` at startup.

**Recommendation:** *closed enum for the platform set, with a
`Custom { vk_hash }` escape for app-defined kinds*. This mirrors
the macaroon `CaveatType` design (§1.4) which is the existing
precedent. The closed enum gives audit tools structural visibility;
the `Custom` escape gives apps extensibility.

### §6.3. Replay semantics

For witnessed predicates that depend on external state (the temporal
predicate's state roots; the blinded set's commitment), how does
`WitnessedReceipt`-scope-2 replay re-evaluate?

Per `SLOT-CAVEATS-EVALUATION.md` finding 3 (already adopted for
non-witnessed replay-sensitive variants): **snapshot the commitment
at receipt-time, replay against the snapshot**. For witnessed
predicates this means the receipt must carry both the
`WitnessedPredicate` declaration *and* the proof bytes; on replay,
the verifier reads the commitment from the snapshot, not from the
replayer's current chain.

The proof bytes themselves are already on the receipt. The only
additional carry is the *commitment as resolved at receipt-time* (if
the commitment came from a slot at the time, the slot value is on the
receipt; if it came from a constant in the cell program, the cell
program hash is on the receipt). Both already implicit; the only
explicit change is documenting it.

**Recommendation:** make commitment-snapshotting an invariant of
`WitnessedPredicate`'s replay contract. The receipt-builder
populates the snapshot; the replayer must use it.

### §6.4. Cross-cell composition (`BoundDelta` revisited)

Per §3.6 case 5 and §4.2: the cross-cell predicate is bilateral, not
single-party. The per-cell `StateConstraint::BoundDelta` declares
the bilateral predicate; the γ.2 aggregator's match-receipt is itself
a `WitnessedPredicate { kind: Custom { vk_hash: gamma_2_vk } }`.

This means the *predicate algebra* is one level higher: a
"cross-cell predicate" composes two single-cell `WitnessedPredicate`
declarations into one aggregate proof. The aggregation logic lives in
the γ.2 crate (per `STAGE-7-GAMMA-2-PI-DESIGN.md`), not in the
predicate registry. Open question: should the registry model this
composition explicitly (a `Composite { left: WP, right: WP, op:
Relation }` variant)?

**Recommendation:** **no**. The aggregator's role is structurally
distinct (it operates over *receipts*, not over predicates) and
should stay in γ.2. The composition is a pipeline step, not a
predicate kind.

### §6.5. AIR enforcement — per-variant opt-in

Per `SLOT-CAVEATS-DESIGN.md §4`'s recommendation: ship slot caveats
as executor-side first, AIR-enforce per-variant opt-in second.

The same logic applies to `WitnessedPredicate`. Witnessed kinds that
already have AIRs (Temporal, BridgePredicate, BlindedMembership)
*already* get AIR enforcement on the predicate side. The
`StateConstraint::Witnessed(WP)` lift inherits whatever the kind's
verifier does.

The new opt-in question is: do we add an `effect_vm_air` constraint
that *binds the WP's verification result to the transition*? Today
the slot-caveat AIR doesn't constrain the WP's verifier call at all
(per `SLOT-CAVEATS-DESIGN.md §4.1` "Option A"). Binding it
algebraically is `SLOT-CAVEATS-DESIGN.md` Phase 5 — out of scope for
the unification commit.

**Recommendation:** ship `WitnessedPredicate` as
*executor-side-binding-only* in v1. The kind's own AIR provides
soundness for the predicate; the executor's responsibility is to
*call* the verifier and reject the action on failure. Algebraic
binding into the EffectVmAir is a follow-on.

### §6.6. Privacy boundary contract per kind

Each `WitnessedPredicateKind` needs a documented boundary contract
(§5). The recommendation is to require it: a kind cannot be
registered without rustdoc lines in the form
`BOUNDARIES.md §5.2`:

```
/// Boundary contract:
/// - Cleartext-inside:  <population>
/// - Commitment-inside: <population>
/// - Acceptance-inside: <population>
/// - Out-of-band:       <population>
```

Editorial discipline, not type. Per `BOUNDARIES.md §5.2`.

---

## §7. Recommended sequencing

After slot caveats v1 lands (Phases 1-4 in
`SLOT-CAVEATS-DESIGN.md §8`), the natural ordering for unification:

### §7.1. Phase 1 — `WitnessedPredicate` module (~250 LOC)

Create `cell/src/predicate.rs`. Add `WitnessedPredicate`, `InputRef`,
`WitnessedPredicateKind`, `WitnessedPredicateVerifier` trait,
`WitnessedPredicateRegistry`. Register the built-in kinds with stub
verifiers (calling out to existing
`circuit::temporal_predicate_dsl::verify_temporal_predicate`,
`bridge::present::verify_predicate_proof`, etc.).

Pure additive — no existing types change yet. Adds unit tests for
each registered kind.

### §7.2. Phase 2 — Lift `StateConstraint::TemporalPredicate` to `Witnessed` (~80 LOC)

Replace the typed `StateConstraint::TemporalPredicate { i, dsl_hash }`
variant with `StateConstraint::Witnessed(WP)`. Update
`cell/src/program.rs` evaluator to delegate to the registry. Maintain
serde back-compat via `#[serde(other)]` or an explicit version tag.

### §7.3. Phase 3 — DFA classification as a `Witnessed` kind (~150 LOC)

Per `DFA-RATIONALIZATION-DESIGN.md §3` (Option B-with-borrowings),
the wire DFA router gains the unified compiler. The
`WitnessedPredicate { kind: Dfa, commitment: route_table_root }`
becomes a first-class predicate kind, usable from slot caveats and
preconditions.

The first real consumer: an `apps/*` cell that wants "this message
must DFA-classify to `RouteTarget::Userspace { kind: 'auth' }` for
the SetField to apply." Encodes as
`Preconditions::witnessed: vec![WP { kind: Dfa, … }]`.

### §7.4. Phase 4 — Lift bridge predicate proofs (~120 LOC)

Replace `BridgePredicateProof` direct-callers with
`WitnessedPredicate { kind: BridgePredicate, … }`. Intent
`PredicateRequirement` becomes a `WitnessedPredicate` declaration;
its fulfillment becomes a `WitnessedPredicate` instance.

### §7.5. Phase 5 — Collapse `turn::preconditions::Precondition` (~−100 LOC)

Per §4.3 case 1, fold the `turn`-side builder enum into a
`cell::Preconditions::builder()` method. Net deletion.

### §7.6. Phase 6 — `Capability::caveats: Vec<CapabilityCaveat>` (~200 LOC)

Add a typed `CapabilityCaveat` enum to `cell::capability`. Variants:
`FacetConstraint(FacetConstraint)`, `Witnessed(WP)`. Backward-compat:
existing `allowed_effects: Option<EffectMask>` and `ExtendedFacet`
stay; the new field is additive.

This is the **payoff** phase: a capability can now carry "this cap
only fires when you produce a DFA-match proof against the
governance-bound route table." Or "only when you produce a
temporal-predicate proof of `balance >= 100 for 30 steps`." Either
without changing the executor, because the `WitnessedPredicate`
registry already has those kinds.

### §7.7. Phase 7 (deferred) — AIR-bind `WitnessedPredicate` verifier results

Per §6.5: the `EffectVmAir` gains constraints that *bind* the WP
verifier's accept/reject to the transition. Per-kind, opt-in. Same
shape as `SLOT-CAVEATS-DESIGN.md` Phase 5.

### §7.8. Phase 8 (deferred) — collapse `storage::programmable` (per `SLOT-CAVEATS-DESIGN.md §5` Option C)

Storage queues become cells whose program is a `Vec<StateConstraint>`,
some of which are `Witnessed(WP { kind: Dfa, … })` for the
ContentPattern case. The `storage::programmable` crate stops having
its own enforcement loop. Large; gated on `MerkleQueue::root` being
folded into the queue cell's `fields[1]` per
`STORAGE-REFLECTIVITY-RBG-DFA-AUDIT.md` Q4.2.

### §7.9. LOC budget

| Phase | Net LOC | Risk |
|---|---:|---|
| 1. predicate module | +250 | low |
| 2. TemporalPredicate lift | +80 | low |
| 3. DFA as WP kind | +150 | medium (depends on DFA rationalization) |
| 4. Bridge predicate lift | +120 | low |
| 5. Precondition collapse | −100 | low |
| 6. CapabilityCaveat | +200 | low |
| 7. AIR-bind | +400 | high (circuit work) |
| 8. Storage collapse | +0 / −500 | high (multi-crate refactor) |

Phases 1-6 are ~700 LOC net. Phases 7-8 are deferred multi-week
workstreams.

---

## §8. Connection to DFA caveats specifically

The designer asked: "can 'that DFA matched' be a caveat?" Yes.

### §8.1. The shape

In v1 the natural form is **`StateConstraint::Witnessed(WP { kind:
Dfa, … })`** on a cell whose state field at some slot indexes a
classification result. Worked example: a "user-authenticated" cell
whose slot 0 holds the user's role token, and whose program declares
that any `SetField` action targeting slot 1 must come with a
DFA-classify proof against the federation-bound route table:

```rust
const ROUTE_TABLE_ROOT: [u8; 32] = …; // from federation constitution
const INPUT_WITNESS_SLOT: u8 = 5;   // action's witness blob[5] is the
                                    // message bytestring
const PROOF_SLOT: u8 = 6;           // action's witness blob[6] is the
                                    // DFA-trace STARK proof

pub fn auth_cell_program() -> CellProgram {
    CellProgram::Predicate(vec![
        StateConstraint::Witnessed(WitnessedPredicate {
            kind: WitnessedPredicateKind::Dfa,
            commitment: ROUTE_TABLE_ROOT,
            input_ref: InputRef::Witness { index: INPUT_WITNESS_SLOT },
            proof_witness_index: PROOF_SLOT,
        }),
    ])
}
```

### §8.2. How the executor verifies

Per `DFA-RATIONALIZATION-DESIGN.md §1.5`: the AIR for
`generate_air_trace` (the `(step, state, byte, next_state)` row
shape) is in `circuit/src/dsl/circuit.rs:1711-1941`. The
`WitnessedPredicate::Dfa` verifier:

1. Loads the route table whose root matches `commitment`. (The
   table is the cleartext "shape" — but the proof's
   zero-knowledge over both pattern and input still holds.)
2. Resolves the input via `input_ref` (in the example, reads from
   `action.witness_blobs[5]`).
3. Loads the proof bytes via `proof_witness_index`.
4. Calls `wire::dfa_router::verify_air_trace(commitment, input,
   proof)`.
5. On accept: returns `Ok(())`. On reject: the executor refuses
   the action.

The `RouteTarget` is *not* part of this verifier's contract — that's
the router's job at *classification* time (which can happen out of
band). The caveat's job is just "the input was accepted by *some*
target under this table commitment." If the cell wants to predicate
on which target was reached, the input_ref / commitment can encode
that (e.g., a per-target sub-commitment).

### §8.3. Composition with `CapabilityCaveat::Witnessed`

After Phase 6 (§7.6), a *capability* can carry a DFA caveat:

```rust
Capability {
    target: …,
    permissions: …,
    allowed_effects: Some(EFFECT_TRANSFER),
    caveats: vec![
        CapabilityCaveat::Witnessed(WitnessedPredicate {
            kind: WitnessedPredicateKind::Dfa,
            commitment: ROUTE_TABLE_ROOT,
            input_ref: InputRef::PublicInput { pi_index: 0 },
            // The PI carries the message body — so the caveat says
            // "this cap can only authorize an action whose message
            // body DFA-classifies under this route table."
            proof_witness_index: 0,
        }),
    ],
}
```

The capability becomes a *typed pattern-bound right*: the holder can
exercise the cap only on messages that route to the named target.

### §8.4. How it interacts with `RouteTarget::Userspace`

Per `DFA-RATIONALIZATION-DESIGN.md §4.1-§4.4`: `RouteTarget::Userspace
{ kind: String, payload: Vec<u8> }` is the open variant for app-defined
destinations. After unification, a `RouteTarget::Userspace { kind:
"witnessed_caveat", payload: bincode(WP) }` is the natural way to
encode "this route requires the holder to present this `WitnessedPredicate`
on top of the DFA classification." Two-stage:

1. **Stage 1: DFA classifies.** Router returns
   `RouteTarget::Userspace { kind: "witnessed_caveat", payload }`.
2. **Stage 2: dispatcher decodes the payload as a `WP` and treats
   it as a per-route caveat** to evaluate alongside the cell's slot
   caveats.

The route DFA selects the destination; the route's WP gates the
action; the cell's slot caveats validate the resulting transition.
Three stages, three evaluators, **all calling the same WP registry**.

---

## §9. Connection to STORAGE-AS-CELL-PROGRAMS

The premise of STORAGE-AS-CELL-PROGRAMS (per
`STORAGE-REFLECTIVITY-RBG-DFA-AUDIT.md` and
`SLOT-CAVEATS-DESIGN.md §5` Option C) is that the storage primitives
should be expressible as *cells whose programs are
`CellProgram::Predicate(Vec<StateConstraint>)`*. After this study, the
predicate inventory needed for each storage primitive is well-defined:

### §9.1. `CapInbox` (`storage/src/inbox.rs`)

Needs:
- **Authorization:** `StateConstraint::SenderAuthorized { set:
  AuthorizedSet::PublicRoot { … } }` against a quota-bound sender set.
- **MaxSize:** `StateConstraint::FieldLte` against a length slot.
- **MinDeposit:** `StateConstraint::FieldGte` against a deposit slot.

Every predicate already in the inventory. The CapInbox-as-cell
collapses to ~3 slot caveats. **No new predicate kinds.**

### §9.2. `ProgrammableQueue` (`storage/src/programmable.rs`)

Needs all of `QueueConstraint`'s 9 variants. Every one already aliased
to a `StateConstraint` per §1.8. The Lane G Phase 2 (Option C) is the
collapse. **No new predicate kinds.**

### §9.3. `PubSubTopic` (gossip / `intent::gossip`)

Needs:
- **Topic filter:** `WitnessedPredicate { kind: Dfa, commitment:
  topic_filter_root }`. Per
  `DFA-RATIONALIZATION-DESIGN.md §6.2-§6.4`.
- **Subscription ACL:** `StateConstraint::SenderAuthorized { set: …
  }` for membership-gated topics.

The DFA kind unlocks topic-filtered gossip; the SenderAuthorized
caveat unlocks scoped subscription. **Both predicates already in
inventory after Phase 3** (§7.3).

### §9.4. `BlindedQueue` (`storage/src/blinded.rs`)

Needs:
- **Commitment hiding:** producer carries randomness; queue stores
  `BlindedItemCommitment`. *Not a predicate* — a commitment scheme.
- **Spend proof:** `WitnessedPredicate { kind: Custom { vk_hash:
  blinded_queue_air_vk }, commitment: queue_root, input_ref:
  InputRef::Witness { index: nullifier_slot }, proof_witness_index: …
  }`. The current `/consume-private` endpoint stub
  (`AUDIT-privacy.md §...`) becomes a WP verifier call.

**One new `vk_hash`-registered kind needed.** Slots into the registry
without per-primitive plumbing.

### §9.5. `RelayOperator` (`storage/src/operator.rs`)

Wraps `CapInbox`. Needs:
- **Per-relay quota:** `StateConstraint::RateLimitBySum { slot_index:
  bytes_relayed_slot, max_sum_per_epoch, epoch_duration }`.
- **Capacity check:** `StateConstraint::FieldLte` against a capacity
  slot.
- **Sender authorization:** as in CapInbox.

Every predicate already in the inventory. **No new predicate kinds.**

### §9.6. The migration claim

Every storage primitive's predicate needs are met by the unified
inventory after Phases 1-3 of §7:

| Primitive | New kinds needed |
|---|---|
| CapInbox | none |
| ProgrammableQueue | none |
| PubSubTopic | none (Dfa kind covers it) |
| BlindedQueue | one (`Custom { vk_hash: blinded_queue_vk }`) |
| RelayOperator | none |

**STORAGE-AS-CELL-PROGRAMS is therefore a clean migration, not a
port.** Every storage primitive becomes a cell whose program is a
specific composition of predicates that the unified inventory
supplies. Apps that build new storage shapes (a new queue kind, a
new pool primitive) register their own `WitnessedPredicateKind::Custom
{ vk_hash }` and inherit the entire evaluation pipeline. No per-kind
executor plumbing.

This is the justification the unification design exists for. Without
`WitnessedPredicate`, each storage primitive's bespoke predicate
shape (the legacy `QueueConstraint::Custom { expr }` form, the
`BlindedQueue`'s ad-hoc consume-private endpoint, the relay's hard-
coded quota logic) would each need its own enforcement loop. With
the unification, they share one — the executor's predicate evaluator
calls the registry, and the registry already knows how to verify
every shape they need.

---

## §10. Honest closing — what this doesn't fix

1. **Macaroon caveats remain a parallel system.** They're a token-
   presentation pipeline, not a transition-validity vocabulary. The
   unification doesn't reach them. They have their *own* polymorphic
   registry that this design borrows from but does not absorb.

2. **Intent `MatchSpec` remains structural, not byte-pattern.** The
   matcher is its own predicate algebra. A `MatchSpec::compile_to_dfa()`
   is a separable optimization that may or may not be worth doing
   (per `DFA-RATIONALIZATION-DESIGN.md §6.1`).

3. **Federation aggregate signatures are not STARK-shaped.** The
   `(commitment, input, proof)` triple applies but the verifier
   pipelines (BLS pairings, KZG, weighted-threshold) are
   structurally different. Keep parallel.

4. **`CapabilityProof::SignedAttestation` is signature-based.** The
   removed `StarkMembership` variant (`cell/capability_proof.rs:79`)
   *would have* fit `WitnessedPredicate { kind: MerkleMembership }`
   once a real gadget lands. Restore it then, not before.

5. **The unification doesn't shrink any executor code today.** It
   *enables* future shrinking (Phase 5's `Precondition` collapse,
   Phase 8's storage collapse) but the immediate effect is one new
   module + a typed wrapper. The win is *future plug-in ergonomics*,
   not present-day deletion.

6. **The `Custom { vk_hash }` escape is a partial-trust surface.**
   Just like `Effect::Custom`, a maliciously-registered verifier kind
   can accept arbitrary proofs. The registry needs the same audit
   discipline as the effect registry (kind names listed in
   constitution, vk_hashes attested, verification function bytecode
   reproducible).

7. **Boundary contracts are editorial, not type-enforced.** The
   per-kind boundary doc string (§6.6) is discipline. Apps that
   register a new `Custom` kind can lie about its boundary contract.
   The mitigation is audit tooling, not the type system.

8. **γ.2 cross-cell composition stays outside the registry.** Per
   §6.4: the bilateral predicate's *aggregation* is a γ.2 pipeline
   step, not a predicate kind. The registry handles single-cell
   predicates; γ.2 composes them.

9. **The 15 collapsing kinds (§1.6) are mostly already-witness-
   bearing.** The unification doesn't add new predicate kinds in
   v1 — it just gives the existing ones a shared shell. The new
   capability surface (`CapabilityCaveat::Witnessed`) is the
   user-visible payoff; the executor-side ergonomics matter only to
   future predicate authors.

10. **None of this is a substitute for `SLOT-CAVEATS-DESIGN.md`.** The
    21-variant `StateConstraint` enum is the cell-program-author's
    *static* vocabulary; `WitnessedPredicate` is the
    *witness-bearing* generalization that sits inside it (as
    `StateConstraint::Witnessed`). Both vocabularies exist; one is
    a superset of the witness-attached column of the other.

---

## §11. Cited file pointers

Code:
- `cell/src/program.rs:223-397` — 21-variant `StateConstraint`.
- `cell/src/program.rs:73-141` — `HashKind`, `AuthorizedSet`,
  `DeltaRelation`, `ReadSet`, `CustomDescriptor`, `SimpleStateConstraint`.
- `cell/src/preconditions.rs:1-336` — cell-side `Preconditions`,
  `CellStatePrecondition`, `EvalContext`, `PreconditionError`.
- `turn/src/preconditions.rs:1-162` — turn-side
  `Precondition::{SlotEquals, SlotZero, NonceAtLeast}` builder.
- `cell/src/capability.rs:36-291` — `CapabilityRef.allowed_effects`,
  delegation, attenuation.
- `cell/src/facet.rs:182-365` — `ExtendedFacet`, `FacetConstraint`
  (MaxTransferAmount / AllowedTargets / RateLimit / Budget),
  `is_at_least_as_tight`.
- `cell/src/capability_proof.rs:49-355` — `CapabilityProof`,
  `CapabilityProofData::SignedAttestation`. The removed
  `StarkMembership` variant is noted at lines 79-83.
- `cell/src/seal.rs:1-217` — `SealPair`, `SealedBox`, `SealerPublic`.
- `cell/src/peer_exchange.rs:35-303` — `PeerStateTransition`,
  optional `transition_proof: Option<Vec<u8>>`.
- `cell/src/note_bridge.rs:74-447` — `PortableNoteProof`,
  `BridgedNullifierSet`, `BridgeError`, `BridgeReceipt`.
- `cell/src/value_commitment.rs:122-759` — `ValueCommitment`,
  `ConservationProof`, `BulletproofRangeProof`,
  `FullConservationProof`.
- `cell/src/stealth.rs:47-221` — stealth address ownership predicate.
- `cell/src/oblivious_transfer.rs:39-80` — OT protocol predicates.
- `circuit/src/temporal_predicate_dsl.rs:1-922` — full DSL temporal
  predicate AIR, `TemporalPredicateProof`,
  `prove/verify_temporal_predicate`, `TemporalPredicateRequirement`.
- `circuit/src/dsl/circuit.rs:1711-1941` — DFA-lookup constraint
  AIR.
- `wire/src/dfa_router.rs:1-700` — canonical DFA router with
  `Router`, `RouteTable`, `RouteTarget`, `GovernedRouter`.
- `apps/governed-namespace/src/routes.rs:1-287` — duplicate
  longest-prefix matcher.
- `rbg/src/routing.rs:1-1346` — workspace-excluded full
  NFA→DFA implementation with `Pattern`, `AirTraceRow`,
  `generate_air_trace`.
- `intent/src/lib.rs:179-373` — `PredicateRequirement`,
  `Constraint`, `MatchSpec`, `ActionPattern`, `IntentKind`.
- `intent/src/matcher.rs` — matcher impl.
- `intent/src/solver.rs:24-528` — `IntentNode`, `RingTrade`,
  `RingSolver`.
- `intent/src/trustless.rs:1-217` and surrounding — 7-layer protocol
  with `EngineError`, `BatchState`, `SealedTurn`.
- `intent/src/gossip.rs` — flat broadcast (DFA candidate).
- `bridge/src/present.rs:149-3398` — `BridgePresentationProof`,
  `WirePresentationProof`, `BridgePredicateProof{Inner}`,
  `Predicate { Gte/Lte/Gt/Lt/Neq/InRange }`,
  `verify_predicate_proof`, `verify_predicate_program`,
  `verify_committed_threshold_proof`.
- `chain/src/credential.rs:191-296` — `verify_credential_proof_locally`.
- `chain/src/withdraw.rs:337` — `verify_withdrawal_proof_locally`.
- `macaroon/src/caveat.rs:18-167` — `CaveatType`, `Caveat` trait,
  `WireCaveat`, `CaveatSet`. Reserved type-ID ranges at 27-45.
- `macaroon/src/caveat_3p.rs:35` — `ThirdPartyCaveat`.
- `macaroon/src/action.rs:16`, `macaroon/src/resource.rs:27-98` —
  `Action`, `ResourceSet`.
- `storage/src/programmable.rs:60-580` — legacy `QueueConstraint`,
  evaluator, validation context. The Phase-1 alias to
  `cell::program::StateConstraint` is at lines 30-36.
- `storage/src/blinded.rs:48-415` — `BlindedQueue`.
- `storage/src/operator.rs:38-191` — `RelayOperator`,
  wraps `CapInbox`.
- `storage/src/inbox.rs` — `CapInbox`, `InboxError`,
  `InboxMessage`.
- `dregg-dsl/src/ir.rs:9-194` — `ConstraintIr`, `Statement`,
  `Requirement{Kind}`, `Mutation`, `MatchArm`. `RequirementKind` is
  the atomic-predicate-primitive enum (`LessEqual`, `GreaterEqual`,
  `Equal`, `NotEqual`, `Membership`, `BitRange`,
  `MerkleAtPosition`, `Poseidon2Hash`).
- `dregg-dsl/src/{gen_air,gen_kimchi,gen_plonky3}.rs` — backend
  emitters.
- `dregg-dsl/src/parse.rs:13-46` — `parse_caveat`, parser for
  `#[dregg_caveat]` functions.
- `types/src/lib.rs:281-309` — `AttestedRoot` definition.
- `federation/src/threshold.rs:37` — `FederationCommittee`.
- `federation/src/receipt.rs:122` — `FederationReceipt::verify`.
- `turn/src/witnessed_receipt.rs:1-115` — `WitnessedReceipt`,
  `WitnessBundle`, `trace_rows`.
- `turn/src/escrow.rs` — `EscrowCondition`.
- `turn/src/obligation.rs` — `Obligation`.
- `turn/src/conditional.rs` — conditional turn predicates.
- `turn/src/presence_discharge.rs:27` — `PresenceCaveat`.

Design docs:
- `SLOT-CAVEATS-DESIGN.md` — Lane G lift, 21-variant enum, executor
  evaluation, Custom escape.
- `SLOT-CAVEATS-EVALUATION.md` — adopted findings, including the 21
  variants, replay-snapshot semantics, BlindedSet variant for
  `SenderAuthorized`.
- `BOUNDARIES.md` — populations vocabulary
  (`cleartext-inside/commitment-inside/acceptance-inside/out-of-band`),
  per-subsystem boundary contracts, `§5.2` rustdoc convention.
- `DFA-RATIONALIZATION-DESIGN.md` — three DFA implementations,
  the Option B-with-borrowings unification, composition with slot
  caveats (§5), composition with intent (§6), composition with
  CapTP (§7).
- `STORAGE-REFLECTIVITY-RBG-DFA-AUDIT.md` — the storage / RBG / DFA
  audit naming the open loops.
- `AUDIT-distributed-semantics.md`, `AUDIT-privacy.md`,
  `AUDIT-nullifiers.md`, `CELL-CRATE-REVIEW.md`,
  `AUDIT-sovereign-witness-teeth.md`,
  `WITNESSED-RECEIPT-CHAIN-DESIGN.md`,
  `STAGE-7-GAMMA-2-PI-DESIGN.md`, `DESIGN-max-custom-effects.md`,
  `FEDERATION-UNIFICATION-DESIGN.md`,
  `APPS-USERSPACE-GAPS.md`.
