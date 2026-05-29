# Rebuild Lens 01 — The Capability Substrate as Spine

> **Status:** forward design exploration, not an audit. Current-state claims
> are cited `file:line`; everything else is a proposal for the "under and
> through" rebuild.
>
> **Anchor:** the local-first, seL4-reflectable **capability /
> capability-derivation-tree (CDT)** is the keystone. Cells, predicates,
> proofs, and consensus are *servants of* the capability layer.
>
> **Mandate to self:** be self-adversarial. The user wants this lens's
> hidden constraints and tensions mapped, not advocacy. Section 7 is the
> point of the document as much as Sections 1–6.

---

## 0. The thesis in one breath

Today Dragon's Egg has *a* capability model that is genuinely good and
already seL4-shaped: a slot in a c-list holds a typed, attenuable, faceted
reference to a target cell (`cell/src/capability.rs:43` `CapabilityRef
{target, slot, permissions, allowed_effects}`; `CapabilitySet` is the
CNode with monotone `attenuate`/`attenuate_faceted`/`attenuate_in_place` at
`capability.rs:262,288,342`; `facet.rs` `EffectMask` is the
interface-restriction lattice). But that model is *a participant* in the
system, sitting next to authorization (`turn/src/action.rs:206`
`Authorization` coproduct), effects (`action.rs:760` `Effect`), conservation
(`action.rs:698` `LinearityClass`), consensus (`blocklace/`), and durable
export (`captp/src/sturdy.rs`). These are **peers** today, and the seams
between them are where the rot lives: auth verified in plain Rust outside
any proof, sturdy-refs as a `HashMap` side-table (`sturdy.rs:69`),
delegation modes that don't enforce (`action.rs:642` `DelegationMode` —
"only `None` is enforced"), revocation/nullifier sets as executor side
tables.

The thesis of *this* lens: **make the capability the irreducible primitive
and demote everything else to a way of describing, restricting, or
attesting capability exercise.** A turn is not "a batch of effects that
happen to check some caps"; a turn is **a bundle of capability exercises,
each carrying a proof that an unforgeable derivation chain authorized it.**
"Proof is truth" becomes native: the proof attests *the exercise was
licensed by the CDT*, and the executor is just a cache that replays the
derivation. This is the strongest possible reading of the FIXED DECISION.

Whether that reading is *correct* — versus capability being one faithful
layer that should not swallow conservation and set-membership — is the
honest question I hold open until Section 8.

---

## 1. The irreducible primitive, and what becomes a servant

### 1.1 The primitive: a *cap* is a derivation node, not a row in a table

Strip `CapabilityRef` to its load-bearing essence and you get four things:
**what** you can reach (`target`), **what subset of its interface**
(`allowed_effects`/facet), **under what authority discipline**
(`permissions: AuthRequired`), and **bounded by what caveats** (expiry,
witnessed predicates). The slot number (`capability.rs:48`) is *not*
essential — it is a local-naming convenience (a CSlot index). The
*essential* identity of a cap is **its position in a derivation tree**: who
minted the root, and the exact chain of attenuations from root to here.

So the rebuilt primitive is the **CDT node**:

```
Cap {
    root:        RootSeal,        // unforgeable origin (cell-mint or seL4 reflection)
    target:      CellRef,         // what authority reaches
    authority:   AuthorityClass,  // the discipline (was AuthRequired)
    facet:       Interface,       // the restricted interface (was EffectMask, but richer)
    caveats:     CaveatSet,       // expiry, predicate, rate — the BindingSite of Lens-2
    parent:      Option<CapHash>, // the derivation edge: this cap = attenuate(parent, Δ)
    delta:       Attenuation,     // the narrowing applied at this edge (must be ≤-monotone)
}
CapHash = H(canonical(Cap))      // content-addressed identity == CDT node id
```

The crucial inversion: **a cap is identified by its derivation, not by its
storage location.** `CapHash` is the node's name. A c-list (`CapabilitySet`)
becomes a *cache of CapHashes a cell currently holds*, not the source of
truth. The source of truth is the **CDT**: the partial order of
`(parent → child)` edges, each edge a monotone attenuation
(`is_attenuation` at `capability.rs:461` generalizes from
`AuthRequired`-only to the whole `Attenuation` lattice). The CDT is
*append-only and content-addressed* — which is exactly the shape of the
blocklace (per-strand append-only causal log). **The CDT and the strand log
are the same data structure viewed two ways.** That collapse is the deepest
move this lens makes, and Section 4 returns to it.

### 1.2 What each existing concept becomes a servant of

- **Cells** become *the targets and the mints of caps.* A cell is still the
  unit of state and lifecycle (`cell/src/lifecycle.rs` `CellLifecycle`
  survives unchanged — terminal objects are a keeper). But a cell's
  *authority surface* is now defined purely as "the set of root caps it
  mints." A cell does not "have permissions"; a cell *mints a root cap whose
  facet is its full interface*, and every actual access is an attenuation of
  that root. `Permissions` on a cell collapses into "the root seal's
  authority class + the cell's mint policy." This kills the `AuthRequired`
  field's double life (it lives on both the cell and the cap today).

- **Predicates** become *caveats on cap exercise.* The audit already found
  the collapse: the 4 gates (Precondition / StateConstraint /
  CapabilityCaveat / `Authorization::Custom`) all wrap one
  `WitnessedPredicate`. Under this lens that is not a coincidence — **a
  predicate is the witnessed precondition of a cap exercise**, and the
  `CapabilityCaveat` enum at `cell/src/capability.rs:31` is the *canonical
  home* the other three should migrate into. A state-constraint is "this
  exercise is licensed only when the witnessed predicate over the target's
  state holds"; an authorization-custom is "this exercise is licensed only
  when the witnessed predicate over the signing message holds." Both are
  caveats. The `BindingSite{when,input,signed_by}` the audit proposes is the
  caveat's *evaluation context*.

- **Proofs** become *the attestation that the CDT licensed the exercise.*
  See Section 2. This is where "proof is truth" lives natively.

- **Consensus / strands** become *the medium in which the CDT lives and the
  mechanism by which revocation (a tree edit) achieves agreement.* The
  blocklace is the CDT's backing store; finality is "this CDT edit is
  causally stable across the reference group." See Section 4.

- **Authorization (the coproduct at `action.rs:206`)** mostly *dissolves.*
  `Signature`, `Proof`, `Custom`, `Token`, `Stealth`, `Bearer`,
  `CapTpDelivered`, `OneOf` are today eight ways of saying "I'm allowed."
  Under cap-centrism there is *one* way — "here is a path in the CDT from a
  root I control to this exercise, plus the witness each edge's caveat
  demands" — and the eight variants become **eight kinds of root seal /
  caveat-discharge**, not eight top-level auth modes. `Signature` = "the
  root seal is a keypair; the discharge is a sig." `Custom` = "an edge has a
  witnessed-predicate caveat." `Bearer` = "the path is carried inline rather
  than resident in a c-list." `Stealth` = "the root seal is a one-time
  derived key." `OneOf` = "the CDT path is a *choice* of sub-paths" (the
  coproduct moves *inside* the path type). This is a large simplification
  and I flag it as ambitious (Section 7.2 on over-abstraction).

---

## 2. "Proof is truth," expressed natively: the CDT *is* the proof

This is the part of the rebuild where the capability lens is not just
*compatible with* the FIXED DECISION — it is arguably its most natural
home.

### 2.1 The current gap, in cap terms

Today auth is checked in plain Rust outside any proof (the FIXED DECISION's
indictment), and the cap path is the worst offender: `ExerciseViaCapability`
(`action.rs:1073`) does "look up a capability by slot, verify permissions,
execute inner effects" — *all executor-side*. The proof (EffectVM AIR)
re-derives some effect semantics but **never re-derives that a valid CDT
path authorized the exercise.** Bearer caps (`action.rs:459`
`BearerCapProof` with `DelegationProofData::StarkDelegation`) are the *only*
place a derivation chain is even proven — and that proof is bolted onto one
auth variant, not the spine.

### 2.2 The native form: every exercise carries a *derivation proof*

Make the bearer-cap insight universal. **Every cap exercise's proof
includes a sub-proof that a valid CDT path exists from an unforgeable root
to the exercised node, and that every edge on the path is a monotone
attenuation whose caveats are discharged by the carried witnesses.**

Concretely the public inputs of a turn's proof bind:

1. **Root seals** — for each exercise, the root `Cap` and *why it's
   unforgeable* (a cell-mint root binds the cell id + mint nonce; a
   reflected seL4 root binds the badge — Section 3).
2. **Path commitment** — the Merkle/folded commitment to the chain
   `root → … → exercised`, with a circuit constraint per edge:
   `child.facet ⊆ parent.facet ∧ child.authority ≤ parent.authority ∧
   child.caveats ⊇ parent.caveats` (attenuation is monotone — this is
   `is_facet_attenuation` and `is_narrower_or_equal` lifted *into the AIR*,
   not checked in Rust).
3. **Caveat discharges** — for each caveat on the path, the witness that
   satisfies it (the `WitnessBlob` carrier at `action.rs:124` survives, now
   indexed *by CDT edge* not by predicate).
4. **Effect ⊆ facet** — the effects actually performed are a subset of the
   *leaf* cap's facet. This closes the FIXED DECISION's "effects_hash is a
   host commitment the AIR never re-derives" — the AIR re-derives that every
   effect is licensed by the facet of the cap that authorized it.

The slogan: **the proof attests "this exercise is the value of `eval` on a
genuine CDT morphism."** `ExerciseViaCapability` is literally described in
the code as "the categorical evaluation map (eval: B^A × A → B)"
(`action.rs:1069`). The rebuild makes that comment *true in the circuit*:
the proof is a proof that `eval` was applied to a real arrow in the cap
category, not a Rust function call the verifier trusts.

### 2.3 Why this is *more* faithful than the other lenses' "proof is truth"

A predicate-centric or effect-centric reading has to *bolt authorization
onto* the proof as an extra conjunct ("…and also the actor was allowed").
Under cap-centrism, authorization is not a conjunct — it **is** the
proof's subject. There is no "auth check" separate from "the exercise
happened"; the exercise *is* the traversal of an authorized arrow. The
auth-in-proof requirement is satisfied *by construction* rather than *by
addition*. That is a real argument for this lens being primary, and I'll
weigh it honestly against Section 7.

### 2.4 Versioning the arrow (closing the Urbit trap)

The FIXED DECISION names the un-versioned frozen AIR as "the Urbit trap."
Under cap-centrism the fix is clean: the *attenuation lattice itself* is
versioned, and the lattice version (`CapLatticeVersion`) is a public input
to every derivation proof. Because attenuation is the single rule the whole
system rests on, there is exactly one thing to version, and it is forced
into the PI by the path-edge constraint. The CDT edge constraint *is* the
AIR's semantics, so `AirVersion ≡ CapLatticeVersion` and it cannot be
omitted without the edge constraint being meaningless. The frozen-AIR
problem dissolves because there is no separate "effect semantics" to freeze
— there is only "is this edge a legal attenuation under lattice version V."

---

## 3. The seL4 reflection seam

This is the north star: an seL4-implemented Robigalia OS where **seL4
capabilities reflect into Dragon's Egg capabilities**. Today there is *zero*
seL4/Robigalia code and *no* reflection seam — but the cap model is
"already seL4 CNode/CSpace/CSlot-shaped" (the audit's words, and
`capability.rs` confirms: slot-allocated typed attenuable references).

### 3.1 The two directions

**Reflect IN (seL4 → dregg):** an seL4 cap is a local kernel object — a
typed, badged authority an seL4 thread holds in its CSpace, with no
consensus, no proof, no ledger. To reflect it into a dregg cap we need a
**root seal of kind `Sel4Reflected`**:

```
RootSeal::Sel4Reflected {
    kernel_badge:   u64,        // the seL4 badge (endpoint distinguisher)
    cnode_origin:   Sel4Path,   // CSpace path proving provenance on this machine
    machine_id:     MachineId,  // which Robigalia node's kernel vouches for it
    reflection_sig: MachineSig, // the rbg subsystem signs "this badge is live here"
}
```

The key realization: **seL4 gives us *local* unforgeability for free (the
kernel enforces it), so a reflected-in cap does NOT need a derivation proof
*on this machine* — the kernel IS the proof.** The dregg cap minted from it
inherits the seL4 cap's authority and the rbg-subsystem signature stands in
for the CDT root. The cap becomes "proof-bearing" only when it crosses a
machine boundary (Section 3.3).

**Reflect OUT (dregg → seL4 / network):** the durable form is already
right. A sturdy-ref (`captp/src/sturdy.rs`, `dregg://` + swiss number) and a
handoff certificate are *exactly* the "give a cap to another address space"
operation. The rebuild's change: the swiss-table (`sturdy.rs:69` `SwissTable
HashMap`) stops being an executor side-table and becomes a **cell** (the
audit's "nullifier/revocation/authorized-sender SETS should be CELLS"
applied to the swiss table too) — `export` is "mint a child CDT node whose
root is this swiss seal"; `enliven` is "present a path; receive the leaf
cap"; `revoke` is "append a tombstone edge to the CDT cell." When reflecting
*out to an seL4 machine*, the dregg cap is materialized as a kernel cap by
the rbg subsystem minting a CNode entry badged with `CapHash`.

### 3.2 What the primitive must look like for this to be clean

Three requirements fall out:

1. **Roots must be a sum type, and one summand is "the local kernel
   vouches."** This is why `RootSeal` (not "always a keypair or a cell
   mint") is the right shape. A dregg cap whose root is `Sel4Reflected`
   needs no signature and no STARK *for local exercise* — its authority is
   the kernel's. The `AuthorityClass` enum must admit a `KernelVouched`
   discipline alongside `Signature`/`Proof`.

2. **Badge ≡ CapHash.** seL4 badges are 64-bit (or fewer) kernel-assigned
   distinguishers; dregg `CapHash` is 256-bit content-addressed. The clean
   seam is: when reflecting out, the rbg subsystem maintains a
   `badge ↔ CapHash` table (a cell), and the badge is a *local handle* to
   the content-addressed identity, exactly as the c-list slot is a local
   handle today (`capability.rs:48`). The slot/badge duality is the same
   pattern at two layers — this is reassuring, the model is uniform.

3. **Attenuation must be expressible as both a kernel `Mint`/`CNode_Mint`
   with reduced rights AND a dregg CDT edge.** seL4 `Mint` can reduce a
   badge and strip rights bits; dregg `attenuate_faceted` reduces the facet
   mask. These must agree: the facet lattice (`facet.rs` `EffectMask`) needs
   a *projection onto seL4 rights bits* (read/write/grant/grantreply) so a
   reflected cap's facet maps losslessly onto kernel rights, and a kernel
   `Mint` reflects back as a dregg `attenuate`. If the lattices don't align,
   the seam leaks authority. **This is a concrete design constraint the
   current `EffectMask` does not yet satisfy** — the 18+ effect bits
   (`facet.rs` `EFFECT_*`) have no canonical projection onto seL4's 4-ish
   rights bits, and inventing one is real work (Section 7.6).

### 3.3 Reconciling local-first (no consensus) with the gossiped ledger

This is the sharpest tension in the seam, and the user named it. seL4 caps
are **local kernel objects with no consensus**; the dregg ledger is a
**gossiped multi-party CDT.** How can a cap be both?

The resolution: **a cap is local-first by default and gains consensus only
on demand, at the boundary it crosses.** Three regimes for one primitive:

- **Intra-machine (n=1 strand):** the kernel is the authority. No proof, no
  gossip, instant finality (the audit notes "n=1 strands get instant
  finality"). A `Sel4Reflected` cap exercised on its home machine is a plain
  kernel `Call`. The dregg layer records it in the local strand log *for
  history*, not for agreement. This is orthogonal persistence: the log is
  the inputs (the exercise events), not the bytes.

- **Cross-machine, point-to-point (handoff):** when the cap crosses to
  another address space via CapTP handoff (`captp` handoff certs), it
  *acquires a derivation proof* at the boundary — the membrane (Section 4.4)
  emits a proof-carrying receipt (the "badge" in the goal usecase). The
  receiving machine verifies the proof instead of trusting its kernel
  (which never saw the cap). Still no global consensus — two-party,
  store-and-forward, works offline. **This is the BLE/phone-gossip case:**
  two friends in Bluetooth range exchange proof-carrying caps; each
  verifies the other's CDT path; neither needs a quorum.

- **Multi-party shared resource (the ledger proper):** *only* when a cap's
  exercise contends for a resource whose conservation requires agreement
  (a balance, a nullifier, a singleton) does the exercise enter the
  consensus regime — its CDT edit must become causally stable across the
  reference group. **Revocation is the canonical case** (Section 7.4): "this
  cap no longer licenses exercises" is a claim that all parties must
  eventually share, and *that* needs finality.

The unifying principle: **consensus is a property a cap exercise *opts
into* based on what it touches, not a property of the substrate.** Local
exercises are kernel-fast; contended exercises pay for agreement. This is
the "fluid about boundaries" mandate realized at the cap layer — and it
maps cleanly onto seL4 (local = kernel) vs ledger (shared = gossip). I
believe this is the strongest contribution of the cap-as-spine framing.

---

## 4. Fluid boundaries with the cap layer primary

### 4.1 Is a ReferenceGroup a capability?

Yes — and this is a satisfying collapse. Today `ReferenceGroup`
(`blocklace/src/ordering.rs:545`) is a *view* over the shared DAG, and
`GovernanceMode` (`blocklace/src/constitution.rs:750`:
`Open`/`InviteOnly`/`Constitutional`) is governance-as-lens. Under
cap-centrism a reference group **is a cell that mints membership caps**:

- The group cell's root cap is "participate in this group's DAG."
- `GovernanceMode` is the group cell's **mint policy** — the caveat set on
  the membership caps it will issue. `Open` = "mint a membership cap to any
  presenter." `InviteOnly` = "mint only when the request carries a valid
  membership cap as introducer" (a CDT edge: your membership derives from
  an existing member's). `Constitutional` = "minting requires a witnessed
  predicate (the vote) discharged" — i.e., a caveat.
- A "friend group" that gossips over BLE is a group cell whose membership
  caps are held locally and exchanged peer-to-peer; the gossip *is* CDT
  edge propagation.

This is elegant: governance modes stop being a bespoke enum and become
**instances of the one caveat/attenuation vocabulary.** Joining a group is
acquiring a cap; being kicked is revocation; the constitution is a caveat.

### 4.2 Is a fork a cap-scoped sandbox?

The biggest consensus gap the audit names is "NO fork/branch/merge
primitive." Cap-centrism gives a crisp definition: **a fork is a cap that
scopes a *copy-on-write sub-CDT*.** Forking a strand onto an rbg subsystem
"to evaluate in a container" is: mint a `ForkCap` whose target is a snapshot
of the parent CDT, with facet = "exercise freely within the sandbox, but
your edits are confined to a child sub-tree." The fork's exercises are real
caps in a real (sandboxed) CDT; **merge is re-rooting the fork's sub-CDT
under the parent** — which is legal *iff* every edge in the fork sub-tree is
still a monotone attenuation of the (possibly-advanced) parent. Merge
conflicts are *attenuation violations* (the fork relied on authority the
parent has since narrowed). This gives merge a **principled rejection
rule** instead of an ad-hoc CRDT tie-break: a merge is sound exactly when
the fork's CDT edges remain valid against the parent's current state.

`DelegationMode::SnapshotRefresh` (`action.rs:653`) is *already* a baby
version of this ("child inherits parent's caps as a point-in-time snapshot;
refresh to pick up new caps; revocation is eventual"). The fork primitive
is `SnapshotRefresh` promoted to a first-class CDT operation with a defined
merge. **Cut the unenforced `ParentsOwn`/`Inherit` modes
(`action.rs:646-652`, admitted no-ops); keep and generalize
`SnapshotRefresh` into Fork.**

### 4.3 Pluggable finality and "various topologies"

The audit names "monomorphic finality (one hardcoded Cordial-Miners tau,
NOT pluggable)" as a from-a-paper risk. Under cap-centrism, **finality is a
caveat on the *commit cap* of a strand.** A strand's append cap carries a
caveat "this edit is stable when predicate F holds," where F is the finality
rule. F = `n=1` → instant (the trivial predicate). F = Cordial-Miners-tau →
the current rule. F = "BFT 2/3 signed" → a different witnessed predicate.
Because finality is a caveat (a `WitnessedPredicate` discharged by a
witness), it is *pluggable by construction* — different strands, even
different caps within a strand, can carry different finality caveats. A
"blockchain topology" is a reference group whose commit caps all share one
strict finality caveat; a "CRDT topology" is one whose commit caps have the
trivial caveat and rely on union-merge. **The topology is a choice of
caveat, not a choice of substrate.** This directly serves "able to implement
various blockchain OR other topologies."

### 4.4 The membrane = a boundary cap that emits a proof-carrying receipt

The goal usecase (zkRPC verifiable toolcalls) wants a "membrane = a
capability boundary that emits a proof-carrying receipt (the badge)." This
falls straight out: a membrane is a cap whose *facet is the exposed
interface* and whose *exercise produces a `WitnessedReceipt`*
(`turn/src/witnessed_receipt.rs` — a keeper, "state derivable from the
witness/input stream"). The MCP server (`node/src/mcp.rs`), the composed
prover (`sdk/src/full_turn_proof.rs`), and CapTP handoff — "all exist,
unjoined" — are joined *by the membrane cap*: the MCP tool call is a cap
exercise; the prover produces the derivation proof; the handoff carries the
resulting badge across the boundary. The membrane is not new machinery; it
is the cap primitive applied at an I/O boundary, with the receipt as the
"truth" the FIXED DECISION demands.

---

## 5. Migration: under and through

What to cut first, what survives, in dependency order.

### 5.1 Survives unchanged (the keepers, re-anchored)

- `CapabilitySet` slot allocation + `attenuate*` monotone narrowing
  (`capability.rs`) — becomes the *cache layer* over the CDT, not the
  source of truth, but the code is the keeper.
- `EffectMask` facet lattice (`facet.rs`) — survives, *gains* an seL4-rights
  projection (Section 3.2 req 3).
- `WitnessedReceipt` (`witnessed_receipt.rs`) — the persistence model; the
  membrane's output.
- `LinearityClass` exhaustive no-default match (`action.rs:698`) — survives;
  see the tension in 7.1 (it is *not* naturally a cap exercise).
- `CellLifecycle` terminal objects (`lifecycle.rs`) — survives.
- `FieldVisibility` selective disclosure (`cell/src/state.rs`) — survives.
- Sturdy-refs + handoff certs (`captp/`) — survive as the reflect-OUT form;
  the `SwissTable` storage moves into a cell.
- Blocklace causal logs + union-merge (`blocklace/`) — survive as the CDT's
  backing store.

### 5.2 Cut first (the inert / double-life machinery)

1. **`DelegationMode::ParentsOwn` and `::Inherit`** (`action.rs:646-652`) —
   admitted no-ops. Cut immediately; the CDT *is* delegation. Keep
   `SnapshotRefresh`, rename toward Fork.
2. **The `CallForest` tree** — the audit found it "enforcement-inert
   (delegation modes unenforced) → flatten to `Vec<Action>`." Under
   cap-centrism the *CDT* carries the tree structure that mattered; the
   action list is flat.
3. **The 4 separate gates** (Precondition / StateConstraint /
   CapabilityCaveat / `Authorization::Custom`) → collapse into one
   `CaveatSet` on the cap, per the audit.
4. **Executor-side authority checks in `ExerciseViaCapability`**
   (`action.rs:1073`) — replaced by the derivation proof (Section 2). This
   is the *core* of the FIXED DECISION and the highest-value cut.
5. **The `Authorization` 8-variant coproduct as a top-level type**
   (`action.rs:206`) — demote to root-seal kinds + caveat-discharge kinds
   (Section 1.2). This is the largest and *riskiest* cut; stage it last
   among the structural changes (see 7.2).

### 5.3 Order of operations

1. Introduce `Cap{root, target, authority, facet, caveats, parent, delta}`
   + `CapHash` as the content-addressed identity, *alongside* the existing
   `CapabilityRef` (make `CapabilityRef` a projection/cache of a `Cap`).
2. Move `SwissTable` and the revocation/nullifier sets into cells (the
   "SETS should be CELLS" collapse). Now the CDT has a home.
3. Lift the attenuation predicate into the AIR (the derivation-proof
   circuit). Begin with `ExerciseViaCapability` only; prove its path.
4. Migrate the 4 gates into `CaveatSet`; the AIR discharges caveats per
   edge.
5. Generalize `SnapshotRefresh` → Fork/branch/merge with the
   attenuation-validity merge rule.
6. Make finality a commit-cap caveat (pluggable).
7. *Last:* dissolve the `Authorization` coproduct into root-seal kinds.
8. Add the `RootSeal::Sel4Reflected` summand + the rbg `badge ↔ CapHash`
   table. (Additive; the seam is greenfield, so it lands without
   disturbing the above.)

The principle: **the CDT must exist as real backing store (steps 1–2)
before the proof can attest paths in it (step 3).** Everything else hangs
off those two.

---

## 6. (deferred to its own section because it is the point) — see Section 7.

---

## 7. CONSTRAINTS & TENSIONS — where cap-centrism strains, gets awkward, or is wrong

This is the section the user actually wants. I will argue *against* my own
anchor.

### 7.1 Conservation and set-membership are not capability exercises

This is the deepest strain. **Value conservation** (`Effect::Transfer`,
`balance_change` summing to zero, `LinearityClass::Conservative` at
`action.rs:698`) is a property *of a turn as a whole*, not of any single cap
exercise. "I am authorized to move 5 from A to B" is a cap exercise; "the
total in the system is unchanged" is a **global invariant over the
multiset of effects**, orthogonal to who was authorized to do what. You can
hold a perfectly valid CDT path to a `Transfer` cap and still violate
conservation (if the paired sibling is absent). Cap-centrism has *nothing
to say* about this; conservation must ride *alongside* the cap layer as a
co-equal, not a servant.

The honest read: **the FIXED DECISION lists FOUR things every turn proves —
authorization + full effect semantics + state-constraints + conservation.**
Cap-centrism nails *authorization* (Section 2 is genuinely native) and
*effect⊆facet* and *state-constraints-as-caveats*. But **conservation is a
fourth thing that the cap lens cannot absorb without distortion.** Trying to
model conservation as "a caveat on a cap" is exactly the kind of
over-abstraction in 7.2 — you'd be smuggling a global accounting invariant
into a local authority check. `LinearityClass` *survives* the migration
(5.1) precisely because it is *not* reducible to the cap vocabulary. This is
the single strongest piece of evidence that capability is **one faithful
layer, not the universal spine.**

**Set-membership** (nullifier non-membership, authorized-sender membership)
is subtler. The audit says these sets "should be CELLS," and indeed if a
nullifier set is a cell then "this nullifier is unspent" is "a witnessed
predicate over the set-cell's state" — a *caveat*, which *is* cap-shaped.
So set-membership reflects into the cap lens more comfortably than
conservation does. But there's a catch: nullifier *insertion* must be
**exactly-once across all concurrent exercises**, which is a consensus
property (7.4), not an authority property. The cap licenses *attempting* the
spend; only consensus decides *who won the race*. So even here the cap layer
covers the "may I try" but not the "did I win" — half the problem.

### 7.2 The "everything is a file" risk — does cap-everything over-abstract?

The user's sharpest prompt: does making everything a capability over-abstract
the way "everything is a file" did in Unix? **I think the danger is real and
I'll name where.**

"Everything is a file" worked for streams and failed for everything with a
*shape* — sockets needed `ioctl`, processes needed `/proc`, async needed
`select`. The failure mode: forcing a rich typed interaction through a thin
universal pipe, then re-introducing the lost structure as out-of-band
escape hatches (`ioctl` is where "file" goes to die).

The cap-centric analogue: **if every interaction must be phrased as "exercise
a cap with a facet and caveats," then interactions with rich internal
structure get flattened into opaque caveats — and the caveat
(`WitnessedPredicate`) becomes the `ioctl` of dregg.** Watch for it: the
moment we find ourselves writing `Caveat::Custom(arbitrary_bytes)` for
conservation, for schema migration, for ordering — that is the
"everything is a file" failure recurring. The `WitnessedPredicate::Custom`
escape hatch (already present) is precisely the pressure-release valve that
*looks* like it preserves the abstraction while actually abandoning it.

Mitigation, and honest limit: the abstraction holds **only for things that
are genuinely "authority to do X."** It should *not* be stretched over (a)
conservation (7.1), (b) global ordering/serialization (7.6), (c) schema
identity (7.5). The discipline must be: **a small, closed set of caveat
*kinds* (expiry, predicate, rate, facet) — and `Custom` is a code smell, not
a feature.** If the rebuild ends with a thriving `Caveat::Custom` ecosystem,
cap-centrism has over-abstracted and we've rebuilt `ioctl`.

### 7.3 Revocation vs. consensus vs. local-first — the irreducible conflict

Revocation needs *agreement*: a revoked cap must stop licensing exercises
*everywhere*. But local-first means a partitioned strand (a phone in
airplane mode) **cannot learn about a revocation** and will keep honoring
the cap. This is not a bug to fix; it is a **theorem** (you cannot have
immediate global revocation without immediate global consensus, and
local-first explicitly forgoes the latter). The cap lens does not escape it
— it *inherits* it from `SnapshotRefresh`'s admitted "revocation is
eventual, bounded by max_staleness" (`action.rs:653`).

The cap-centric framing makes the tradeoff *explicit and tunable* rather
than hidden, which is the best available outcome:

- **Expiry caveats** (already on every cap, `capability.rs:56`) bound the
  blast radius: a cap that expires at height H is auto-revoked everywhere
  that agrees on H, no gossip needed. **Prefer short expiry + renewal over
  revocation.** This is the local-first-correct posture.
- **Revocation = a tombstone edge in the CDT cell**, which propagates at
  gossip speed and achieves finality at the finality-caveat's pace (7.4).
  Between revocation and stability, the cap is in a *known-uncertain*
  window. Exercises in that window are valid-but-revocable; the membrane
  receipt records "exercised at staleness S," so a later reconciler can
  *detect and compensate* (not prevent) a revoked-cap exercise.
- The honest admission: **there is no clean answer.** Either you accept a
  revocation window (local-first) or you accept that every exercise blocks
  on consensus (not local-first). Cap-centrism does not dissolve this — it
  *surfaces* it as the expiry-vs-revocation knob and refuses to pretend
  revocation is instant. Any lens that *claims* clean revocation under
  local-first is lying.

### 7.4 Ordering / concurrency of cap exercises across partitioned strands

Two strands, partitioned, both hold a cap that grants "spend note N" or
"transfer the last 5 computrons." Both exercise it; both produce valid
derivation proofs. **The proofs are individually correct and jointly
inconsistent.** The cap layer authorizes *both* — authority is not
mutual exclusion. Resolving the double-spend is a *consensus/ordering*
problem the cap lens is structurally blind to (same shape as 7.1's "may I
try vs. did I win").

This is where union-merge CRDT semantics (`blocklace/`) do the real work,
*underneath* the cap layer, and it's why I keep saying consensus is a *peer*
of the cap layer at the contended-resource boundary, not a servant. The cap
lens can *tag* an exercise as "linear/exactly-once" (the facet says so) but
it cannot *enforce* exactly-once across a partition. Enforcement is the
finality mechanism's job. **Cap-centrism gets concurrency wrong if it claims
to own it; it's correct only if it explicitly delegates contention to the
consensus layer.**

### 7.5 Data / schema evolution under a cap lens

A cap's facet names an *interface* (`allowed_effects` bits today). When a
cell's interface *evolves* — a new method, a changed state layout — what
happens to the millions of outstanding caps whose facet was minted against
the old interface? Two bad options: (a) old caps silently gain/lose meaning
as bit positions shift (catastrophic — authority is not stable), or (b)
every schema change invalidates all derived caps (revocation storm, 7.3).

The cap lens has **no native story for schema evolution**, and this is a
genuine gap. The "code+data one versioned history" houyhnhnm goal *helps*
(the schema version is in the same history as the caps), but it forces a
constraint the current model lacks: **the facet must name interface elements
by stable content-address, not by bit position.** The current `EffectMask`
(`facet.rs`, bit-positional) is *exactly the fragile design* — bit 7 means
`SET_PERMISSIONS` forever, fine for a fixed effect set, but it does not
generalize to per-cell evolving interfaces. Reflecting onto seL4 (whose
rights bits are *also* fixed and few, 3.2) actually *rescues* this for the
kernel-rights subset but leaves dregg-specific interface evolution
unsolved. **This is the cap lens's weakest area and I will not pretend
otherwise.**

### 7.6 The seL4 lattice-alignment tax, restated as a tension

Section 3.2 req 3 is not free. seL4 has ~4 rights bits and 64-bit badges;
dregg has 18+ facet bits, 256-bit hashes, and rich witnessed-predicate
caveats. **Most of the dregg cap's expressiveness has no seL4 counterpart.**
A reflected-OUT cap must either (a) lose its caveats at the kernel boundary
(the kernel can't evaluate a `WitnessedPredicate`), or (b) keep them
"above" the kernel in a dregg shim that the kernel cap merely gates. Option
(b) is correct but means **the seL4 reflection is lossy in one direction:
kernel→dregg is faithful (kernel rights ⊂ dregg facets), dregg→kernel
projects away everything richer than rights bits.** The clean primitive of
Section 3 is clean *only for the rights-bit core*; the caveat-rich part of
dregg caps lives in user space on the Robigalia side regardless. That's
probably fine — but it means "seL4 caps reflect into dregg caps" is a
*partial* functor, not an isomorphism, and the rebuild should document the
non-reflected residue rather than imply parity.

### 7.7 Ordering of this section's tensions, ranked by severity

1. **Conservation is not a cap exercise (7.1)** — fatal to "spine"; merely
   a wrinkle for "faithful layer." This is the decisive one.
2. **Schema/interface evolution (7.5)** — no native story; forces a
   content-addressed facet redesign.
3. **Revocation vs. local-first (7.3)** and **concurrency (7.4)** — not
   *wrong*, but the cap layer must explicitly cede them to consensus;
   pretending otherwise is the danger.
4. **Over-abstraction / `Custom` as `ioctl` (7.2)** — a discipline risk,
   manageable if `Custom` is treated as a smell.
5. **seL4 lossy projection (7.6)** — acceptable, document the residue.

---

## 8. Conclusions

### 8.a The minimal primitive set under this lens

If capability is the spine, the irreducible set is:

1. **`Cap`** = `{root: RootSeal, target: CellRef, authority: AuthorityClass,
   facet: Interface, caveats: CaveatSet, parent: Option<CapHash>, delta:
   Attenuation}`, identified by `CapHash = H(canonical(Cap))`.
2. **`RootSeal`** = sum of `{CellMint, KeySeal, Sel4Reflected, SwissSeal}` —
   the unforgeable origins. (Auth modes collapse into here.)
3. **`Attenuation`** = the single monotone narrowing operation (facet
   subset ∧ authority ≤ ∧ caveats superset ∧ expiry ≤), versioned by
   `CapLatticeVersion`. *This is the one rule the whole system rests on.*
4. **`CaveatSet`** = a *small closed* set `{Expiry, Predicate(Witnessed),
   Rate, Finality}` — with `Custom` deliberately excluded/quarantined.
5. **The CDT** = the append-only, content-addressed partial order of
   `(parent → child)` attenuation edges; backed by the blocklace; *the same
   structure as the strand log*.
6. **`DerivationProof`** = the proof that a turn's exercises are values of
   `eval` on genuine CDT arrows, with every edge a legal attenuation and
   every caveat discharged. (This is "proof is truth," native.)
7. **The membrane** = a cap at an I/O boundary that emits a
   `WitnessedReceipt`.

…**plus two things the cap layer must hold as co-equal peers, not
servants:** **(8) conservation / `LinearityClass`** (a global per-turn
invariant the cap lens cannot absorb — 7.1) and **(9) the consensus /
finality mechanism** that resolves contention and revocation across
partitions (7.3, 7.4). `CellLifecycle`, `FieldVisibility`, and
`WitnessedReceipt` survive as cell-layer keepers underneath.

### 8.b Honest verdict — spine, or one faithful layer?

**Capability-as-spine is the right organizing principle for *authority*, and
authority is a larger fraction of the system than the current architecture
admits — large enough that promoting the cap layer to primary is the correct
rebuild move.** The single most valuable thing it buys is that "proof is
truth" stops being a bolted-on conjunct and becomes the *subject* of the
proof: an exercise is the traversal of an authorized CDT arrow, and the
derivation proof attests exactly that (Section 2). That is genuinely native
here in a way no other lens can match, and it directly closes the FIXED
DECISION's central indictment (auth-in-plain-Rust, executor-as-authority).
The seL4 seam, fork-as-cap-scoped-sandbox, governance-as-mint-policy, and
finality-as-caveat are real, clean wins that fall out almost for free.

**But it is not the universal spine, and the honest word is "primary, not
total."** Conservation (7.1) is a global invariant the cap vocabulary cannot
express without the `Custom`-caveat over-abstraction that would rebuild
`ioctl` (7.2); ordering/exactly-once across partitions (7.4) is a consensus
property the cap layer must explicitly cede; schema evolution (7.5) exposes
a fragile bit-positional facet design with no native fix. The
correct architecture is therefore **a cap *spine* with two load-bearing
*ribs* it does not own — conservation and consensus** — bolted to it as
co-equal invariants. Anyone who tells you a single primitive (caps, or
effects, or predicates) cleanly subsumes all four of {authorization, effect
semantics, state-constraints, conservation} is selling the "everything is a
file" dream a second time. Capability earns the spine because it owns the
*first three* natively and surfaces the fourth's intractability honestly —
which is the most a primitive can do.
