# 03 — The Spine Is The Proof

> **Lens / fixed decision:** *Proof is truth.* The morphism-witness is the source
> of truth; the executor is a cache. Cells, capabilities, consensus, and the
> local-first substrate must reorganize **around** the proof, not the other way
> around.
>
> This is a **forward design**, not an audit. Current-state claims are cited
> `file:line` only to keep the design honest about its starting material. The
> back half of the document is deliberately **self-adversarial**: the strongest
> case against this lens is made here, by its own advocate.

---

## 0. The thesis, stated sharply

A *turn* in Dragon's Egg is a morphism: it takes a slice of the world (some cells
in some pre-states, held under some capabilities) and produces a new slice (the
same cells in new post-states, plus emitted effects). Today that morphism is
*executed* by trusted Rust (`turn/src/executor/*`) and *partially* witnessed by a
STARK over the Effect-VM (`circuit/src/effect_vm/air.rs`). The proof is a
second-class citizen: it is generated *after* the executor decides what happened,
and it attests to a strict subset of what the executor actually did
(authorization is entirely outside it — `turn/src/executor/authorize.rs:8`; ~half
the effect semantics are a host commitment the AIR never re-derives —
`circuit/src/effect_vm/air.rs:1097-1125`).

Under this lens we **invert the dependency**. The proof is primary. A turn does
not "happen" and then get proved; a turn **is** the act of producing a proof that
a valid morphism exists. The executor's job shrinks to: *propose a witness, and
maintain a fast materialized view of whatever the latest valid proof attests.* If
the executor and the proof disagree, the executor is wrong, by definition. The
ledger is not the truth; it is a **memo table** of proof outputs.

The discipline this buys: **there is no privileged code path that can mutate
state without a proof.** That is exactly the property the houyhnhnm/Robigalia
vision needs at a boundary — a membrane that emits a proof-carrying receipt is
*self-evidently* a full-abstraction boundary, because nothing crosses it that
isn't attested. seL4 capabilities reflecting into Dragon's Egg capabilities
becomes coherent: an seL4 cap-invocation produces (or is wrapped by) a witness,
and the witness is the only thing the rest of the system trusts.

That is the promise. The rest of this document is about whether it survives
contact with cost, concurrency, and consensus. (Spoiler from §10: the spine
holds for **validity**; it does **not** subsume **ordering**, and pretending
otherwise is the characteristic failure mode of this lens.)

---

## 1. What a complete turn proof must attest

The current proof attests an **effect-transition**: *given* a declared
`OLD_COMMIT` and a *host-asserted* `EFFECTS_HASH`, there exists a row-consistent
trace whose arithmetic is valid and whose recomputed `NEW_COMMIT` matches
(`circuit/src/effect_vm/pi.rs:15-25`). Four things are missing for "proof is
truth," in severity order. A **complete turn proof** must close all four.

### 1.1 Authorization — the actor was *permitted*, in-circuit (the biggest gap)

Today `verify_authorization` is plain Rust (`turn/src/executor/authorize.rs:8`),
handling signature / proof / bearer-cap / captp paths. Under this lens **none of
that is truth** — it's an executor opinion. The proof must attest an
**unforgeable derivation chain** from a root authority to the specific action.

A complete turn proof must witness, in-circuit:

1. **Root binding.** Some PI-exposed root authority commitment (a cell's owner
   key, a genesis cap root, or — in the Robigalia future — a reflected seL4
   cap-handle hash) is the head of the chain.
2. **Delegation steps.** Each delegation/attenuation in the c-list is a real
   cryptographic step: a Schnorr/Ed25519 signature over the child cap by the
   parent (we already have `circuit/src/schnorr_air.rs`,
   `circuit/src/native_signature.rs`), *plus* the attenuation predicate (the
   child's authority ⊆ parent's authority).
3. **Caveat discharge.** Every caveat on every cap in the chain is **evaluated
   inside the circuit** against the turn's witnessed context (this is the
   `verify_slot_caveat_manifest` logic — currently in TESTS only, not the
   standalone verifier; see §1.3).
4. **Action ⊆ leaf authority.** The action actually performed is within the
   authority of the chain's leaf.

The output is a single PI field, `AUTH_OK` is *not enough* — `AUTH_OK` is a
boolean the prover could just set. Instead we expose **`AUTH_ROOT`** (the root
authority commitment) and **`ACTION_AUTHORITY_DIGEST`** (a commitment to *what
action against what cell under what attenuation* the chain authorizes). The
verifier binds `AUTH_ROOT` to a known root and binds `ACTION_AUTHORITY_DIGEST` to
the canonical action — and the *only* way the prover can produce a valid trace
for that pair is to actually possess the signatures.

### 1.2 Full effect semantics — an in-circuit effects-fold, not a host commitment

Today `EFFECTS_HASH` is a host commitment the AIR never re-derives
(`compute_effects_hash` is never called inside the evaluator), so Custom effects
and ~half the variants are "state-columns-didn't-move" only — *the prover can
claim arbitrary side-effects occurred* (`air.rs:1120`). The Effect-VM does have
real teeth for Transfer/SetField/GrantCap/etc. (`circuit/src/effect_vm/effect.rs`,
`trace.rs`, the per-effect constraint groups in `air.rs`), and it recomputes the
state commitment — that part is **a keeper**.

Under this lens the rule is absolute: **every effect's contribution to
`EFFECTS_HASH` is recomputed *inside* the circuit from the effect's own witnessed
parameters, and every effect's state mutation is constrained.** No effect gets a
"state passthrough + trust the host hash" exemption.

- The effects-fold becomes a **rolling Poseidon2 absorb over the canonical-DFS
  effect stream** (the `EFFECTS_HASH_GLOBAL` slot at `pi.rs:92` already names the
  ambition: "canonical-DFS-order traversal of the whole call_forest's effects").
  Under this lens that rolling hash is computed *by the AIR per row*, not asserted
  by the executor and matched cross-PI.
- **Custom effects** are the hard case and the lens forces the right answer:
  a Custom effect is *not* truth unless its CellProgram's own proof is verified.
  The "verifier MUST independently verify" caveat at `air.rs:1109` is exactly the
  classical-PI-matching hole. Under "proof is truth," the Custom-effect
  constraint must be a **recursive verification** of the CellProgram's proof
  against the committed program VK (see §2.3). There is no honest middle ground:
  either the sub-proof is verified in-circuit, or the Custom effect is a hole.

### 1.3 State-constraints, range, and field totality

Slot-caveat / state-constraint checks and range proofs are executor-side
(`verify_slot_caveat_manifest` lives in `tests/`, not the standalone verifier),
and the projection truncates 32-byte fields to 4 bytes — a soundness hole where
two distinct field values collide. Under this lens:

- The **constraint-AIR** evaluates the cell's declared state-constraint manifest
  against the *full-width* witnessed pre/post field values.
- Field projection is **full 32-byte → 4×felt (or more)**, not truncation. The
  Stage-1 widening to 4-felt commitments (`pi.rs:1-13`) is the right direction;
  this lens demands it be the *floor*, applied to every field that a constraint
  reads, with the trace columns widened to match (the `AUDIT[stage1-trace-widen]`
  note at `pi.rs:10` flags exactly the gap to close).

### 1.4 Conservation — LinearityClass enforced as a global constraint

`LinearityClass` is a keeper. The proof must attest that **linear resources are
neither created nor destroyed across the turn**: Σ(consumed) = Σ(produced) for
each linear class, and affine resources are used ≤ once. Today there's a
`net_delta` balance binding (`pi.rs:50-52`) — that's conservation for the *one*
balance scalar. The lens generalizes it: conservation is a **per-class sum-check**
over the witnessed effect stream, with the class taxonomy (linear / affine /
relevant / unrestricted) exposed so the verifier knows *which* discipline each
resource was held to.

### 1.5 Binding to canonical turn identity

The proof must be bound to **this** turn, not merely *some* valid turn. The
existing turn-identity PI block is the right skeleton: `TURN_HASH` (`pi.rs:86`),
`ACTOR_NONCE` (`pi.rs:99`), `PREVIOUS_RECEIPT_HASH` (`pi.rs:103`). Under this lens
these are not optional cross-checks — they are the **anti-malleability spine**
(see §10.5, the "right proof for THIS turn" tension). A complete turn proof's PI
must pin: the canonical `Turn::hash`, the actor nonce (monotone), the previous
receipt hash (chain position), and the AIR version (§2.4).

### 1.6 The public-input surface (what's public vs. witness)

**Public (the proof's external interface — the "badge"):**

| Field | Meaning |
|---|---|
| `AIR_VERSION` | typed AIR-shape version (§2.4) — *the* anti-Urbit-trap field |
| `OLD_COMMIT` (4 felt) | pre-state commitment(s) of touched cells |
| `NEW_COMMIT` (4 felt) | post-state commitment(s) |
| `EFFECTS_HASH` (4 felt) | **re-derived in-circuit** rolling fold over the effect stream |
| `AUTH_ROOT` | root authority the derivation chain descends from |
| `ACTION_AUTHORITY_DIGEST` | what-action-against-what-cell-under-what-attenuation |
| `CONSERVATION_VECTOR` | per-LinearityClass net-delta = 0 witness |
| `TURN_HASH` / `ACTOR_NONCE` / `PREVIOUS_RECEIPT_HASH` | canonical identity binding |
| `CONSTRAINT_MANIFEST_HASH` | which state-constraint set was enforced |

**Witness (private):** the trace itself; all signatures and delegation
secrets; the full-width field values; the per-effect parameters; the
intermediate fold states; the caveat-evaluation context. ZK (§4) decides
*which* of these are actually *hidden* vs. merely *not-exposed-but-derivable*.

The design rule: **the PI surface is the entire trust boundary.** If a verifier
who knows only the PI cannot reject a forged history, the field is in the wrong
place.

---

## 2. AIR / recursion architecture

We must compose **four** statements — auth, effect-semantics, constraints,
conservation — into **one** verifiable statement per turn, then compose turns
into strands. Today composition is **classical PI-matching** (the verifier checks
N independent proofs share PI values; `sdk/src/full_turn_proof.rs:429`,
`verify_proof_carrying_turn_bundle` style), which is *sound* but not *recursive*
and not *succinct in N*. The lens wants recursion where it buys real properties.

### 2.1 Per-turn composition: chip-style multi-AIR, shared bus

Within one turn, the four AIRs are not independent statements glued by the
verifier — they are **chips in one proof** sharing a **logical bus** (lookup /
permutation argument):

```
        ┌─────────────────────────────────────────────┐
        │              ONE TURN PROOF                   │
        │                                               │
        │  [auth-AIR] ──┐                               │
        │  [effect-AIR]─┼─ shared bus (Poseidon2 +     │
        │  [constr-AIR]─┤   logup): effect stream,      │
        │  [conserv-AIR]┘   field values, cap-chain,    │
        │                   turn-identity               │
        │                                               │
        │  PI = §1.6 surface                            │
        └─────────────────────────────────────────────┘
```

The bus is what makes the four chips *one truth* instead of four: the same
effect-stream rows that the effect-AIR folds into `EFFECTS_HASH` are the rows the
conservation-AIR sums; the same cap-chain rows the auth-AIR validates are the rows
the constraint-AIR reads caveats from. **Classical cross-PI matching is replaced
by an in-proof lookup argument** within a turn. This is the first place recursion
(or at least a shared-commitment argument) earns its keep.

### 2.2 Cross-cell, within a turn: aggregation micro-AIR (not cross-PI)

A turn touches N cells. Today each cell gets its own proof and the executor's
loop checks they agree on `TURN_HASH`/`ACTOR_NONCE`/bilateral roots
(`pi.rs:106-120` — the γ.2 bilateral binding is literally "the verifier rejects
any per-cell PI that doesn't match the schedule-derived expectation"). That's the
executor reconstructing truth off-circuit. Under this lens, the merge of N per-cell
`EFFECTS_HASH` into `EFFECTS_HASH_GLOBAL` is an **aggregation micro-AIR** that
*recursively verifies* the N per-cell proofs and folds their public effect-roots
— the work the `pi.rs:79-81` comment defers ("γ.1 elevates the
effects_hash_global → Σ effects_local merge to an aggregation micro-AIR"). Make
that the **base** behavior, not a deferred elevation.

### 2.3 Custom effects and sub-proofs: `FriVerifierGadget` in-circuit

The recursion primitive exists: `circuit/src/stark_zk.rs` —
`RecursiveFriAir`/`FriVerifierGadget` (the W3-A recursion teeth,
`stark_zk.rs:240-452`). The Custom-effect hole (§1.2) is closed by **running the
FRI verifier gadget over the CellProgram's sub-proof inside the turn AIR**, bound
to the committed program VK. This is the canonical place classical PI-matching
*must* become real recursion: a Custom effect's truth is *its sub-proof's* truth,
and the only honest way to inherit that is to verify it in-circuit.

### 2.4 Versioning: `AIR_VERSION` in PI — escaping the Urbit trap

The Effect-VM AIR is **frozen and unversioned** — `AirVersion` is not in the
public inputs. This is the **u3 trap**: a fixed low-level VM whose real semantics
leak into the trusted executor, with no upgrade path that a verifier can reason
about. The fix is structural, not cosmetic:

1. **`AIR_VERSION` is a mandatory PI field.** A verifier *selects* its constraint
   system by version; a proof for version *v* is only ever checked against the
   constraint set of *v*. No silent reinterpretation.
2. **Typed AIR-shape upgrades.** An AIR version is a *typed shape* (column
   layout + PI layout + constraint set) with an explicit, *provable* migration
   relation to the next: `migrate: Shape_v → Shape_{v+1}` is itself a statement
   ("every state valid under v maps to a state valid under v+1"). This is the
   houyhnhnm "code+data one versioned history" principle applied to the *prover*:
   the constraint system is data, versioned, with provable migrations.
3. **No effect-semantics in the executor that isn't in *some* AIR version.** The
   anti-trap invariant: if the executor can do it, an AIR version proves it. The
   moment a capability exists only in Rust, we've rebuilt u3.

The deep point: the frozen-AIR trap and the proof-is-truth lens are the **same
issue from two sides.** "Proof is truth" *requires* that nothing escapes into the
executor; an unversioned frozen AIR *guarantees* things escape (because you can't
extend the proof, so you extend the executor). Versioning isn't a feature — it's
the precondition for the lens to be honest over time.

### 2.5 Strand-level: IVC over a chain of turns

A strand is a causal chain of turns. `circuit/src/ivc.rs` exists but is a **hash
chain, not real recursion** — "without the real recursion backend, the IVC is
implemented as a HASH CHAIN" (`ivc.rs:30`), where each step's `AccumulatedProof`
carries "the constraint proof of the most recent fold step" but **not** a
recursive proof covering all prior steps (`ivc.rs:80-85`). Under this lens the
strand head is a **single constant-size recursive proof** attesting: *this
post-state is the result of a valid chain of turns from genesis, each
authorized, each conservation-respecting.* `RecursiveFriAir` is the swap-in;
`ivc.rs`'s API was "designed so that swapping to real recursion requires no
changes" (`ivc.rs:38`) — good, make the swap the spine.

---

## 3. Reorganizing cells / caps / consensus around the proof

### 3.1 What is a cell?

> A cell is **the equivalence class of all valid proof-chains that agree on its
> current commitment.** Its "state" is `NEW_COMMIT` of the latest turn proof that
> touched it. The materialized bytes in the executor are a **cache** of the
> preimage of that commitment.

`CellLifecycle` and `FieldVisibility` (both keepers) become *attested* properties:
a cell is "sealed"/"active"/"retired" because the latest valid proof says so, not
because an executor flag says so. `FieldVisibility` maps directly to the
public/witness split of §1.6 — a private field is one whose preimage stays in the
witness and never reaches a PI.

This is the houyhnhnm "log IS the inputs, not bytes" principle: a cell's history
is the chain of *turn witnesses* (morphisms), not a chain of byte-diffs. You can
discard the materialized bytes and **re-derive** them by replaying the witnessed
inputs; the proof guarantees the replay is faithful.

### 3.2 Is the ledger just a memo table?

**Yes, and this is the clarifying reframe.** The ledger is a memo table mapping
`turn_id → (proof, NEW_COMMIT)`. It exists for *performance and discovery*, not
for *truth*. A `WitnessedReceipt` (keeper) is one memo-table entry: it is the
proof-carrying receipt a membrane emits. The "badge alongside an LLM tool result"
(the zkRPC goal) **is** a memo-table entry that the recipient can verify without
trusting the ledger that stored it.

But — flagged hard here, expanded in §10.6 — **a memo table has no opinion about
which of two conflicting entries is canonical.** Memoization assumes a function;
divergent forks mean the "function" is relational. The ledger-as-memo-table
framing is exactly where the lens quietly needs an *ordering* primitive it cannot
itself provide.

### 3.3 Local-first strands, fork, merge

Each strand is "a chain of proofs (recursive IVC over a strand)" — the consensus
substrate is already local-first-shaped (per-strand causal logs + CRDT merge +
ReferenceGroup-view). Under this lens:

- **A strand head = a recursive IVC proof** (§2.5). Two friends gossiping over
  Bluetooth exchange *strand heads*; each can verify the other's head **without
  replaying** the other's turns. This is the local-first dream realized: O(1)
  verification of an O(n) history.
- **Fork** is free and *requires no permission*: anyone can extend any verified
  head. Forking produces two valid heads with a common ancestor. **Both are
  "true" as morphisms** — and this is the rub (§10.4).
- **Merge** is where linear logic earns its place. A CRDT merge of two strands is
  itself a turn (a *merge morphism*) that must be **proved**: it takes two
  post-states and produces a reconciled state, and for **linear** resources the
  merge proof must show no double-spend across the fork (Σ consumed across both
  branches ≤ Σ available at the fork point). Unrestricted/CRDT-friendly state
  merges trivially; linear state forces the merge proof to *pick* (or to prove a
  split). **Linear logic is what makes merge a decidable obligation rather than a
  policy choice** — but it makes merge *fail* (provably) when both forks spent the
  same linear resource, which is correct but unpleasant (§10.4).

---

## 4. ZK: hiding vs. succinctness, cost model, porting

"Proof is truth" does **not** imply "proof is private." Most of the value here is
**succinctness + soundness** (small, fast-to-verify, unforgeable). Hiding is a
*separate* property needed only for *some* statements. Today the main path
`stark::prove` is succinct+sound but **not hiding**; the `HidingFriPcs` ZK path is
wired to *one* demo AIR (`circuit/src/stark_zk.rs:130-204`, `prove_zk`/`verify_zk`).

**Which statements need hiding:**

| Statement | Hiding? | Why |
|---|---|---|
| State transition validity | No | `OLD_COMMIT`/`NEW_COMMIT` are already commitments; the *transition* needs soundness, not hiding |
| Conservation | No | The vector being zero is a public claim |
| **Authorization derivation chain** | **Yes** | The whole point of caps is that *who delegated to whom* is private; exposing the chain de-anonymizes (this is what `credentials/` anonymity is about) |
| **Field values behind a private `FieldVisibility`** | **Yes** | Definitionally hidden |
| **Custom effect parameters** | **Maybe** | App-dependent; the sub-proof may itself be ZK |
| Turn identity binding | No | `TURN_HASH` etc. are public anti-malleability anchors |

**Cost model (order-of-magnitude, the honest version):** the dominant cost is
**auth-in-circuit** (each Schnorr/Ed25519 verification is thousands of constraints
over a non-native field) and **recursion** (each `FriVerifierGadget` invocation is
the FRI verifier's hash/Merkle work as a trace). A complete turn proof with a
short cap-chain (depth ≤ 3) + a handful of effects + conservation is **plausibly
seconds on a laptop, tens of seconds on a phone** with today's Plonky3/BabyBear
stack. Deep cap-chains, many Custom sub-proof recursions, or many-cell aggregation
push it to **minutes** — which is the feasibility wall (§10.1).

**Porting the Effect-VM AIR onto a hiding PCS:** the path is to take the existing
Effect-VM AIR and instantiate its config with `HidingFriPcs` (the machinery in
`stark_zk.rs`) instead of the plain FRI PCS — the AIR constraints are unchanged;
only the polynomial commitment gains blinding. The work is (a) ensuring no
constraint leaks witness values into low-degree-testable positions, and (b)
adding blinding rows. This is *mechanical* once the AIR is otherwise complete —
which is why ZK is the *last* thing to do, not the first (§5).

---

## 5. Migration "under and through" — what to cut first

The lens dictates the order: **close the truth-gaps in severity order, exposing
the more-complete prover on the real path, and *delete* the trusted executor
paths as each gap closes.** "Under and through," not "layer upon."

1. **Cut the placeholder-state prover on the MCP path first.** The zkRPC goal
   (verifiable toolcalls) currently uses a *placeholder-state prover*, while the
   more-complete composition lives in `sdk/src/full_turn_proof.rs` and is
   *unexposed* to the toolcall path. **Wire the real prover to the MCP path.**
   This is the highest-leverage cut: it makes the flagship demo *actually* carry
   truth, and it forces every subsequent gap to be visible at the demo surface.
2. **Move authorization into the circuit** (§1.1). The moment `AUTH_ROOT` /
   `ACTION_AUTHORITY_DIGEST` are real PI, **delete `verify_authorization`'s
   trust** (`turn/src/executor/authorize.rs` becomes a *witness builder*, not a
   *decider*). Biggest gap, so it goes early.
3. **Re-derive `EFFECTS_HASH` in-circuit** (§1.2) and remove the host-commitment
   matching. Then **recursively verify Custom sub-proofs** (§2.3). This deletes
   the `air.rs:1097-1125` exemption entirely.
4. **Pull `verify_slot_caveat_manifest` into the standalone verifier as a
   constraint-AIR** (§1.3), and **widen field projection to full-width** (kill
   the 32→4 byte truncation).
5. **Add `AIR_VERSION` to PI and define one migration** (§2.4) — even a trivial
   v1→v1 — so the *mechanism* exists before it's needed.
6. **Swap `ivc.rs`'s hash-chain for `RecursiveFriAir`** (§2.5): strand heads
   become real recursive proofs.
7. **Port to `HidingFriPcs`** for the auth-chain and private fields (§4) — last,
   because hiding over an incomplete statement hides nothing worth hiding.

Each step **removes** trusted Rust. The end state: the executor is a witness
builder + cache, and there is no code path to state mutation that doesn't go
through a proof.

---

## 6. The minimal primitive set under this lens

1. **Witness** — the private input to a morphism (trace + secrets + full-width
   fields). *The log is witnesses, not bytes.*
2. **Turn proof** — a single proof over the four-chip AIR (§2.1) attesting the
   §1 statement, with the §1.6 PI surface.
3. **Commitment** — the typed, full-width (4-felt floor) Poseidon2 commitment to
   a cell state; the cell *is* its commitment.
4. **Capability** — a delegation-chain whose validity is *attested in-circuit*
   (auth-AIR), not checked by the executor. (`LinearityClass` rides here.)
5. **Effect stream** — the canonical-DFS sequence whose in-circuit fold *is*
   `EFFECTS_HASH`.
6. **AIR version** — a typed constraint-system shape with provable migrations.
7. **Recursive accumulator** — `RecursiveFriAir` over (a) cross-cell aggregation
   and (b) strand IVC; the strand head is one constant-size proof.
8. **Receipt** — a `WitnessedReceipt`: the proof + PI, the memo-table entry, the
   membrane's badge.

Everything else (cells, ledgers, gossip, the MCP server) is **derived**: a cache,
a discovery index, or a transport for the above.

---

## 7–9 collapsed into the adversarial section

The constructive design is above. Sections 7–9 of a normal doc (detailed APIs,
column layouts, benchmarks) are deliberately omitted because the *honest* work of
this lens is the next section: where it breaks.

---

## 10. CONSTRAINTS & TENSIONS (self-adversarial)

This is the part the lens's advocate must write, not its critic.

### 10.1 The cost of proving *every* turn's full semantics may be intractable

Auth-in-circuit + in-circuit effects-fold + recursive Custom sub-proofs +
strand-IVC is **heavy**. On a phone (the local-first/Bluetooth-gossip scenario),
a complete turn proof with a non-trivial cap-chain and a Custom sub-proof
recursion is plausibly **tens of seconds to minutes**. That is fatal for any
interactive workload. The lens's clean answer — "everything is a proof" — collides
with physics.

The honest mitigations, none free:
- **Asymmetric prove/verify is the saving grace:** a phone need only *verify*
  gossiped strand heads (milliseconds), and can *defer* or *delegate* proving.
  But delegated proving reintroduces a trusted prover unless the delegate's work
  is itself recursively verified — which adds cost.
- **Batching:** prove M turns as one strand-IVC step amortizes the recursion
  overhead. But batching *delays truth*: between batches, the executor's cache is
  ahead of the latest proof, i.e., **the cache holds un-proven state.** Which is…

### 10.2 …an un-proven fast path that *contradicts the lens*

If anything runs ahead of its proof — a speculative executor, a batch window, an
interactive REPL — then for some interval **state exists that is not yet truth.**
The lens says "the executor is a cache," but a cache that's *ahead* of the truth
is a *write-back cache with dirty pages*, and dirty pages can be wrong. We must
either (a) admit a "provisional" state tier that is explicitly *not* truth (and
then "proof is truth" is really "proof is *eventual* truth"), or (b) refuse all
speculation and eat the latency. There is no third option. **This lens makes
interactivity awkward and is at risk of quietly smuggling in a trusted fast
path.** The defensible stance: provisional state is allowed but **never
gossiped** and **never authorizes a downstream turn** until proved — the proof is
truth *at every boundary crossing*, even if not at every keystroke.

### 10.3 The base case / bootstrapping

Strand-IVC proves "valid chain from genesis." **What proves genesis?** The base
case cannot itself be a turn proof (no prior state). Options: (a) a *trusted
setup* genesis commitment (a trust root — uncomfortable for a "no single kernel"
vision); (b) genesis is a *capability reflected from seL4* (the root authority is
the OS cap, and the OS is the trust base — coherent with Robigalia, but it means
**the proof's trust bottoms out in seL4, not in the proof**); (c) "genesis is
whatever a quorum signed" — which is *consensus*, reappearing at the bottom of the
stack. **There is no proof-only bootstrap.** The lens has a turtles-all-the-way-
down problem and the ground turtle is either a trusted setup or a consensus act.

### 10.4 Two valid proofs over divergent forks — which is true?

This is the deepest crack. Fork is free (§3.3). Alice extends head H to H→A;
Bob extends H to H→B. **Both A and B are valid morphisms — both proofs verify.**
The proof says *nothing* about which is canonical, because validity is a *local*
property and canonicity is a *global* choice. For a linear resource spent in both
A and B, **both proofs are individually sound and jointly contradictory.** The
proof system cannot adjudicate; it can only *detect* the conflict at merge time
(§3.3) and *refuse to merge* (or force a pick). **Proof gives you validity; it
does not give you agreement.**

### 10.5 The "succinct proof exists" vs. "the *right* proof for THIS turn" gap

A prover can produce *a* valid proof of *a* valid turn. Binding it to **this**
canonical turn — this nonce, this previous receipt, this action against this cell
— is what `TURN_HASH`/`ACTOR_NONCE`/`PREVIOUS_RECEIPT_HASH` (§1.5) are for. But
note the subtlety: **the binding fields are themselves public inputs the prover
chooses.** Soundness only forces "the trace is consistent with these PI"; it does
*not* force "these PI are the canonical ones." Canonicity of the *PI themselves*
(is `PREVIOUS_RECEIPT_HASH` really the head of *the* strand?) is **again an
ordering question the proof can't answer.** A malleable prover can produce a valid
proof for a *different but well-formed* turn-identity; only an external notion of
"which receipt-chain is the real one" rejects it. This is §10.4 wearing a
different hat.

### 10.6 Does "proof is truth" smuggle consensus back in? — Yes.

Every crack above (10.3 genesis, 10.4 forks, 10.5 binding) has the same shape:
**proof establishes validity; it cannot establish *which valid history is
canonical*.** "The ledger is a memo table" (§3.2) is only well-defined if there's
agreement on *which* entry is the memo for a given key — and that agreement is
exactly **consensus / ordering**, which the proof does not produce. The current
substrate's "monomorphic finality + NO fork/merge" risk is the symptom: the
existing system avoids the problem by *not allowing forks*, i.e., by having a
single writer / single order. The moment we embrace local-first fork/merge (the
vision), **we need an ordering primitive the proof cannot subsume.**

### 10.7 What this lens gets *wrong* / makes *awkward*

- **Streaming / interactive / external-IO computations.** A turn that talks to a
  live network socket, reads a sensor, or interacts with a human cannot be
  "proved" in the usual sense — the *inputs* are non-deterministic and external.
  The best we get is "proof *given* the witnessed inputs," which pushes the trust
  to "were these the real inputs?" — an *attestation* problem, not a *proof*
  problem. The lens over-promises on anything touching the messy outside.
- **Cost-opaque effects.** Some morphisms (a big sort, an ML inference) are cheap
  to *do* and ruinous to *prove*. The lens has no good answer except "recurse a
  cheaper attestation," which is a downgrade it's supposed to forbid.
- **Debuggability.** When the executor (cache) and the proof disagree, the lens
  says the executor is wrong — but the *human* usually wants to know *why the
  proof rejected*, and a failed STARK is a famously opaque "no." Proof-as-truth
  makes the system **harder to operate**, not easier.

---

## 11. Honest verdict

**Proof-as-truth is a real and powerful spine — for *validity*, and only for
validity.** It can genuinely be the organizing principle for *what a turn is
allowed to be*: the morphism-witness, with authorization, full effect semantics,
state-constraints, and conservation all attested in one versioned, recursive
statement, with the executor demoted to a witness-builder-and-cache. That
inversion is correct, it is buildable on the existing Effect-VM + `schnorr_air` +
`RecursiveFriAir` + IVC parts, and it is exactly the discipline the
houyhnhnm/Robigalia membrane needs. **But it cannot be the *whole* spine, because
a proof certifies that a history is *valid*, never that it is *the* history.**
Forks, genesis, and turn-identity-canonicity all reduce to "which valid thing is
canonical?" — an ordering/agreement question that lives strictly outside the
proof. So the honest architecture is **two coupled spines**: *proof* for validity
(this lens) and a *separate, minimal ordering primitive* (a per-strand causal
order with explicit, proof-checked fork/merge — the local-first substrate, made
fork-aware) for canonicity. Proof is truth; **consensus is which truth.** Build
the proof spine as the primary one — it shrinks the trusted base to almost
nothing and makes the boundary self-evident — but do not let it pretend to
subsume the ordering primitive it structurally cannot.
