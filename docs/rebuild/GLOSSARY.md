# dregg2 GLOSSARY — the load-bearing vocabulary

> Precise definitions so the terms are unambiguous. Where a term has a *common*
> meaning the design deliberately rejects (e.g. "membrane"), the rejection is stated.
> Citations point at the canonical docs (`dregg2.md`, `dregg2-multicell-privacy.md`,
> `00-synthesis.md`) and code (`file:line`).

### cell
The endpoint object: `(identity, Preserves state, CellProgram)`. Semantically a
**live coalgebra** — a point of the final coalgebra `νF`, `F X = Obs ×
(AdmissibleTurn ⇒ X)` (a Moore/DFA-shaped behaviour functor). The keystone type is
`Cell = νC. µI. StepProof I × (Turn ⇒ C)`: the outer `νC` is the cell's unbounded life
(it never bottoms out *while reachable*); the inner `µI` is the bounded per-turn proof
obligation tree. A cell is the seL4-CNode analog: an endpoint plus a c-list cache of
held `CapHash`es. (`dregg2.md §1.3`, `cand-A`.)

### CellProgram (the coalgebra structure-map / admissibility)
The thing a cell *carries* that **is** the `AdmissibleTurn ⇒ Cell` arrow of
`step : Cell → Obs × (AdmissibleTurn ⇒ Cell)` (`cell/src/program.rs:53`). It does two
jobs together: (1) the **admissibility filter** — which turns are admissible and to
which post-state (`AdmissibleTurn = { t | program.evaluate(old, new(t), ctx) = Ok }`,
so the program *decides the domain of the arrow*); (2) the **effect-semantics** — the
post-state. Shapes: `None` (terminal program — every authorized turn admissible);
`Predicate([c…])` (domain = conjunction of gates); `Cases([{guard,[c…]}…])`
(method-dispatched; **no matching case = default-deny**, `program.rs:1106`);
`Circuit { circuit_hash }` (admissibility = "the turn carries a proof the circuit
accepts"). Content-addressed: a `CellProgram` value *is* a schema/AIR identity.
(`dregg2.md §1.5`.)

### turn
The generator morphism — a bundle of capability *exercises* moving a cell (or a tuple
of cells) from one state to the next; the seL4-invocation (`Call`/`Send`) analog; and
**the rollback handler** (it holds outgoing effects until commit; commit = replay the
held list + advance the `▶` step + emit the witness at a boundary; abort = discard =
conservation-preserving refund). (`dregg2.md §1.1, §4`.)

### JointTurn (the multi-cell equalizer = Mina's account-update forest)
A turn over cells `C₁…Cₙ`, reified as the **equalizer / pullback object** the category
demands — structurally **Mina's `Zkapp_command` forest** re-grounded. Joint validity =
three bound parts: (1) a **shared turn-identity** every per-cell step-proof commits to
in its PI (CG-2, the pullback — a cell's proof is valid *only* as part of this
JointTurn, never replayed solo); (2) per-cell step-proofs; (3) the **cross-cell
conservation-over-commitments** N-lateral aggregate (CG-5). Atomicity is a **proof
property** (Mina's prophecy `will_succeed` + in-circuit cumulative AND), not a live
2PC coordinator. **`νF₁⊗νF₂` is NOT final ⇒ cross-cell soundness is irreducible to
per-cell**: the CG-2⊗CG-5 binding is an explicit **hypothesis**, never derived from
`per-cell-sound ∧ per-cell-sound`. (`dregg2-multicell-privacy.md §1`, `dregg2.md §1.6`.)

### vat-boundary (NOT "membrane")
The trust-root crossing seam: the kernel↔network seam where caps↔keys convert and the
witness side of `Predicate ⊣ Witness` becomes mandatory. **Reject "membrane" for this**:
Miller's *membrane* is narrowly a transitively-applied **revocable forwarder** (a
pattern, not a trust boundary) — reserve "membrane" for that revocable-forwarder pattern
dregg may add separately. A turn composing *purely within one trust-root* needs no
witness; *crossing a vat-boundary* is exactly where the witness becomes mandatory.
(`discoveries §2a/§3.1`, `00-synthesis §2`.)

### caps-as-caps vs keys-as-caps
**caps-as-caps**: positional, mediator-enforced authority, unforgeable *by construction*
(seL4 CDT slots, a live CapTP session, a trusted host interior) — possession of the slot
*is* authority, no secret. Survives only on **mediator islands**. **keys-as-caps**:
epistemic, crypto-unforgeable, *freely copyable* authority — knowing a key / holding a
derivation proof *is* authority. Demoting the executor to a cache (proof-is-truth)
removes the mediator ⇒ authority must become epistemic. The vat-boundary is the
**principled-lossy** caps↔keys conversion point: `ρ_out` drops Miller's Property F
(confinement) + Property E (revocable forwarders) — a named, exact loss
(`Positional.lean::lossy_attenuation_only`); a key may only narrow. (`00-synthesis §2.2`,
`dregg2.md §3`.)

### the keys-as-caps token layer (biscuit / macaroon / discharge)
The concrete carriers of keys-as-caps at/beyond the boundary
(`Authorization::Token { encoded, key_ref, discharges }`, `turn/src/action.rs:422`):
- **biscuit** (`eb2_…`, `BiscuitIssuer`) = **cross-vat**: Ed25519 public-key, offline-
  verifiable by anyone (UCAN-class, DID-rooted attenuation chain). The biscuit
  delegation graph **≡** the distributed CDT. This is what an `Obs` badge wears off-vat.
- **macaroon** (`em2_…`, `CellScopedMacaroon`) = **intra-vat**: cell-scoped HMAC
  convenience inside one trust-root — never cross-domain (HMAC ≠ third-party-verifiable).
- **discharge**: a 3rd-party caveat `cav@Loc⟨cId,vId⟩` is a turn that cannot become
  admissible until a named **gateway** resolves it; the discharge token is the
  resolution; `bindForRequest = H(M'.sig :: M.sig)` is the binding-site (isomorphic to
  `ConditionalTurn`). Discharge is the **authority-face of the await engine**.
(`dregg2.md §3`.)

### WitnessedCondition (binding-site + engine)
The universal gate that the four cell-side gates collapse to. Two parts: a **binding**
`BindingSite { when: block_height, input: AuthRequest-facts, signed_by }` + an **engine**
selecting *how* it is satisfied: **Datalog** (logic-eval, biscuit/macaroon) | **STARK**
(`WitnessedPredicate` proof-verify, STARK/Merkle registry) | **Await** (deferred
resolution, the continuation family). A gate is satisfied by logic, by proof, or by
awaiting a resolution. (`00-synthesis §3.1`.)

### the await family (algebraic-effects + linear continuations; turn = rollback handler)
A suspended morphism awaiting a predicate-satisfying resolution. Continuations are the
**one** effect that is *not* algebraic (Plotkin-Power), so the substrate is **two layers**:
a gate-engine (algebraic handler / `Verify`) + a delimited continuation-capture
primitive. **The turn IS the rollback handler** (held-until-commit list). **One-shot is
STATIC conservation typing** on the zkpromise (linear continuation ⇒ conservation falls
out as a corollary), not a runtime check. One `Await`/`Resolver` inductive
(`named | gateway | ∃P | registry`); four faces:

| Face | Resolver | Direction |
|---|---|---|
| zkpromise / zkawait | specified party | forward, point-to-point |
| discharge (3rd-party caveat) | named gateway | forward (the universal-gate `Await` engine) |
| intent | *any* filler satisfying P (∃) | **inverse** vat-boundary (gates the missing half) |
| settled-call return | the callee's advanced `Obs` | **backward** (the return projection) |

VERIFY a fill = tractable; FIND a fill = undecidable (`HOU ⪯ GeneralMatch`); the matcher
is a bounded, untrusted, soundness-only plugin. (`dregg2.md §4`.)

### the three orthogonal judgements (conservation / ordering / I-confluence)
Every turn carries **three independent judgements** — not "two laws":
- **conservation** (Law 1, linearity): `Σ_k` is a **monoid-hom `(Turns,∘) → (ℕ,+)` +
  invariance** on ordinary turns (constant on every non-mint/burn hom-set; mint/burn are
  the only generators that move the count). Conservation = withholding the cartesian copy
  `Δ` / erase `◇`. *(The "strong monoidal functor" packaging is decorative — the
  monoid-hom + invariance is load-bearing.)* (`dregg2.md §2.1`.)
- **ordering** (Law 2, session/canonicity): which valid history is *the* history — a
  per-cell **pluggable finality tier** on one DAG (not in any proof). (`dregg2.md §2.2`.)
- **I-confluence** (invariant-merge): do concurrent writes merge invariant-safely
  (`I(x) ∧ I(y) ⇒ I(x ⊔ y)`)? A BEC analysis over `write-set × cell-state-lattice`. It is
  **independent** of the other two and is **NOT the session type**: linear ⇏ I-confluent
  (two pool withdrawals), I-confluent ⇏ linear (a monotone counter); it reduces from
  consensus, so it is a distributed-agreement obligation, not a typing one. Gates tier-1
  eligibility and the cross-group fast path. (`dregg2.md §2.3`,
  `dregg2-multicell-privacy.md §6`, `study-choreography`.)

### finality tiers
The pluggable ordering menu on one DAG (a join-semilattice CvRDT): **(1) Causal-only/CRDT**
(n≥1, never blocks); **(2) Ack-threshold** (k-of-m, no leader); **(3) Cordial-Miners
τ-BFT** (n≥3, stalls then resumes after GST); **(4) Constitutional** (τ-BFT + self-amending
`(P,σ,Δ)`). A turn commits at the **join** of its written cells' tiers; no finalized value
downgrades; conservation is tier-independent. Tier-1 is selectable **only if** the cell's
state is I-confluent (else a static type error). (`dregg2.md §2.2`, `00-synthesis §4`.)

### the coordination / choreography layer (protocol-cell)
*Above* the JointTurn: real multi-round, multi-party coordination is a **global type `G`
(a choreography)** under linear discipline; **projection** `G ↾ p` gives each party its
local protocol and yields progress + deadlock-freedom (the MPST guarantee). Reified as a
**protocol-cell** whose `CellProgram` *is* `G` — a cell coordinating cells (no new
top-level primitive); the await family connects the steps. Privacy-by-projection: party
`p` sees only `G ↾ p`. A protocol whose steps are *all* I-confluent runs fully cross-group
and partition-tolerant; you fall to the blocking atomic mechanism only at the genuine
value-settlement step. (`dregg2-multicell-privacy.md §6`.)

### proof-is-truth / PCA
The B-projection: **soundness is by verification, never by construction; the TCB is the
verifier, never the solver.** Authorization = a proof in a logic the verifier checks
(Proof-Carrying Authorization), not an ACL. Sharper than the over-claiming slogan "proof
is truth" (which over-claims canonicity — ordering is *not* in any proof). dregg2's
novelty = **PCA + IVC**. (`dregg2.md §1.2, §7`, `cand-B`.)

### the badge (= permitted + effects-as-committed, NOT de-facto authority)
The `Obs` artifact a turn returns across a vat-boundary. It attests **(permitted) ∧
(effects-as-committed)** — a legal derivation existed (de-jure) *and* the committed
`Obs`-delta + per-class conservation hold (the value rib). It does **NOT** attest
*de-facto authority* — what the holder can eventually *cause* is recovered behaviorally
from the log, never from the badge (the Miller `BA`-vs-`TP` split). A badge is a
value-bearing transition-attestation, **not a grant of standing**. (`dregg2.md §0, §6b`.)

### Preserves (cell-state / facet / AIR by content-hash)
The data substrate: **identity = hash of a canonical data-model value**. cell-state =
name-keyed `Record @schema #"air-id"`; **facet** = a canonical **Set of effect Symbols**
(adding `transfer` adds an *element*, never shifts a bit position — kills `EffectMask`
fragility); **AIR-id** = `H(canonical(schema_decl))` (kills the frozen/unversioned-AIR
Urbit trap); caps = Embedded (the caps↔keys conversion point). Typed schema-upgrade =
lazy `migrate-on-read`, sound iff **transparent** (lazily-migrated ≡ fresh-at-v2) **AND
conservative** (a DROP over a linear slot emits `Σ before = Σ after + Σ dropped`).
(`dregg2.md §5`.)

### the anti-brick `set_program` / `AIR_VERSION` clause
The #1 missing upgrade safeguard (adopted from Mina `permissions.ml:77`). When dregg2
swaps the recursion backend / AIR encoding, every live `Circuit{circuit_hash}` cell
pinned to the old proof system would become unverifiable — *bricked*. The fix:
`CellProgram`-upgrade carries a **`set_program` admissibility clause** pinning a
proof-system / `AIR_VERSION`; when a cell's pinned version is older than the live
verifier, the upgrade authority **falls back to a signature by the cell's owner** — a
verifier upgrade can never strand a sovereign cell. (`dregg2-multicell-privacy.md §3`.)

---

### supporting terms (quick reference)
- **CDT** — capability-derivation-tree: the primary structural object, content-addressed
  and gossiped; `CDT ≡ strand log ≡ biscuit delegation graph` (one append-only partial
  order, three renderings). **Acyclic.** (`dregg2.md §1.1`.)
- **`⊗` (cross-cell tensor)** — the monoidal product the Core carries; a turn over N cells
  is a morphism on `C₁⊗…⊗Cₙ`, bound by the equalizer (CG-2 ⊗ CG-5). (`dregg2.md §1.6`.)
- **GC / cell-liveness** — codata unfolds forever (`ν`) *unless unreachable*. Two
  mechanisms: acyclic-CDT refcount-to-zero pruning (built) vs cyclic-liveness
  mark-from-roots collection (open — refcounting cannot detect dead cycles).
  (`dregg2.md §1.7`.)
- **StepInv** — `Conservation ∧ Authority ∧ ChainLink ∧ ObsAdvance`; soundness holds iff
  every step attests *all four* in-circuit (a non-contractive step "permits a drifting
  future"). The 6-clause auth conjunct: key → delegation → policy-entailment → effect-fold
  → replay → cell-root-binding. (`dregg2.md §7.1`.)
- **`▶` ("later") guard** — Birkedal's productivity guard, typed off
  `previous_receipt_hash`; buys productivity, not soundness (step-completeness buys
  soundness). (`Boundary.lean`.)
- **`Sound` / `IsBisim` / `sound_of_step_complete`** — soundness = a `▶`-guarded
  bisimulation to the Lean golden-oracle spec; `sound_of_step_complete` is the keystone
  theorem. (`Boundary.lean`.)
- **RecursionBackend** — the swappable trait (`MAX_DEPTH: Option`, `needs_cycle: bool`;
  **never** an `additive_combine` method) behind which IVC recursion lives; recursion is a
  deferrable feature, not on the soundness-critical path. (`dregg2.md §7`, `decisions §3`.)
