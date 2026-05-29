# LEARNINGS — Capability theory & the vat-boundary law

> Axis: **the vat-boundary / membrane law** and the caps-as-caps axioms that
> license it. Read against `docs/rebuild/00-synthesis.md` (esp. §1 categorical
> skeleton, §2 trust-boundary/phase model, §8 metatheory hook) and
> `01-spine-capability.md` (esp. §2 "proof is truth native", §7 tensions).
> Tags: **[paper]** = grounded in a read PDF; **[design]** = my forward proposal.

---

## Papers read (filename — one-line)

- **robust-composition.pdf** — Miller's ocap thesis. The load-bearing chapters
  for this axis: ch.8 (Permission vs Authority + Table 8.1, the CP/EP/BP/TP and
  EA/BA/TA lattice — the BA-vs-TP analysis); ch.9 (object-capability paradigm:
  the four connectivity rules + "only connectivity begets connectivity";
  Redell's caretaker; the **membrane** pattern, which Miller defines *narrowly*);
  ch.14 (the **vat**: near/far references, the **turn** as the unit of
  synchronous mutual-exclusion); ch.5 (defensive correctness vs **defensive
  consistency** — the achievable property).
- **capability-myths-demolished.pdf** — Miller/Yee/Shapiro. The canonical
  **seven properties A–G** distinguishing ACL / caps-as-rows / caps-as-keys /
  object-caps (Fig.13/15). Refutes Equivalence, Confinement, Irrevocability
  myths. The exact caps-vs-keys delta lives in **Property E (composability)**
  and **Property F (access-controlled delegation channels)**.
- **take-grant-protection-model.pdf** — Jones/Lipton/Snyder. `can_share` /
  `can_steal` **decidable in O(|V|+|E|)** via tg-paths / islands / bridges; the
  decidability comes from *restricting the rewrite rules*, vs HRU's undecidable
  general matrix. Plus the TAM/SPM follow-ups: types + acyclic creation ⇒
  decidable.
- **eros-fast-capability-system.pdf** — Shapiro et al. Persistent capability OS.
  Three security axioms; the **constructor/factory** confinement decision
  procedure; single-level store + **checkpoint with a pre-commit consistency
  check** = orthogonal persistence; the **weak** access right = automatic
  *transitive* read-only attenuation; KeySafe **compartments** = reference
  monitor wrapping every boundary-crossing cap (= membrane in OS form).
- **sel4-information-flow-enforcement.pdf** — Murray et al. The machine-checked
  **integrity theorem** + **authority confinement** + **intransitive
  noninterference (nonleakage)** over the 8,830-LOC kernel. The case split I
  build the vat-boundary law on lives here: integrity says *every state change
  is authorised by the current subject's caps*; confinement says *pas is an
  upper bound on authority, no thread's authority grows*; `sscc` is the
  boundary-stability side-condition.
- **doerrie-mechanized-confinement-capability-systems.pdf** — Doerrie's
  dissertation (SDM, **Coq, axiom-free**). First mechanized confinement proof:
  (1) machine-checked safety, (2) a system-lifetime upper bound `mutable` that
  **approximates** the true `mutated`, (3) the confinement test verified sound
  (`mutable` of any authorized subsystem ⊆ `mutable` of any subsystem passing
  the test). This is Miller's TA⊇EA bound, *formalized and checked*.

---

## Key ideas (attributed, with locations)

### A. Permission vs Authority, and the BA/TP lattice — Miller ch.8, Table 8.1
The single most load-bearing distinction for this axis. **[paper]**

- **Permission** = a direct access right = an *edge in the access graph*; the
  protection state is the *topology of permissions at an instant*
  (robust §8.1). **Authority** = the ability to *cause an effect* on a resource,
  possibly **indirectly**, through the behaviour of other subjects on permitted
  causal paths (the Alice-proxies-for-Bob example).
- Two analyses of "what can happen eventually": **de jure** (permission
  propagation; Bishop-Snyder potential-de-jure) vs **de facto** (authority /
  information transfer; potential-de-facto).
- Table 8.1 gives a lattice of bounds:
  `CP ⊆ EP ⊆ BP ⊆ TP` (current ⊆ eventual ⊆ behavioral-bound ⊆ topology-bound,
  permission side) and `EA ⊆ BA ⊆ TA` (authority side), with `EP⊆EA`, `BP⊆BA`,
  `TP⊆TA`. Tractability/safety verdicts:
  - **CP** trivial; **EP, EA** intractable (depend on behaviour, undecidable);
  - **TP, TA** "easy" (graph reachability) but **over-conservative** — they
    include flows that good code provably won't make (a caretaker "might" hand
    Bob direct access — but it won't);
  - **BA** = *behavioral bound on eventual authority* = **"the smallest safe
    tractable set"**: it never calls an unsafe policy safe, and usually lets us
    accept genuinely-safe policies that TA would reject.
- The two killer slogans (robust §8.1):
  - **"Permission is relative to a frame of reference. Authority is invariant."**
    (At one abstraction level the membrane's caretaker is a *permission edge*;
    one level up it is *behaviour that bounds authority*.)
  - **"To render a permission-only analysis useless, a threat model need not
    include malice or accident; it need only include subjects following security
    best practices."** (A caretaker — best practice — makes the static
    permission graph *lie* about real authority.)
- HRU footnote (robust §8.1, fn.2): HRU does **not** say safety is never
  decidable — it says you can *design* update rules that are undecidable. "At
  least three protection systems have been shown to be decidably safe
  [Take-Grant JLS76, EROS SW00, MPSV00]."

### B. The seven properties A–G — capability-myths
The discrete axiomatization of "what makes a cap a cap." **[paper]** (Fig.13/15)
- **A. No Designation Without Authority** — to *name* a resource is to *have* it
  (the cap *is* the designator). ACLs structurally cannot have this; it is the
  cure for the confused deputy.
- **B. Dynamic Subject Creation**; **G. Dynamic Resource Creation** — needed for
  least-privilege; ACLs lack B, POSIX-caps lack G.
- **C. Subject-Aggregated Authority Management** — you edit *your own* c-list,
  not the resource's ACL.
- **D. No Ambient Authority** — you must *select/present* the authority you
  exercise (vs Unix `open()` which silently uses whatever you happen to have).
- **E. Composability of Authorities** — resources *are* subjects; authority
  graphs compose to any depth. **This is what makes revocable forwarders
  possible.**
- **F. Access-Controlled Delegation Channels** — X can pass an authority to Y
  *only if X already has an access edge to Y*. **This is what makes confinement
  possible.**
- Confinement myth refuted: a cap transfer "cannot introduce a new connection
  between two objects that were not already connected by some path" — so
  confinement = *observe that the subgraph is disconnected from the rest*. To
  prevent Alice→Bob delegation, simply never give Alice access to Bob.
- Irrevocability myth refuted: **caretaker/forwarder pair** (F=forwarding facet
  to Bob, R=revoking facet kept by Alice). Revoking does not revoke the
  *capability* (Bob still holds F) — it revokes the *access F represents* by
  cutting R→Carol. Works transitively (anyone Bob delegated F to also loses it).
- **The caps→keys delta is exactly the loss of E and F.** caps-as-keys (Model 3,
  SPKI) has unrestricted propagation (no F ⇒ no confinement) and no
  composability-as-subjects in practice (no E ⇒ no revocable forwarder ⇒
  irrevocability genuinely true). Both myths are *true in Model 3 and false in
  Model 4*. This is the precise content of synthesis §2.2's
  "caps-as-caps vs keys-as-caps."

### C. Only-connectivity-begets-connectivity — Miller ch.9.2
The acquisition axiom. **[paper]** All ways Bob can come to reference Carol:
**initial conditions, parenthood** (Bob creates Carol), **endowment** (Bob born
holding Carol, by his creator), **introduction** (`alice.send(bob, carol)` —
requires Alice already hold *both* bob and carol). Mutation only *drops/reindexes*
references, never *acquires*. ⇒ **"all access must derive from previous access;
two disjoint subgraphs cannot become connected."** TP/TA analysis is literally
graph reachability over these edges. (This is the formal core of synthesis
§2.2's "unforgeable by construction" and 01-spine §1.1's CDT.)

### D. The vat and the turn — Miller ch.14
**[paper]** This is the direct source of dregg's "cell = membrane / turn =
generator" skeleton. A **vat** = one heap + one call-return stack + one delivery
queue + **one thread**. A **turn** = the run-to-completion processing of one
dequeued message; *each turn has mutually exclusive access to the vat's state*.
- **near reference**: same-vat, synchronous, conveys *immediate-call*
  (caps-as-caps).
- **far reference**: vat-crossing, conveys only *eventual-send*, returns a
  **promise** (keys-as-caps / async).
- "Only near references convey immediate-calls; objects in one vat may not
  immediate-call objects in another." ⇒ **the vat boundary is exactly the
  sync→async transition.** Vat = "minimum granularity for resource controls"
  and the unit of rollback ("vat incarnation rather than process… roll back to a
  previous assumed-good state"). This *is* synthesis §1's "a turn is a
  transaction whose effects are held until commit" and §2.1's three grains.
- **Defensive consistency** (ch.5) is the achievable property at vat granularity:
  a defensively-consistent object is *incorruptible by its clients* (correct or
  fails-stop, never gives a wrong answer) even though it may be DoS'd. Full
  *defensive correctness* (also guaranteeing progress) is infeasible across
  mutually-distrustful vats. **Corruption is contagious only upstream
  (provider→client), not downstream.**

### E. Take-Grant decidability — take-grant paper
**[paper]** `Can_share(α,x,y,G₀)` iff an α-edge can be added by the four rewrite
rules (take/grant/create/remove). Decidable via: **tg-path** (path of t/g
edges); **island** (maximal tg-connected subject-only subgraph — all rights
shareable within); **bridge** (a tg-path of a restricted form connecting
islands). Theorem: share is possible iff x's island connects to a vertex with
the α-edge through a chain of bridges (+ initial/terminal spans for objects).
**O(|V|+|E|)**. `Can_steal` (acquire without anyone *granting*) similarly
characterized. **The decidability is bought by restricting the rules** — HRU's
general matrix is undecidable; "limiting scope makes it decidable; types are
critical" (TAM: decidable iff acyclic creation graph; poly if commands ≤3
params). **This is the formal precedent that dregg's monotone-attenuation-only
edge rule yields a decidable cap-propagation safety question.**

### F. seL4 integrity / confinement / nonleakage — seL4 paper
**[paper]** The three-layer theorem, all machine-checked over the abstract spec
(then transported to C by refinement):
- **Integrity** `integrity pas s s'`: *any modification the current subject can
  perform is permitted by the authority represented in `pas`* — i.e. the change
  from s to s' is bounded by the current subject's outgoing authority edges.
  "When S2 executes, nothing in S1 changes, because S2 has only Read authority
  to S1."
- **Authority confinement**: `pas-refined pas s ⇒ pas-refined pas s'` for all
  reachable s' — **`pas` is an upper bound on authority; no thread's authority
  increases.** (Requires wellformedness: no Grant edges between distinct
  subjects, etc.)
- **Nonleakage / intransitive noninterference**: partition contents after n
  steps depend only on `PSched` + `sources n s p` (the partitions the policy
  permits to flow to p). The boundary-stability side-condition **`sscc`** (safe
  subject-crossing capabilities): every cap that crosses a partition boundary
  must be kept non-`final` (an inert never-deletable copy exists) — *because
  destroying a cross-boundary channel is itself observable both ways*, i.e.
  **the membrane's interface must be static, or its destruction is a covert
  bidirectional flow.**
- The **case-split engine** I need: integrity is proven *per transition* with
  exactly two cases — `part s ⤳ p` (the current partition *may* flow to p:
  contents may change, constrained by the authority edge) vs `part s ⤳̸ p` (no
  authority edge: integrity forces `s ∼ s'` for p — **p is untouched, no policy
  consulted because no edge exists**). This is the literal source of the
  vat-boundary law statement below.

### G. Mechanized confinement (SDM) — Doerrie
**[paper]** SDM, in Coq, **axiom-free** (no uninstantiable assertions). The
move that matters: define `mutated` (the objects a subsystem can *actually*
affect over the system lifetime — the EA-analogue, intractable in general) and a
decidable `mutable` (a topology-derived upper bound — the TA-analogue);
**prove `mutable` approximates (over-approximates) `mutated`** and is
*non-decreasing*. Then the **confinement test** (KeyKOS/EROS constructor: inspect
*only the caps to be placed in the new subsystem*, not the whole system) is
verified sound: any subsystem passing the test has `mutable` ⊆ the
authorized-set's `mutable`. Confinement is **composable** (unusual among
security policies) and validated by a *local* decision procedure on the minted
subsystem. This is the existence-proof that **dregg's `./metatheory` can carry a
checked vat-boundary/confinement theorem of exactly this shape.**

### H. EROS specifics — eros paper
**[paper]** (i) Three axioms: caps unforgeable/tamperproof; obtainable **only via
authorized interfaces**; given **only to the authorized** (synthesis Q2 axioms,
verbatim). (ii) **Constructor/factory** = the confinement decision procedure +
yield mechanism: a built subsystem's outward flow ⊆ flow inherent in the caps
its requester provided. (iii) **Weak** access right = capabilities fetched
through a weak cap are *automatically diminished to read-only+weak* ⇒
**transitive read-only is enforced by construction** (generalizes KeyKOS
*sense*). This is *monotone attenuation made into a kernel primitive* — a model
for dregg's attenuation-as-the-one-rule. (iv) Single-level store + periodic
**checkpoint with a pre-commit consistency check** ("an inconsistent checkpoint
lives forever" so check *before* commit; zero inconsistent checkpoints in 17
years) = orthogonal persistence + **the cheap-eager-pin discipline** of
synthesis §2.4 (causal order of protection state preserved; data journaling
allowed to violate causal order *only because it touches no protection state*).

---

## Takeaways for dregg (idea → concrete move)

1. **State the vat-boundary law as seL4's integrity case-split, lifted to turns.**
   → *Within one trust-root*: a turn composing entirely inside one vat consults
   **no** policy/authority edge — it mutates freely (sync, caps-as-caps, the
   kernel/executor *is* the mediator, no witness). *Crossing a trust-root*:
   every cross is gated by a **specific authority edge**, and that is exactly
   where the witness side of `Predicate ⊣ Witness` becomes mandatory. Maps to
   synthesis §8.4 (the sharp metatheory target) and §2.2. The law is the seL4
   `part s ⤳ p` vs `part s ⤳̸ p` dichotomy with `subject`→`trust-root`,
   `transition`→`turn`. **[design, grounded in seL4 §IV]**

2. **Adopt the seven properties A–G as the conformance checklist for the Cap
   type.** → 01-spine's `Cap` must satisfy A (CapHash is both name and
   authority), D (no ambient: every exercise *presents* its path), E/F (the
   CDT-edge rule *is* F; revocable-forwarder = E). When dregg crosses to keys
   (proof-is-truth removes the mediator), **flag explicitly that E and F are the
   two properties at risk** — see law in §"Tensions". Maps to
   `cell/src/capability.rs`, `facet.rs`. **[design, grounded in myths Fig.15]**

3. **Make `weak`/diminish a first-class attenuation primitive, not a special
   case.** → EROS's weak right shows monotone *transitive* read-only is
   implementable as "fetched caps are diminished by the edge they pass through."
   dregg's `attenuate_faceted` (capability.rs:288) should be the *general* form
   and `weak` a named point in the facet lattice; the AIR edge constraint
   `child.facet ⊆ parent.facet` (01-spine §2.2) is the same fact in-circuit.
   **[design, grounded in eros §2.3]**

4. **Use the confinement test (local, on-the-minted-subsystem) as the model for
   the deferred-prover's boundary check.** → Doerrie verifies you need inspect
   *only the caps placed in the new cell*, not the whole system, to bound its
   outward authority. dregg's "membrane crystallizes a proof obligation"
   (synthesis §2.3) should prove a *local* statement (`mutable(exported caps) ⊆
   authorized`), not a global one. Pairs with synthesis §6 keystone
   (deferred-prover) and the capability-sealed-serialization safety axis
   (§2.4(2)). **[design, grounded in doerrie §abstract + §9]**

5. **Keep EROS's pre-commit consistency check as the shape of the eager pin.**
   → synthesis §2.4 wants a "cheap eager pin … causally-pinned receipt chain."
   EROS's rule — *check consistency before the checkpoint commits, because a
   committed bad checkpoint is permanent; protection-state causal order is
   sacred, data may journal out of order* — is a directly transplantable
   invariant for `previous_receipt_hash` (turn.rs:6-38): the cheap pin must
   preserve **causal order of authority/protection events specifically**, and
   may relax it only for pure-data effects. **[design, grounded in eros §3.5]**

6. **BA, not TP, is the honest target for any "what can this cell eventually
   do?" query.** → Any dregg tooling that answers "can cell X reach resource Y"
   (audit, policy admission, the analogue of a security officer's query) must
   compute a **behavioral** bound (BA): a topology-only/static-cap-graph answer
   (TP/TA) will be *unsafe-by-overconservatism* — it will both (a) reject safe
   policies and (b, worse) mislead, because a caretaker/membrane makes the
   static graph *lie*. This is the formal justification for synthesis's
   "truth is the log (behaviour), not the static cap-graph." **[design,
   grounded in robust Table 8.1 + §9.4]**

7. **Vat = cell = the sync/membrane grain is correct and Miller-grounded.**
   → synthesis §2.1's "cell is the membrane grain (Spritely's vat)" and §1's
   "turn-as-generator, effects held until commit" are *exactly* Miller ch.14.
   No correction needed; the rollback-to-assumed-good-state ("vat incarnation")
   is the source of the time-travel claim. **[paper-confirms-design]**

---

## Tensions & corrections (where the papers strain/refute the synthesis)

- **T1 — "membrane" is being used too broadly; Miller's membrane is narrow.**
  The synthesis & 01-spine use "membrane" for the whole trust-boundary / phase /
  caps↔keys-conversion concept (§2, §6, "the membrane is the caps↔keys
  conversion point"). **Miller's membrane (ch.9) is a specific *pattern*: a
  transitively-applied caretaker** — it wraps *every* capability crossing in
  either direction in a forwarder, and **all those forwarders share one
  revocation switch** ("all these caretakers revoke together… the membrane
  remains interposed between Bob and Carol"). It is a *full-abstraction,
  transitively-revocable, same-vat forwarder*, not a trust-root or a sync/async
  boundary. Using "membrane" for the trust boundary conflates Miller's revocable
  *forwarder* with the *vat boundary itself*. **Correction / vocabulary
  recommendation in §4 below.** **[paper refutes loose usage]**

- **T2 — caps-as-caps does NOT survive the caps→keys crossing "principled-lossy
  but symmetric"; the loss is specifically E and F, and it is one-directional.**
  Synthesis §2.2 says "caps→keys drops the mediator's structural guarantee;
  keys→caps needs a trusted minter." The myths paper sharpens this: caps→keys
  loses **Property F** (⇒ confinement no longer holds: a key, once given, can be
  copied to anyone — Boebert's attack becomes real) and **Property E in
  practice** (⇒ revocation no longer free: irrevocability myth becomes *true*).
  So the forgetful functor doesn't just "drop the mediator" — it drops *exactly
  the two properties that confinement and revocation rest on*. State this
  precisely (see §"forgetful functor law" in Lean section). **[paper sharpens]**

- **T3 — the cap-graph is provably the *wrong* truth-source; this *supports*
  synthesis but contradicts 01-spine's strongest "the CDT IS the proof" reading.**
  01-spine §2 wants the static CDT path to *be* the proof of authorization.
  Table 8.1 says a *topological* (static-graph) bound is `TA` — safe but
  over-conservative, and **a behavioral abstraction (caretaker/membrane) makes
  the static graph not even reflect real authority**. The reconciliation: the
  CDT-path proof attests **permission/de-jure** (a real edge existed and every
  step was a legal attenuation) — that is sound and is the right thing to prove.
  But it must **not** be sold as proving **authority/de-facto** (what the
  recipient can *eventually cause*), which is BA/EA and *not* a static-graph
  fact. dregg should prove TP-class facts in-circuit and reason about BA-class
  facts *behaviorally / from the log*. This is the precise meeting point of
  "proof is truth (across)" and "log is truth (within behaviour)." **[paper
  qualifies 01-spine §2]**

- **T4 — confinement needs static interfaces (`sscc`); dregg's "fork/merge" and
  "teleport" mutate the boundary.** seL4's nonleakage requires that
  subject-crossing channels **never be destroyed** (destruction is an observable
  bidirectional flow). dregg's planned fork/merge and cell-teleport (synthesis
  §6.6–6.7) *do* mutate the boundary topology. ⇒ Either those operations must be
  modeled as happening *strictly within one trust-root* (so no cross-boundary
  channel changes), or the boundary-mutation must itself be an authorized,
  logged, gated turn. The membrane (forwarder) pattern handles this gracefully
  (revoke-by-switch leaves the channel *present but disabled*, not destroyed) —
  another reason to keep Miller's revocable-forwarder primitive. **[paper adds a
  constraint synthesis §6 omits]**

- **T5 — defensive *correctness* is infeasible; only defensive *consistency* is
  achievable — so the boundary law must be fail-stop, not fail-safe.** Miller
  ch.5: across mutually-distrustful vats you cannot guarantee progress, only
  incorruptibility. dregg's boundary law should therefore promise *"a crossing
  either produces a valid witnessed turn or fails-stop (breaks the
  promise/receipt)"* — never "always makes progress." Corruption contagion is
  upstream-only (provider→client); the law can rely on that direction. This
  matches dregg's `WitnessedReceipt` + broken-promise model but should be stated
  as the *limit* of what the boundary guarantees. **[paper bounds the claim]**

---

## Proposed Lean / metatheory artifacts

These target synthesis §8's seed (base category + conservation + two authority
models + the membrane law). `sorry`'d theorem targets are fine; the value is the
*statement*. **[design, shapes grounded as cited]**

```lean
-- §8.1 base: objects = cell states, morphisms = turns
opaque CellState : Type
opaque Turn : CellState → CellState → Type   -- a turn is an arrow
opaque TrustRoot : Type                       -- vat / host / seL4 CSpace (synth §2.1)
opaque rootOf : CellState → TrustRoot

-- §8.3 two authority models (myths Models 3 vs 4)
structure CapEdge where                       -- positional / caps-as-caps (Model 4)
  src dst : CellState
  facet   : Facet                             -- restricted interface (EffectMask)
-- the acquisition axiom: only-connectivity-begets-connectivity (robust §9.2)
inductive Reaches : CellState → CellState → Prop
  | initial  : Reaches a a
  | parent   : Creates a b → Reaches a b
  | endow    : Reaches alice c → Creates alice b → Endowed b c → Reaches b c
  | introduce: Reaches alice b → Reaches alice c → Introduces alice b c → Reaches b c
-- NB: no `mutate` constructor — mutation never acquires (robust §9.2)

-- monotone attenuation = the ONE edge rule (01-spine §2.2; eros `weak`)
def isAttenuation (parent child : CapEdge) : Prop :=
  child.facet ≤ parent.facet                  -- facet ⊆, authority ≤, caveats ⊇
theorem attenuation_decidable : DecidablePred (fun e => isAttenuation e.1 e.2) := sorry
  -- grounded: take-grant safety O(|V|+|E|); decidability from rule-restriction

-- THE VAT-BOUNDARY LAW (the synthesis §8.4 sharp target), as seL4's case split
-- (seL4 integrity §IV): "own the object ⇒ change freely; cross ⇒ authority edge"
theorem vat_boundary_law
    (t : Turn s s') :
    -- CASE 1: turn stays within one trust-root → no witness, no policy edge
    (rootOf s = rootOf s' → ChangesConfinedTo (rootOf s) t  -- integrity, intra
        ∧ ¬ RequiresWitness t)
    -- CASE 2: turn crosses a trust-root → a specific authority edge must license
    -- it AND the Witness side of (Predicate ⊣ Witness) is mandatory
    ∧ (rootOf s ≠ rootOf s' →
        ∃ e : CapEdge, AuthorizesCrossing e t        -- the "specific edge" (seL4)
          ∧ RequiresWitness t                        -- proof becomes mandatory
          ∧ isAttenuation_along_path e) := sorry

-- AUTHORITY CONFINEMENT (seL4): the trust-root is an upper bound; no growth
theorem authority_confinement (t : Turn s s') :
    AuthorityBound (rootOf s) s' ≤ AuthorityBound (rootOf s) s := sorry

-- THE FORGETFUL FUNCTOR caps→keys: what is PRECISELY lost (myths E,F; §T2)
-- F_drop : ObjCap (Model 4) → KeyCap (Model 3) is faithful on `target`/`facet`
-- but DROPS Property F (access-controlled delegation) and Property E-in-practice
theorem caps_to_keys_drops_F :
    ∀ (k : KeyCap), ¬ AccessControlledDelegation k := sorry   -- keys copy freely
theorem caps_to_keys_drops_E :
    ∀ (k : KeyCap), ¬ ∃ revoke, RevocableForwarder k revoke := sorry
-- consequence: the inverse keys→caps needs a TRUSTED MINTER to re-establish F
--   (synthesis §2.2), i.e. F_lift is only defined relative to a mediator island.

-- CONFINEMENT TEST is LOCAL (Doerrie SDM): inspect only the minted caps
-- `mutable` (topology bound, decidable) over-approximates `mutated` (actual)
def mutable (caps : List CapEdge) : Set CellState := sorry   -- TA-analogue
theorem mutable_approx_mutated (caps) : mutated caps ⊆ mutable caps := sorry
theorem confinement_test_sound (sub authorized) :
    PassesTest sub authorized → mutable sub.caps ⊆ mutable authorized := sorry
```

Differential-testing hook (synthesis §9.1): Lean `mutable`/`isAttenuation` are
the **golden oracle**; the Rust `is_attenuation` (capability.rs:461) and the
deferred-prover's boundary check are checked against it (the
`dregg-dsl-differential` pattern). Lean buys coherence + the precise
caps→keys-loss statement; it does **not** establish that the STARK attests the
morphism (synthesis §8 caveat — that lives in the circuit).

---

## Open questions / what to read next

1. **BA in-circuit?** Table 8.1 says BA (behavioral authority bound) is the
   smallest safe tractable set, but it depends on *behaviour*. Can the
   deferred-prover prove a *behavioral* bound (e.g. "this exported cell's
   forwarder only forwards `read`"), or is dregg structurally limited to proving
   TP-class (path-exists + legal-attenuation) facts and must treat BA as a
   log/behavioral matter? This decides whether "membrane proves what it
   attenuates" (01-spine §4.4) is a TP or BA claim. **(Central; revisit with the
   proof-spine agent.)**
2. **Intransitive noninterference for dregg's 4-corners regime.** seL4's
   nonleakage handles *intransitive* policies (A→B, B→C, ¬A→C). dregg's
   off-diagonal corners (synthesis §9.2) may need exactly this. Read
   `complexity-of-intransitive-noninterference.pdf` and
   `noninterference-for-os-kernels-murray.pdf` next.
3. **`sscc` vs fork/merge/teleport (T4).** Does dregg's boundary-mutation story
   need a "static-interface" invariant? Cross-check with the cell-spine agent
   and `verifying-eros-confinement.pdf` (Shapiro/Weber, the [SW00] decidable
   system Miller cites).
4. **Constructor/factory ↔ on-chain mint/grant (synthesis §6.8).** The KeyKOS
   factory confinement test (Doerrie §9) looks isomorphic to dregg's planned
   `GrantCapability`→biscuit-block + capability-tree-as-view. Confirm the
   embedding; SDM "embeds without injecting into the semantics" — a model for
   keeping the cap layer a *projection* (synthesis §1) not a god-object.
5. **capdl-sel4.pdf / keykos-nanokernel** (unread, available) — capDL is the
   concrete language for "ship `(id, head, rule)`" cell descriptors (synthesis
   §6.7); worth a pass for the teleport/transport format.
6. **proof-carrying-authorization (Garg/Appel-Felten/Bauer, unread)** — PCA is
   *literally* "auth-in-proof" prior art (synthesis §5.3 recovery); read to
   avoid reinventing, and to ground the `RequiresWitness`/discharge surface.
