# DREGG4-OS-ENDGAME — the Robigalia persistent-distributed-OS endgame (galaxy-brain, read-only)

> **What this is.** A READ-ONLY design exploration of the *advanced* OS/capability features that make
> dregg **an operating system, not a chain** (`REORIENT.md §0`). It picks up where the dregg2/dregg4
> split was drawn in `CARRY-FORWARD-SYNTHESIS.md §4`: dregg2 = the faithful 3-faced kernel; **dregg4 =
> the generalization** where *every* higher-level capability is composed from one small core + the
> caveat algebra + the attestation modes, with the **transferability** and **disclosure** dials
> first-class. This doc surfaces the features that live *above* that kernel — and the galaxy-brain
> rethinks that could define dregg4.
>
> **The frame I hold throughout (the three-faced turn, `CARRY-FORWARD-SYNTHESIS §0`).** Every feature
> below is decomposed onto:
> - **EFFECTS** (the living-cell step / A-projection / `cand-A`) — the state transition.
> - **CAVEATS / AUTH** (the verify/find law / B + the authority CDT / C) — authorization-narrowing.
> - **ATTESTATION** (the badge = permitted ∧ committed) — the output, **with two dials**: *disclosure*
>   ∈ {acceptance-only, selective, full} (what is revealed) and *transferability* ∈ {public,
>   designated, deniable} (to whom the proof is convincing). The second dial does not exist in the code
>   today — it is pinned at `public` (`GROUND-AUTH-ATTESTATION.md §2.1–§2.3`) — and that absence is the
>   seam through which several dregg4 features enter.
>
> **The honesty discipline (REORIENT §6, carried in).** For each feature I distinguish a *genuinely-new
> capability* from a *rephrasing of an existing theorem*. The biggest finding of `cand-A` is that
> checkpoint/restore/replay/time-travel are **theorems, not features** (anamorphism re-seed + retained
> log + rollback-handler turn, `cand-A §5`). So the interesting dregg4 question is rarely "add the
> feature" — it is "what is the *smallest genuinely-new primitive or dial* that turns an existing
> theorem into the OS-scale product," and where that primitive sits on the three faces.

---

## 0. The one-paragraph thesis

dregg2's center is a *single* living cell whose checkpoint/replay/fork are theorems
(`cand-A §5–§6`). **dregg4 is what happens when you take those single-cell theorems coinductive-and-
networked.** A checkpoint that is a named `(head, receipt)` becomes, at network scale, a *distributed
debugger* (§2). The anamorphism re-seed becomes *live cell migration* (§1). The fork-span becomes
*multi-agent collaboration on untrusted code* (§5). The named-lossy Φ (caps→keys) becomes a *capability
market* once you add the one dial it is missing — *transferability/leasing* (§3). And the
choreography front-end (`cand-D`) is the developer surface that ties them together (§4). The recurring
shape: **dregg2 proved the local theorem; dregg4 adds exactly one networked dial or one coinductive
re-seed, and the OS feature falls out.** The features that need *genuinely new theory* — and are
therefore the most ambitious — are the ones touching the **transferability dial** (markets,
revocation-under-partition, recovery) and the **cross-cell binding** (`νF₁⊗νF₂` is not final,
`study-category.md`), because those are the two places where "compose the local theorem" provably
*fails*.

---

## 1. Live cell migration across the network

**The vision.** A running cell — its state, its `CellProgram`, its held caps, its in-flight awaits —
relocates from vat A to vat B *while live*, surviving partition, without double-existence and without
losing authority it held or gaining authority it didn't.

**Where it derives from / what's new.**
- **Derives (the easy 80%):** this is *literally* `cand-A`'s **anamorphism re-seed** (`cand-A §5`:
  "Restore = resume the unfold from a retained head … re-seeding the anamorphism at an earlier point")
  applied across a vat boundary instead of across time. The cell's substrate footprint is already
  `(id, head, rule)` + retained log (`cand-A §2.1`); migration = ship that triple + receipts over the
  shared DAG (`cand-C §5` "Teleport"). The Rust **already has a real two-phase-commit migration FSM**
  (`turn/src/executor/migration.rs:25` `MigrationState{Frozen,AwaitingReceipt,Completed,Cancelled}`,
  `begin_migration` at `:104`) precisely to avoid the partition-limbo / double-existence hazard
  (`migration.rs:8–23`). So the *mechanism* exists in code and the *theorem* exists in the metatheory;
  they are not yet connected.
- **Genuinely new (the hard 20%):** three things.
  1. **Migrating held authority across the lossy Φ.** Inside vat A authority is caps-as-caps
     (positional); the instant the cell lands in vat B it is keys-as-caps. Migration is **a forced ρ_out
     ∘ ρ_in** (`cand-C §10`, the membrane) on *every held cap at once* — which means the migrated cell
     **loses confinement and revocable-forwarders by construction** (`LossyMorphism`, `cand-C §4B`). The
     genuinely-new piece is a *migration-as-attenuation* theorem: "the post-migration cell's authority
     is ≤ its pre-migration authority, and the loss is exactly Φ's." Nothing today states this.
  2. **Migrating in-flight awaits.** A cell mid-`Await` (a suspended continuation, `cand-A §3`) must
     carry its one-shot linear continuation across the boundary. Continuations are *the one non-algebraic
     effect* (`cand-A §2.2`), so this is not "serialize the state" — it is serialize-a-delimited-
     continuation, the hardest part, and unmodeled.
  3. **The two-phase-commit blocks under partition** (the `migration.rs` `Frozen→Cancelled` timeout) —
     and that is the *correct* `OPEN-PROBLEMS` price (`REORIENT §2`, "cross-disjoint-group atomic commit
     blocks under partition; the price of no global ledger"). dregg4's honest move is **migration =
     a single-cell JointTurn-degenerate** so the same CG-2/CG-5 binding (atomicity-as-proof, not 2PC)
     governs it — replacing the live 2PC FSM with a proof property.

**Three faces.** EFFECTS: a new boundary primitive `Boundary.exportKey/importKey` (the ρ pair,
`EFFECT-ISA-DESIGN §B-#3`) applied to the *whole c-list*; the state-transition is "this cell's head is
now anchored under vat B's root." CAVEATS: every migrated cap re-derives its CDT path under B's
`RootSeal` (attenuation-only). ATTESTATION: the migration receipt is a badge attesting "frozen-at-A ∧
landed-at-B ∧ no-double-existence," which is exactly the `migration.rs` receipt-confirmation step lifted
to a WitnessedReceipt. *Dials:* migration wants **disclosure=selective** (B learns the cell's interface,
not its private state) and is the first feature that *wants* **transferability=designated** (the
migration receipt should convince B, not be a transferable "this cell defected from A" artifact).

**What it would take.** Connect `migration.rs`'s FSM to `cand-A`'s re-seed theorem; prove
migration-as-attenuation; solve continuation-serialization (the genuinely-hard research item); replace
2PC with the JointTurn binding.

---

## 2. Networked time-travel debugging (the distributed debugger)

**The vision.** A developer (or an agent) attaches to a *running network* of cells, sets a breakpoint
("suspend before any turn whose `ACTION_AUTHORITY_DIGEST` touches cell C"), steps the coalgebra under
operator control, inspects `Obs` at each `▶`, and on finding a bad turn **time-travels** to before it
and **forks** an alternate history — *across vats*, not just locally.

**Where it derives from / what's new.**
- **Derives (almost all of it, single-cell):** `cand-A §5` already makes this a *theorem*, verbatim —
  "the debugger is not instrumentation over the runtime — it *is* the runtime's own rollback-handler
  exposed to an operator"; "Breakpoints are admissibility predicates"; "step back is `abort`, step
  forward is `commit`"; "a failed proof … becomes inspectable: the debugger replays the witness build
  and shows *which conjunct of `StepInv`* rejected." This is the single strongest "feature = theorem"
  result in the corpus. dregg2 gets the *local* debugger for free.
- **Genuinely new (the networked lift):**
  1. **Distributed consistent snapshot.** Time-travel of *one* cell is re-seed; time-travel of a
     *causally-entangled set* of cells requires a **consistent cut** of the blocklace DAG — a
     Chandy-Lamport-shaped snapshot, but content-addressed and Byzantine. The genuinely-new theory is
     "a cut is valid iff it is downward-closed in the CDT partial order and conservation-balanced across
     the cut" — which is *exactly* the JointTurn equalizer condition (CG-5) re-read as a snapshot
     predicate. Nobody has connected "consistent distributed snapshot" to "the JointTurn binding"; that
     identification is a dregg4-native idea.
  2. **Forking a network, not a cell.** `cand-A §6` fork is a span/pushout with hand-proved laws; a
     *distributed* fork is a span in the JointTurn tensor — and `νF₁⊗νF₂` is **not final**
     (`study-category.md`), so "fork the network" does **not** reduce to "fork each cell." This is the
     same irreducibility that makes cross-cell soundness a hypothesis (`REORIENT §2`); the debugger
     inherits it. Honest dregg4 stance: network-fork is only sound over a *session-ordered* sub-DAG
     (the `cand-D §5d` boundary lemma), and *rejected* over `G₁|G₂`-concurrent shared cells.
  3. **Adversarial replay / "blame replay."** Because `cand-D`'s monitor assigns **blame**
     (`cand-D §2`), the networked debugger can *replay an equivocation*: show the two incompatible
     blocks a Byzantine peer gossiped and the cut at which they diverge. This is a debugger feature that
     only exists because the substrate is the equivocation-repelling blocklace (`cand-D §5a`).

**Three faces.** EFFECTS: none new at the kernel — the debugger drives the *existing* commit/abort of
the rollback-handler turn; it is pure runtime-theorem (`EFFECT-ISA-DESIGN §3`, "checkpoint/replay/time-
travel … adding them as effects would be a category error"). CAVEATS: a debug-attach is itself a
*cap* — you may only step/inspect cells you hold an inspection cap into; **this is the seam where
debugging meets confinement** (a debugger that could inspect any cell would break the OS's whole point).
ATTESTATION: an inspection produces a *non-transferable* view of private `Obs` — so the debugger is the
**second feature that needs transferability=designated/deniable**: "I showed you my cell's internal
state for debugging; you cannot prove to anyone else what it contained."

**What it would take.** The consistent-cut-as-CG5 theorem; the network-fork well-formedness restriction
(reuse `cand-D §5d`); an inspection-cap facet; and the designated-verifier dial (§7) so debug views
don't become transferable surveillance.

---

## 3. Capability markets / leasing / economics

**The vision.** Caps are *leased* (time-boxed, auto-expiring), *priced* (a market clears who gets a
contended cap), *metered* (computron/byte quotas, which the storage tier already meters,
`GROUND-STORAGE §0`), and *traded* (a cap is a transferable, attenuatable asset with a settlement
guarantee).

**Where it derives from / what's new.** This is the feature that is *most* "rephrasing + one new dial,"
and the analysis is sharp:
- **Leasing derives, fully.** `cand-A §9.6` / `cand-C §7.2` already make **short-expiry-plus-renewal the
  *preferred* substitute for revocation** ("auto-revoke needs no gossip"). A lease is just an `Expiry`
  caveat (`cand-C §3` `CaveatSet = {Expiry, Predicate, Rate, Finality}`) + a renewal turn. **Leasing is
  not new — it is the architecture's recommended revocation strategy wearing a market name.** Computron
  metering is real in Rust (`storage/` quota, `GROUND-STORAGE §0`). Rate-limiting is an existing caveat
  (`RateLimit(BySum)`, `EFFECT-ISA-DESIGN §0` constraint vocab).
- **Pricing/clearing is the genuinely-new — and it is *exactly* the VERIFY/FIND seam at a new altitude.**
  `cand-A §3` / `cand-B §3.2`: "Winner-determination is NP-hard, no PTAS … the matcher is a bounded,
  untrusted, soundness-only plugin." A **combinatorial-auction clearing engine is the canonical
  FIND-intractable search** (`pdfs/winner-determination-combinatorial-auctions-sandholm`), so dregg4's
  market = *an untrusted clearing solver emitting a checkable allocation witness*. That is not new
  *theory* — it is the existing intent-matcher (`cand-A §3`, the ∃-filler face) pointed at cap
  allocation. The genuinely-new piece is the **settlement atomicity**: "the winner gets the cap **iff**
  payment conserves" is a JointTurn over `(cap-grant cell, payment cell)` (CG-5 conservation across the
  pair). Markets bottom out on the cross-cell binding, same as everything hard.
- **The truly-new dial: TRANSFERABLE caps as a first-class asset.** Today a cap is *attenuation-only and
  non-revendible* — Φ's loss means once you ρ_out a key you cannot prove you *gave it away* (vs *copied
  it*). A **cap lease-market needs the transferability dial on the cap itself**: a "I transfer this cap
  to you and *provably no longer hold it*" operation. This is genuinely absent — it is the *dual* of the
  repudiation hole (`GROUND-AUTH §2`): the badge is over-transferable, but the *cap* is under-
  transferable (you can copy a key but cannot prove a hand-off was exclusive). dregg4's market needs an
  **exclusive-transfer primitive** — which is a *nullifier on the cap* (`NoteSpend`-shaped, S3 in
  `EFFECT-ISA-DESIGN §S3`): transferring a cap *spends* the holder's copy into a nullifier set and mints
  the recipient's. **This is the cleanest galaxy-brain rethink in the doc:** *a tradeable capability is a
  note.* The note machinery (commitment-insert / nullifier-spend, already CORE C11/C12) is *the* missing
  market primitive, and it unifies "private value" and "tradeable authority" under one shape.

**Three faces.** EFFECTS: `Cap.transferExclusive` = C12 nullifier-spend of the source cap + C4 cap-graph
add at the destination, bound in one JointTurn with the payment half-edge (C1). CAVEATS: the lease is
an `Expiry` + `Rate` caveat; the clearing is an untrusted plugin. ATTESTATION: the allocation receipt is
transferable (a market *needs* public settlement — `GROUND-AUTH §2.3`, "consensus/forest path keeps the
transferable badge"). *Dials:* market=**transferability=public** (settlement must be third-party
verifiable), which is the *opposite* of debugging/migration — confirming the dial is genuinely a
first-class choice, not a global setting.

**What it would take.** The cap-as-note exclusive-transfer primitive (the new CORE shape — really a
*reuse* of C11/C12 over a cap record); the clearing-as-FIND plugin; settlement-as-JointTurn. Economics
*above* that (auction design, incentive-compatibility) is `pdfs/§26` mechanism-design and is honestly
out-of-core (it is app-layer on the protocol-cell, `gaps-1-substrate`).

---

## 4. The choreography front-end (cand-D) as the real developer surface

**The vision.** Developers/agents do **not** write turns. They write a **global type `G`** (a
multiparty protocol / choreography, `cand-D §1`); the compiler *projects* it to per-cell `CellProgram`s
and `JointTurn`s; the projected local types are enforced by **runtime monitors that assign blame**
(`cand-D §2`). This is "many syntaxes, one semantics" (`cand-D §0`) realized as the actual IDE.

**Where it derives from / what's new.**
- **Derives:** `cand-D` already establishes that **the membrane = endpoint projection = runtime
  monitor** (`cand-D §2`, "the vat-boundary law and the EPP-correspondence theorem are the same theorem
  at two altitudes"). The runtime is *unchanged* (`cand-D §6`: blue interactions → CellProgram
  admissibility, red → JointTurn); cand-D only adds the front-end. The three judgements collapse into
  one annotated `G` + one analysis (`cand-D §1`).
- **Genuinely new for dregg4 (the developer/agent experience):**
  1. **Choreography as the *agent's* surface, not the human's.** The corpus assumes a human authors `G`.
     The galaxy-brain rethink: in the multi-agent-on-untrusted-code use case (§5), **the agents
     *negotiate* `G`** — `cand-D §3.2` bottom-up compatibility synthesis (`mpst-meet-communicating-
     automata`) means two agents that share *no* pre-agreed protocol can **synthesize a compatible `G`
     from their declared endpoints**. dregg4's developer experience is: each agent declares a local type;
     the system *checks compatibility and emits the monitored boundary*; if incompatible, it produces a
     **blame-localized counterexample** ("your endpoint sends X where mine expects Y"). This is a
     genuinely-new *product* on existing theory.
  2. **Gradual typing as the trust gradient.** `cand-D §3.3` (`gradual-session-types`,
     `hybrid-multiparty-session-types`): typed and untyped endpoints interoperate with blame. This is the
     *exact* shape of "trusted-collaborator code is typed; untrusted-pulled code is `?`-typed and
     monitored" — the gradual `?` boundary *is* the sandbox boundary. The dial: **disclosure of the
     protocol** — a collaborator may see all of `G`; an untrusted party sees only `G ↾ p` (privacy-by-
     projection, `GLOSSARY` "coordination layer").
- **The honest dependency (don't oversell):** `cand-D §5a` — choreography monitoring catches "did you
  follow the protocol as I observed it" but **cannot catch equivocation**; that bottoms out on the
  blocklace (`cand-C`). And `cand-D §8`: cand-D is **purely additive and built last** (after the
  soundness spine, `Confluence.lean`, and the JointTurn). So it is the *surface* but not the *foundation*
  — which is correct, and means dregg4 must not start here.

**Three faces.** The whole point of cand-D is that `G` *carries all three* (`cand-D §1`): conservation =
linear payload typing, ordering = `G`'s sequencing, I-confluence = the projection-time blue/red coloring.
The projector is **untrusted** (`cand-D §5e`): its output is StepInv-checkable, so the TCB does not grow.
*Dials:* protocol-disclosure (privacy-by-projection) and — for a deniable protocol step — transferability,
both expressible as annotations on `G`.

**What it would take.** `Projection.lean` + the projection-split compiler + the `epp_correspondence`
theorem (`cand-D §7`); the open `byzantine_epp_by_monitoring` theorem (the named frontier); the bottom-up
synthesis engine as an untrusted plugin. **Build last.**

---

## 5. Multi-agent collaboration on untrusted code (THE use case)

**The vision (the actual reason dregg exists, `REORIENT §0`).** Multiple agents — some yours, some not,
some malicious — collaborate on a shared codebase / shared cells, **on your machine**, and you do not get
hacked. What is the developer/agent experience?

**The experience, concretely, woven from the pieces above:**
1. You pull an untrusted project. It runs **as cells in a sandbox vat** (`cand-A §5`, the Robigalia
   developer story). The vat is the trust-root boundary; the untrusted code holds *only* the caps
   explicitly delegated into its CSpace — positional, kernel-enforced *intra-vat* (`cand-C §3`).
2. Nothing it does affects your other cells without a turn **crossing the vat boundary**, and every
   boundary-crossing turn is step-complete-witnessed (`cand-A §5`). "Run anyone's code; you never run it
   on your authority — you check the badge it hands you" (`cand-B §4`).
3. You and a collaborating agent **negotiate a `G`** (§4): the protocol you'll cooperate under. Typed
   collaborator, `?`-typed stranger, monitored boundary with blame (`cand-D §3.3`).
4. If the untrusted code misbehaves, you **time-travel** (§2) to before the bad turn, the **debugger**
   shows *which `StepInv` conjunct it tried to violate* (`cand-A §5`), and you **fork** an alternate
   history (`cand-A §6`).
5. The collaboration artifact is **badge exchange** (`cand-B §4`): two agents trade `WitnessedReceipt`s;
   each verifies the other's strand-head in milliseconds *without replaying* the other's turns.

**Where it derives / what's new.**
- **Derives:** every step above is an existing theorem or candidate. The *integration* is the product.
- **Genuinely new for the *agent* (not human) case:**
  1. **Agents as untrusted *provers*, you as the *verifier* (`cand-B`'s thesis, agent-shaped).** An LLM
     agent is exactly the "untrusted solver emitting a checkable witness" of the VERIFY/FIND seam
     (`cand-A §0`). The agent *searches* (writes code, finds a delegation path, proposes a `G`); your
     kernel *verifies*. This is the cleanest possible statement of "safe agentic coding": the agent has
     **zero authority**; it can only ever *fail to produce* a valid badge (`cand-B §4`), never forge
     accept. dregg4's headline is **"agents are FIND, the kernel is VERIFY."**
  2. **Fork-as-sandbox for *speculative* agent work** (`cand-C §3`, "Fork-as-sandbox = the collaboration
     primitive"). An agent's speculative branch is a `ForkCap` scoping a copy-on-write sub-CDT; **merge =
     re-root iff every edge stays a monotone attenuation** (`cand-C §3`) — so an agent literally *cannot*
     merge work that amplified its authority; the merge rule is the security boundary. This is genuinely
     new as a *workflow*: "agent works in a fork; you review the merge; the merge is rejected on
     attenuation-violation, not on taste."
  3. **The capability-attenuated tool-call.** An agent's tool call is a turn exercising a cap; the
     **caveat dials the tool** — `App{id,actions}`, `Budget`, `ValidityWindow`, `FeatureGlob`
     (`GROUND-AUTH §1.1`, the real `dregg_caveats`). dregg4's tool-permissioning *is* the macaroon caveat
     vocabulary, which already exists — the new piece is wiring it to an agent harness.

**Three faces.** EFFECTS: the agent's turns are ordinary cell steps inside the sandbox vat. CAVEATS: the
agent's *entire authority* is the c-list delegated into its vat — this is the load-bearing face for this
use case. ATTESTATION: badge exchange is the collaboration medium. *Dials:* the agent collaboration wants
**disclosure=selective** (the agent sees its sandbox, not your private cells) and the review/merge wants
the attenuation-merge rule (`cand-C §3`).

**What it would take.** A vat sandbox host wiring the existing pieces (the migration/fork code +
macaroon caveats + the badge verifier) into an agent harness. This is *more integration than new theory*
— which is why it is the most *deliverable* of the ambitious features (see ranking).

---

## 6. Cross-cell live upgrade / hot-patching of cell programs

**The vision.** Swap a running cell's `CellProgram` (its admissibility logic / business rules) *while
live*, without bricking it, and roll a coordinated upgrade across a *set* of interacting cells.

**Where it derives / what's new.**
- **Derives:** the anti-brick machinery is *already designed* — the `set_program` / `AIR_VERSION` clause
  (`GLOSSARY` "anti-brick"; `dregg2-multicell-privacy §3`): a `CellProgram`-upgrade carries an
  admissibility clause pinning a proof-system/AIR version, with **owner-signature fallback** so a verifier
  upgrade never strands a sovereign cell. Schema upgrade is **lazy migrate-on-read, sound iff transparent
  ∧ conservative** (`GLOSSARY` "Preserves"; `cand-A §2.4`). The Lean models this faithfully
  (`Exec/StateMigration.lean`, `GROUND-STORAGE §0`).
- **Genuinely new (the *cross-cell coordinated* upgrade):**
  1. **Atomic multi-cell program swap.** Upgrading *one* cell is the existing clause. Upgrading a *set*
     of cells that interact under a `G` so that no intermediate mixed-version state is observable is a
     **JointTurn over the upgrade turns** — and again bottoms out on CG-2/CG-5 (`νF₁⊗νF₂` not final). The
     new theorem: "a coordinated upgrade is sound iff it is a single JointTurn whose per-cell legs each
     satisfy the anti-brick clause." Nobody has stated cross-cell upgrade as a JointTurn.
  2. **Hot-patch as a fork-then-merge.** The galaxy-brain rethink: a hot-patch is **a fork (`cand-A §6`)
     where the divergence is the *program*, not the input stream.** You fork the cell, run the new program
     on the forked head, and merge iff the new program's behavior stays an attenuation of the contract
     (the same merge rule). "Time-travel debugging on the *rules*" — this unifies hot-patch with the
     debugger (§2) under one fork primitive.
  3. **Schema-DAG fork/merge migration** — flagged *open* in `cand-C §7.5` ("Open: schema-DAG / fork-merge
     migration"). When two forks migrate the schema differently, merge needs a *lens* (`pdfs/§16`,
     `cambria-schema-evolution-edit-lenses`, `safe-on-the-fly-relational-schema-evolution`). This is
     genuinely-open theory.

**Three faces.** EFFECTS: `set_program` is a C7 `Meta.bind(domain_tag=program, hash)` (passthrough +
bind the new program hash) — *no new effect*, it is the existing passthrough family
(`EFFECT-ISA-DESIGN §C7`). CAVEATS: the upgrade authority (owner-sig fallback or governance). ATTESTATION:
the upgrade receipt binds old-program-hash → new-program-hash with the anti-brick version. *Dials:*
an upgrade is **transferability=public** (everyone must agree the cell now runs program v2).

**What it would take.** Lift the single-cell anti-brick clause to a JointTurn; the hot-patch-as-program-
fork theorem; the schema-DAG lens (open). The single-cell case is *nearly free* (the design exists);
the cross-cell case is JointTurn-bound; the schema-DAG merge is research.

---

## 7. Capability revocation and recovery under partition

**The vision.** Revoke a cap globally; recover authority after a key compromise or a lost device; do both
*correctly* under network partition.

**Where it derives / what's new.** This is the feature the corpus is *most explicitly honest* about being
hard, and it is a *theorem about a bound*, not a feature to add:
- **Derives (the bound):** revocation is **the one globalism** (`cand-C §6`): a **negative discharge** —
  a STARK *non-membership* proof against an attested revocation root (`cand-A §11`, `cand-C §6/§10`). It
  needs **only root-epoch agreement**; everything else stays local + offline. And the hard truth
  (`OPEN-PROBLEMS`, `cand-C §7.2`): **revocation has a recency floor under partition** — "a partitioned
  phone honors a revoked cap until it learns otherwise … any design claiming clean local-first revocation
  is lying." Mitigation = **short-expiry+renewal** (auto-revoke needs no gossip) + the receipt records
  "exercised at staleness S" so a reconciler can *compensate, not prevent*.
- **Genuinely new (recovery, and the accountable-anonymity tension):**
  1. **Recovery = re-mint under a fresh root, with a provable abdication of the old.** A lost-device
     recovery is *exactly* the cap-as-note exclusive-transfer (§3): nullify the old root's caps, mint
     under the new root, with a JointTurn binding the two so no double-spend of authority. **Recovery and
     market-transfer are the same primitive** — another unification (the cap-nullifier).
  2. **Accountable revocation of anonymous caps** — the open tension. If a cap is anonymous (stealth /
     StarkDelegation, `GROUND-AUTH §2.2a`), *who* can revoke it, and can revocation *de-anonymize*? This
     is `pdfs/§24` (`towards-accountability-for-anonymous-credentials`, `publicly-auditable-privacy-
     revocation-anoncreds`, `revocable-proof-systems` — which bounds what stateless-chain revocation can
     do). The genuinely-new dregg4 piece: a **revocation authority that is itself a capability**, so "who
     can revoke" is a cap-graph fact, and revocation-with-accountability is a *designated-verifier
     de-anonymization* (the transferability dial again — revocation may reveal identity *only to a named
     authority*, not publicly).
  3. **Partition-time revocation as I-confluence.** Revocation is a *tombstone edge* (monotone add to a
     revocation G-Set) — which **is I-confluent** (`Credential.lean:226-244` revocation reuses the
     nullifier G-Set with real I-confluence, `GROUND-AUTH §1.6`). So revocation *spreads* like a CRDT and
     never un-revokes; the only non-I-confluent part is the *recency* (when did you learn). dregg4's clean
     statement: **revocation safety is I-confluent (tier-1, never blocks); revocation *recency* is the
     consensus-bound part.** Splitting these two is the right rethink.

**Three faces.** EFFECTS: revoke = C4 cap-graph edge-remove + a tombstone insert; recover = the
cap-nullifier exclusive-transfer (§3). CAVEATS: the negative-discharge non-membership witness is the
*new gate* on every cross-vat exercise. ATTESTATION: a revocation receipt is public (it must spread); a
recovery-with-accountability receipt is **designated** (de-anonymizes only to the authority). *Dials:*
this feature is the one that most needs **both** dials wired (selective disclosure of *who revoked* +
designated transferability of *de-anonymization*).

**What it would take.** The negative-discharge non-membership circuit (a STARK obligation, §8-railed);
the revocation-G-Set I-confluence (mostly done in `Credential.lean`); the recovery = cap-nullifier reuse;
and the accountable-de-anonymization designated-verifier mode (the new theory, §7-dial).

---

## 8. A real object-capability shell / nameservice

**The vision.** A `bash`-for-ocap: a shell where "files" are cells, "processes" are running cells,
"pipes" are caps/promises, and a **nameservice** resolves human/agent-friendly names to `CapHash`es —
the actual *interface* to the whole OS.

**Where it derives / what's new.**
- **Derives:** a nameservice is **just a cell whose `CellProgram` is a name→CapHash map** — DSL-userspace
  (`EFFECT-ISA-DESIGN §DSL`, "a queue is a cell program, not a kernel primitive"; the same logic applies
  to a directory). The Rust *already has* the Robigalia VFS triple (`rbg/vfs.rs` Volume/Blob/Directory,
  `GROUND-STORAGE §0`). Resolving a name = exercising a read-cap on the nameservice cell; the shell's
  "current directory" is a held cap; a "pipe" is a promise (`PipelinedSend`, `cand-A §2.2` return
  projection). **Almost all of the shell is composition of existing pieces.**
- **Genuinely new (the ocap-shell rethinks):**
  1. **Petname systems, not global names.** The galaxy-brain correctness move (Stiegler/Miller petnames,
     `pdfs/§1` capability theory): there is **no global namespace** (global names re-introduce ambient
     authority). Each principal has its own *petname* cell mapping its private names to CapHashes; names
     are introduced by **cap handoff + naming** (the sealer/unsealer three-vat handoff, S11). dregg4's
     nameservice is **per-vat petname cells federated by introduction**, not a DNS. This is genuinely
     different from every "decentralized naming" chain (which all rebuild a global namespace).
  2. **The shell is a choreography author (§4).** A shell pipeline `a | b | c` *is* a global type `G`
     over three cells; the shell *is* the cand-D front-end's REPL. "Piping" = projecting a 3-party `G`.
     This unifies the shell with the choreography surface.
  3. **Tab-completion as VERIFY/FIND.** Resolving "what can I do with this cap" = enumerating the facet
     (the canonical Set of effect Symbols, `cand-A §2.4` Preserves). The shell's introspection is reading
     the facet; the shell's *search* ("find me a cell that can do X") is the FIND-intractable intent
     matcher (`cand-A §3`). The shell is the human/agent face of the verify/find seam.

**Three faces.** EFFECTS: none new — name-write is C6/C7, resolution is a read. CAVEATS: a petname cell
is read/write-gated like any cell; introduction is sealer/unsealer. ATTESTATION: name bindings can be
attested (a signed petname) or local (private). *Dials:* petnames are inherently **disclosure=selective**
(my names are mine) and the introduction handoff can be **designated** (I tell you a name privately).

**What it would take.** A petname `CellProgram` template (DSL-userspace, like the storage templates);
wiring `rbg/vfs.rs` to it; the shell-as-cand-D-REPL (depends on §4). This is **mostly integration** of
existing pieces — the lowest-theory, highest-ergonomics feature.

---

## 9. Galaxy-brain rethinks not yet considered in the corpus

These are the surprising ideas — things the corpus *implies* but never names. Ranked by surprise×payoff
in §10.

- **R1 — A tradeable capability is a note (the cap-nullifier).** §3/§7 above. The single most unifying
  rethink: *value notes and tradeable/recoverable caps are the same shape* (C11/C12 over a cap record).
  It collapses three features — cap markets, lost-device recovery, exclusive hand-off — into one reuse of
  the existing note machinery. Surprising because the corpus treats notes (privacy) and caps (authority)
  as *different conserved domains* (`EFFECT-ISA-DESIGN §S3` warns against merging them) — yet *exclusive
  transfer* is exactly nullifier-spend. The resolution: they are the same *mechanism* over different
  *records*, which is fine (the warning was against merging the *conservation laws*, not the *shape*).

- **R2 — The transferability dial is the missing axis that unlocks half the OS.** `GROUND-AUTH §2`
  established disclosure⊥transferability and that transferability is pinned at `public`. This doc shows
  the *same* missing dial gates **migration receipts** (§1), **debug views** (§2), **accountable
  de-anonymization** (§7), and **private name introduction** (§8). One piece of new theory — a
  *verifier-indexed* `Discharged` (`GROUND-AUTH §2.4`, designated-verifier ZK) — is load-bearing for four
  features. **dregg4's highest-leverage new theorem is the transferability dial.**

- **R3 — Everything hard bottoms out on "νF₁⊗νF₂ is not final."** Migration-atomicity (§1), network-fork
  (§2), market-settlement (§3), cross-cell upgrade (§6), recovery-binding (§7) *all* reduce to the
  JointTurn CG-2/CG-5 binding, which `study-category.md` proves is *irreducible* to per-cell soundness.
  The surprising consequence: **the JointTurn binding is not just a consensus detail — it is the single
  theorem that gates every advanced cross-cell OS feature.** Investing in CG-5 is investing in all of
  them at once. This re-prioritizes the roadmap: the JointTurn is the *trunk*, not a branch.

- **R4 — Distributed consistent snapshot = the JointTurn equalizer.** §2. Identifying Chandy-Lamport's
  consistent cut with the CG-5 conservation-balanced downward-closed cut is, as far as the corpus shows,
  unstated — and it means the debugger's snapshot and the JointTurn's atomicity are *the same predicate*.

- **R5 — Agents are FIND, the kernel is VERIFY.** §5. The sharpest one-line statement of safe agentic
  computing the architecture admits: an LLM is *definitionally* the untrusted soundness-only search
  plugin of `cand-A §0`. This reframes "AI safety for coding agents" as a *verify/find seam* property,
  not a sandboxing hack — the kernel's TCB is the wall, the agent has no authority, ever.

- **R6 — The OS has no global clock, so "now" is a cap.** Implied by tier-1 causal-only finality
  (`cand-A §7`, "phones over BLE keep working") + revocation-recency-floor (§7): there is no global
  time, so freshness/expiry/recency are all *relative to what a vat has learned*. The rethink: **time is
  not ambient — a "current epoch" assertion is itself a witnessed fact (a beacon cap)**. This is why
  `EFFECT-ISA-DESIGN §B-#6` flags beacon/VRF as a possible primitive. Surprising because most OSes assume
  a clock; dregg4 must treat freshness as an authority-gated observation.

- **R7 — The debugger and the hot-patcher are one primitive (fork-on-program).** §6. Forking on the
  *input stream* is time-travel debugging; forking on the *program* is hot-patch; both are `cand-A §6`
  fork. A single "fork the unfold, diverge one coordinate (input | program | schema), merge under
  attenuation" primitive subsumes debugging, hot-patching, A/B-testing of cell rules, and speculative
  agent branches (§5).

---

## 10. Ranked shortlist

Two rankings, per the brief: **most promising** (leverage × deliverability) and **most surprising**
(novelty × "not yet considered"). Each row notes its dominant face and the one thing it needs.

### A. Most promising (build-order-aware)

| # | Feature | Why it ranks | Dominant face | The one thing it needs |
|---|---|---|---|---|
| 1 | **Multi-agent collaboration on untrusted code (§5)** | THE use case (`REORIENT §0`); *mostly integration* of existing pieces (sandbox vat + macaroon caveats + badge verifier + fork-as-sandbox); highest deliverability | CAVEATS (the agent's c-list IS its whole authority) | a vat-sandbox agent harness wiring existing code |
| 2 | **The transferability dial / designated-verifier mode (R2, §7-dial)** | one new theorem unlocks migration, debug, de-anon, private-naming (4 features) — highest *leverage* | ATTESTATION (the missing second dial) | verifier-indexed `Discharged` + a DVZK companion circuit |
| 3 | **Cap-as-note exclusive transfer (R1, §3/§7)** | unifies markets + recovery + hand-off into a reuse of CORE C11/C12; small new primitive, big payoff | EFFECTS (C12 nullifier-spend over a cap record) | the exclusive-transfer JointTurn + cap-nullifier set |
| 4 | **Networked time-travel debugger (§2)** | single-cell case is a *theorem already* (`cand-A §5`); the lift is a consistent-cut = CG-5 identification | EFFECTS (pure runtime-theorem, no new effect) | the consistent-cut-as-JointTurn theorem + inspection cap |
| 5 | **Live cell migration (§1)** | mechanism exists in Rust (`migration.rs`), theorem exists in Lean (re-seed); connect them + migration-as-attenuation | EFFECTS (ρ_out∘ρ_in over the c-list) | connect FSM↔re-seed; continuation-serialization (hard) |
| 6 | **Object-capability shell + petname nameservice (§8)** | lowest-theory, highest-ergonomics; petnames are the *correct* rethink; mostly DSL-userspace | CAVEATS (read/write-gated petname cell) | a petname CellProgram template + cand-D REPL |
| 7 | **Capability leasing/markets (§3)** | leasing *already* the recommended revocation strategy; clearing is the existing FIND-plugin; markets-proper are app-layer | ATTESTATION (public settlement) | clearing-as-FIND plugin + settlement JointTurn |
| 8 | **Revocation/recovery under partition (§7)** | a *theorem about a bound*, mostly honest-already; recovery = R1 reuse; the new part is accountable de-anon | CAVEATS (negative-discharge gate) | non-membership circuit + designated de-anon (=#2) |
| 9 | **Cross-cell live upgrade / hot-patch (§6)** | single-cell anti-brick exists; cross-cell is JointTurn-bound; schema-DAG merge is open research | EFFECTS (C7 set_program, no new effect) | JointTurn-lift + schema lens (open) |

### B. Most surprising (novelty × not-yet-considered)

| # | Rethink | The surprise |
|---|---|---|
| 1 | **A tradeable/recoverable capability is a note (R1)** | the corpus *warns against* merging notes and caps — yet exclusive transfer *is* nullifier-spend; the mechanism unifies what the conservation-law warning kept separate |
| 2 | **Everything hard is the JointTurn binding (R3)** | migration, network-fork, markets, upgrade, recovery all reduce to CG-5; the binding is the *trunk* of the OS, not a consensus branch — re-prioritizes the whole roadmap |
| 3 | **Distributed consistent snapshot = the JointTurn equalizer (R4)** | Chandy-Lamport's cut and CG-5 atomicity are the *same predicate* (downward-closed ∧ conservation-balanced) — debugger and atomicity unified |
| 4 | **Agents are FIND, the kernel is VERIFY (R5)** | recasts safe agentic coding as a verify/find-seam property, not a sandbox hack: the agent has *zero* authority by construction |
| 5 | **The transferability dial unlocks 4 features (R2)** | one over-looked axis (`GROUND-AUTH §2`) is the common blocker for migration/debug/de-anon/naming — the absence is more load-bearing than it looks |
| 6 | **There is no global clock — "now" is a cap (R6)** | freshness/expiry/recency are authority-gated observations, not ambient; a beacon is a capability |
| 7 | **Debugger = hot-patcher = one fork primitive (R7)** | fork-on-input, fork-on-program, fork-on-schema are one operation; debugging and hot-patching are the same theorem |

---

## 11. The build-order spine (so dregg4 doesn't start at the front-end)

Honoring `REORIENT §5` (build the living cell first) and `cand-D §8` (choreography last):

1. **First, the trunk: the JointTurn CG-2/CG-5 binding** (R3) — because migration, debug-snapshot,
   markets, upgrade, recovery all bottom out on it. This is `study-category.md`'s irreducible hypothesis;
   making it solid is the single highest-leverage investment.
2. **Then the two dials as theory:** the transferability/designated-verifier `Discharged` (R2, the new
   axis) and the cap-as-note exclusive-transfer (R1, reuse of C11/C12).
3. **Then the runtime-theorem features that are nearly free:** the single-cell debugger (`cand-A §5`,
   already a theorem) and single-cell migration (connect `migration.rs` ↔ re-seed).
4. **Then the integration product:** the multi-agent sandbox (§5) — wiring existing caveats + fork +
   badge verifier into an agent harness. This is the deliverable that *demonstrates the OS*.
5. **Then the lift to cross-cell:** networked debugger (consistent cut), cross-cell upgrade, markets,
   recovery — all consuming the trunk from step 1.
6. **Last, the surface:** the choreography front-end (`cand-D`) and the ocap shell/petname nameservice —
   the developer/agent experience, built on everything below.

**The discipline (REORIENT §6, restated for dregg4):** crypto-soundness never merges into the Lean law
(the §8 caveat); the transferability dial's DVZK is a *circuit obligation*, the verifier-indexed
`Discharged` is the *Lean law*. Markets'/debuggers' search engines are *untrusted FIND plugins* — the TCB
never grows. And the honest bounds stay bounds: revocation has a recency floor, cross-disjoint-group
commit blocks under partition, distributed cycle-GC is out of scope. Design *around* them; do not "fix"
them.

---

*A closing quatrain, since the egg is hatching into an OS:*
*The local theorem proved the cell can fork, can fold, can rest — / the network asks: can many do it
bound, and pass the test? / One dial for "to whom," one note for "now yours, not mine," / and the
JointTurn trunk holds all the branches in one line.* 🐉🥚
