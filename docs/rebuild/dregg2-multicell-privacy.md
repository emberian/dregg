# dregg2 — Multi-cell (the JointTurn) + Privacy

> The load-bearing design: without atomic multi-cell turns there is no emergent-consensus
> distributed zkRPC agent coordination. Grounded in the multi-cell reasoning + `study-mina-relink.md`
> (the proven Mina account-update-forest precedent) + `study-{consensus,category,gc}.md`.
> Tags [G] grounded-in-paper/code · [C] in dregg code · [F] forward-design.
> (Written directly during a transient API overload; the Lean `Boundary.lean` edits in §5 are
> spec'd here, to apply when the prover recovers.)

## 1. The JointTurn — the multi-cell primitive (= Mina's `zkapp_command` forest, re-grounded)

A turn over cells `C₁…Cₙ` is reified as a **JointTurn**, the *equalizer object* the category demands:

- **Joint validity = three bound parts.** (1) a **shared turn-identity** every participant's per-cell
  step-proof commits to in its public inputs (= Mina's `account_updates_hash`; the **CG-2 pullback** —
  cell *i*'s proof is valid *only* as part of *this* JointTurn, never replayed solo/elsewhere) [C: `aggregate_bilateral_prover`]; (2) per-cell step-proofs (each `CellProgram`/coalgebra admits its share);
  (3) the **cross-cell conservation-over-commitments** N-lateral aggregate (**CG-5**, γ.2
  `bilateral_aggregation_air`). Per `study-category`, `νF₁⊗νF₂` is **not** final, so **cross-cell
  soundness is irreducible to per-cell** — the CG-2⊗CG-5 binding is an **explicit HYPOTHESIS, never
  `per-cell-sound ∧ per-cell-sound`** (the trap that would make the Boundary module unsound). CG-5 is the
  *price of having no global ledger* — Mina never needs it (one ledger ⇒ one namespace).

- **Atomicity is a PROOF property, not a live coordinator** [G, ADOPT from Mina]. Mina's shape:
  `will_succeed` (prophecy) + an **in-circuit cumulative AND** (`success`) over all updates + a commit.
  So all-or-none is *proven by the aggregate*, not run by a 2PC. **Divergence:** Mina's *single global
  durable write* becomes **per-cell tier-local commits gated on the *same* shared aggregate proof** —
  the proof is shared, the finality is per-cell.

- **Emergent consensus** [F]: ad-hoc, per-turn, **n-lateral, no global quorum**. Finality = the **join
  (max) of participants' tiers**; a tier-3-touching JointTurn inherits BFT stall on all its writes for
  that turn. Consensus is invoked **only on contention**: I-confluent joint ops commit causally;
  **coupled-value ops** (Σ=0 across cells) are *not* I-confluent and escalate to the **COD sum-predicate
  over the whole concurrent set** (`coord/shared_budget.rs` [C]) **on actual overspend**. Honest:
  coupled-value multi-cell is *never* tier-1.

- **Token-owner-as-co-participant** [G, ADOPT from Mina `may_use_token`/caller frames]: a turn moving
  asset A includes **asset-A's owner-cell as a participant**. This grounds the per-asset value rib in the
  multi-cell frame — multi-asset conservation = the asset owners co-sign the JointTurn's equalizer.

- **zkRPC + multiagent coordination ARE multi-cell JointTurns** [F]: a toolcall = a **2-cell JointTurn**
  (`agent-cell ⊗ service-cell`); call + return + **badge** = the joint aggregate proof bound to the
  shared turn-id; M-agent coordination = N-cell JointTurns. *Nailing multi-cell **is** nailing
  emergent-consensus distributed zkRPC.*

## 2. Privacy — three tiers, first-class

- **field** — `FieldVisibility` (Public/Committed/SelectivelyDisclosable) on Preserves Record fields [C].
- **value** — the JointTurn's **conservation equalizer runs over Pedersen commitments** (homomorphic
  `Σ committed = 0` + range), so the cross-cell balance hypothesis is over *commitments*, never cleartext [C].
- **graph** — stealth one-time keys (**unlinkable invocation**), the **ZK-hidden auth-derivation-chain**
  (anonymous delegation), blinded-set membership (authorized-without-revealing-which, holder ∉ PI) [C: W3-D/F].
- **Private predicates = ZK `WitnessedCondition`s inside the `CellProgram`** (the coalgebra admissibility
  map): a cell admits a turn iff a predicate holds *without cell or verifier learning the witness*.
- **The anonymity ⊗ consensus reconciliation** [F, the non-obvious one]: anonymous parties *can*
  participate in a JointTurn that needs ordering + the overspend check — **stealth one-time identities
  order in the group; nullifiers gate contention over the concurrent set without deanonymizing**
  (Zcash-style: commitments/nullifiers public, spender hidden). dregg2's JointTurn **graph-hides the forest
  topology Mina publishes**.

## 3. The anti-brick upgrade clause (the #1 thing the design was missing) [G, ADOPT from Mina `permissions.ml:77`]

dregg2 *will* swap the recursion backend / AIR encoding (§7: depth-as-security-parameter, recursion
deferrable). When it does, **every live `Circuit{circuit_hash}` cell pinned to the old proof system
becomes unverifiable — *bricked*** (the exact failure Mina's `verification_key_perm_fallback_to_signature
_with_older_version` was built to prevent). **Adopt:** `CellProgram`-upgrade gets a **`set_program`
admissibility clause** pinning a proof-system/`AIR_VERSION`; when a cell's pinned version is older than the
live verifier, the upgrade authority **falls back to a signature by the cell's owner** — a verifier
upgrade can never strand a sovereign cell. (dregg2's migration is otherwise *stronger* than Mina's:
transparent + conservative, content-hash-preserving — `study-mina-relink §4`.)

## 4. Inevitable vs contingent (why this isn't "Mina again")

**The forced quartet is a near-categorical-inevitability** (forced by {atomic · conserving ·
decentralized-verifiable · capability-safe}, which is why dregg independently re-derived it):
**atomicity-equalizer ⊕ conservation-functor ⊕ PCA-witness ⊕ attenuation-meet** — plus
**prophecy-then-conjunction atomicity** and the **anti-brick fallback**. These dregg2 **ADOPTS** (the
proven core, much of it the user's own Mina work).

**Mina's contingent L1 choices dregg2 DIVERGES from:** a single **global public totally-ordered ledger**;
a **single durable write**; **eager proving**; **public forest/state**; a **fixed validator set**. dregg2
is the other corner: **local-first, per-cell emergent finality, private, deferred-proven** — *same
morphism-algebra, different ambient category* (the difference is the category you do the algebra *in*, not
the algebra).

## 5. Metatheory deltas (spec for `metatheory/`, to apply when the prover recovers)

- `Boundary.lean`: add a **`JointTurn`** equalizer object — `sharedTurnId` + a **`JointBinding`
  hypothesis** carrying CG-2 (turn-identity pullback) ⊗ CG-5 (cross-side conservation), and
  `joint_sound : (∀i, StepComplete (Cᵢ)) → JointBinding → Sound (JointTurn)` — the binding is a
  **premise, NEVER derived** from the per-cell `Sound`s. Note atomicity = the cumulative-AND prophecy
  property (an invariant on the aggregate, not a coordinator).
- `Authority/Positional.lean`: add `set_program` upgrade admissibility = `AIR_VERSION`-pinned, with the
  `older_version ⇒ signature_fallback` clause as a `sorry`'d lemma (`upgrade_never_bricks`).
- Privacy: the conservation functor's target instance over commitments (a `sorry`'d
  `commitment_conservation`); `FieldVisibility` as the public/witness split already in `Laws.lean`.

## 6. The coordination layer — multi-party · multi-turn · multi-privacy (above the JointTurn)

A JointTurn is *one atomic step*. Real agent coordination — a negotiation, auction, or workflow
(request → subtasks → aggregate → return) — is a **stateful, multi-round, multi-party** interaction: a
structured *composition* of JointTurns over time. The model [G, sessions-as-propositions /
multiparty-session-types; studied in `LEARNINGS-laws-linear-monoidal`]:

- **A coordination = a global type `G` (a choreography)** under **linear** discipline (the *same*
  no-contraction/no-weakening law as conservation). **Projection** `G ↾ p` gives each party its local
  protocol; well-formed projection ⇒ **progress + deadlock-freedom** (the MPST guarantee). This is the
  multi-party-multi-turn safety property.
- **Reified as a cell** [F]: a coordination is a **protocol-cell** whose **`CellProgram` *is* `G`** — its
  admissibility = "is this the next legal action," its state = messages-so-far. Participant cells advance
  it via JointTurns; **the await family connects the steps** (a "receive" *is* a zkpromise/discharge
  awaiting the matching "send"). A coordination is **a cell coordinating cells** — the cell concept
  recursing; no new top-level primitive. Multi-coordination = concurrent protocol-cells, tensored by `⊗`,
  coupling only through shared resources (→ the contention/consensus).
- **Multi-privacy = privacy by projection** [F]: party `p` sees only `G ↾ p`; the global choreography is
  **graph-hidden by the protocol structure itself**, layered with the three tiers (§2). Non-participants
  see nothing; different parties see different fields/values.

### The I-confluent cross-group fragment (escapes the §7-(1) blocking bound, for a real fraction)

Not "all cross-group turns are free" — but **classify each protocol step**. [CORRECTED — `study-choreography`]
**The classifier is NOT the session type.** I-confluence is an *independent third judgement*, orthogonal
to both conservation (linearity, Law 1) and ordering (the session type, Law 2): a **BEC
invariant-confluence analysis over the step's `write-set × cell-state-lattice`** (linear ⇏ I-confluent —
two pool withdrawals; I-confluent ⇏ linear — a monotone counter; CryptoConcurrency shows it reduces from
consensus, so it is a distributed-agreement obligation, not a typing one). dregg2 therefore carries **three
separate judgements** per turn — conservation (linear), ordering (session), I-confluence (invariant-merge).
With that analysis in hand:
- **I-confluent step** (commutative/monotone — append a commitment, add to a CRDT set, post an intent, an
  independent grant): converges regardless of order ⇒ runs **cross-group, partition-tolerant, NO atomic
  commit**.
- **Coupled step** (an atomic Σ=0 settlement): the blocking atomic JointTurn (cross-group blocks under
  partition, §7-(1)).

So a protocol whose steps are *all* I-confluent runs **fully cross-group, partition-tolerant, free** —
covering a large fraction of real coordination (negotiation, accumulation, commit-reveal voting,
intent-posting, discovery); you fall to the beefy mechanism **only at the genuine value-settlement step**,
and the type system tells you the boundary. *This is the honest, buildable form of "cross-group
I-confluent coordination without the beefy mechanism."*

**The full stack:** `CellProgram` (one cell's coalgebra) → `JointTurn` (one atomic multi-cell step =
Mina's forest) → **Coordination** (a multi-party, multi-turn, session-typed choreography reified as a
protocol-cell, with privacy-by-projection and a statically-classified I-confluent fragment).

## 7. Honest open points (the residuals, not papered over)

1. **The deepest one — cross-disjoint-group atomic commit is *blocking* under partition.** Mina's
   atomicity rests on *one* global ledger doing *one* write; dregg2 has no single write-point, so a
   JointTurn straddling **disjoint reference-groups** needs the commit/abort decision to reach all groups.
   **Safety is provable** (the shared aggregate + CG-5 binding); **liveness is not** — this *is* the
   classic distributed-atomic-commit blocking problem (2PC blocks under partition; 3PC/Paxos-commit need a
   shared quorum that disjoint groups *don't have*). Atomic-cross-group ∧ partition-tolerant ∧ live is
   impossible. The only escapes: (a) a shared higher coordinator both groups trust (re-introduces a
   mediator — fine *inside* a vat, not across); (b) restrict cross-group turns to **I-confluent** ops that
   don't need atomicity; (c) accept blocking + timeout-abort for the rare straddling-partition turn.
   *This is the true price of "no global ledger," and it bounds what emergent cross-group coordination can
   promise.* It is a genuine impossibility, not a design oversight — Mina sidesteps it only by **being**
   the one global ledger.
2. **I-confluence ceiling:** coupled-value multi-cell coordination is fundamentally ≥ contention-escalation
   tier — no CRDT-liveness *and* atomic cross-cell value at once (the CAP wall, stated).
3. **Graph-privacy limit:** a one-time identity in the group still leaks *that* a turn happened at time T;
   full unobservability (hiding the turn occurred) needs mixing/PIR — out of scope.
