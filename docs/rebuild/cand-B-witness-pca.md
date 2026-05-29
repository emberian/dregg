# Candidate B — The Proof-Carrying Turn (Witness/PCA)

> **One-line thesis.** dregg2 is a *verifier*. The trusted computing base is a
> proof-checker plus signature/hash axioms; *everything else* — delegation,
> policy, conservation, ordering-search, intent-matching, schema migration — is
> defined inside **checkable witnesses produced by untrusted solvers**. This is
> Robigalia realized as a slogan: **you trust the proof, not the code.** Run
> anyone's untrusted program; you never execute it on your authority — you check
> the badge it hands you.
>
> Lens / fixed decision: **soundness-by-verification, as the universal principle.**
> The organizing law is the **verify/find seam** (`discoveries.md §1`) lifted from
> "the intent matcher is bounded" to the spine of the whole system. Primary object:
> the **proof-carrying turn** (Appel–Felten PCA + IVC). Soundness-critical path:
> **step-completeness** (`decisions.md §0/§2`). Recursion is deferred behind a
> `RecursionBackend` trait. This is the *witness* projection of the turn-generator
> (`00-synthesis.md §1`), driven all the way to its conclusion.

---

## 0. Why this candidate, distinctly

The proof-spine exploration (`03-spine-proof.md`) said "proof is truth — for
validity, never for canonicity," and concluded with *two coupled spines* (proof +
ordering). Candidate B **keeps that verdict** but re-centers the architecture on a
sharper, more defensible claim than "proof is truth": **soundness is by
verification.** The difference is the whole design:

- "Proof is truth" tempts the system into thinking the *proof* decides everything
  and then trips over forks, genesis, and binding (`03 §10.3–10.6`).
- "Soundness by verification" says only this: **the verifier's `accept` is the
  one trusted judgment; producing the thing it accepts is an untrusted search.**
  It does not claim the proof picks the canonical history — only that *every*
  history-element the verifier blesses is sound. Ordering is then, honestly, a
  *separate untrusted search emitting a checkable witness* — not a "second spine,"
  but **the same seam at a different altitude** (find-an-order is intractable;
  verify-an-order is cheap). This is the unification the proof-spine missed.

Distinctly-dregg, then, are two things this candidate makes first-class:

1. **Soundness-by-verification as a *universal* operating principle** — applied
   uniformly to auth-path search, intent-match, ordering, schema-migration, and
   handler-selection, each a `…Plugin` emitting a witness the same tiny TCB
   checks. No bespoke trusted subsystem per concern.
2. **The badge as a first-class, transmissible artifact.** A `WitnessedReceipt`
   (= PI + proof) is not an internal log entry; it is the *product*. "Collaboration
   = exchanging badges." The agent/zkRPC face (a settled-call return wearing a
   badge) is the headline application, not an afterthought.

---

## 1. The ontology

Six nouns. The first is trusted; the rest are untrusted things the first checks.

| Noun | What it is | Trusted? |
|---|---|---|
| **Verifier (the vat TCB)** | a proof-checker + signature/hash axioms + the `Verify P w : Bool` decision procedure. The *only* trusted thing. A vat holds one. | **YES — and nothing else is.** |
| **Witness** | the private input to a morphism: trace, secrets, full-width fields, the cap-chain, the chosen handler, the chosen fill, the chosen order. **Produced by untrusted solvers.** | no |
| **Badge** (`WitnessedReceipt`) | PI + proof; the transmissible, self-attesting export of a turn. The product. The membrane's emission. | n/a (verifier-checked) |
| **Turn proof** | a single PCA statement that a valid morphism exists for *this* canonical turn — the **step-complete** conjunction of §3. | n/a |
| **Cell** | the equivalence class of valid proof-chains agreeing on a commitment (`03 §3.1`). State = `NEW_COMMIT` of the latest badge. | no (a cache/cap) |
| **Ledger** | a **memo table** `turn_id → badge` for discovery/performance, with *no opinion* on canonicity (`03 §3.2`). | no |

The **Predicate ⊣ Witness Galois/Heyting connection** (`discoveries.md §3.4`) is
the ontology's spine: `Verify` is the right adjoint (cheap, decidable, posetal);
`Find` is the left adjoint shadow (intractable). A gate is *defined* by its
predicate; *satisfied* by an emitted witness.

---

## 2. Cell / turn / cap / proof under this lens

- **Cell = "the equivalence class of valid proof-chains agreeing on a
  commitment."** Bytes are a cache; the log of *witnesses* (morphisms, not
  byte-diffs) is the persistence layer; replay re-derives. `CellLifecycle` /
  `FieldVisibility` are *attested* properties (sealed/active because the latest
  badge says so), with `FieldVisibility` = the public/witness split of §4.

- **Turn = the rollback handler that also emits the witness at the vat boundary**
  (`discoveries.md §3.5`). Plotkin–Power §6.8: a turn holds its outgoing effects
  until commit. Commit = replay-the-held-list + emit the badge; abort = discard =
  conservation-preserving refund. `await` is **not** the turn's free model —
  continuations are the one non-algebraic effect — so await is *two* layers: a
  gate-engine (algebraic handler / `Verify`) + a one-shot continuation-capture
  primitive. The deferred-prover keystone *is* "the commit-replay handler emits
  the witness lazily, at the crossing."

- **Cap = a delegation-chain whose validity is attested *in-circuit*, not checked
  by the executor.** The **CDT proves *permission* (de-jure), not *authority*
  (de-facto)** (`discoveries.md §3.6`, Miller Table 8.1): a caretaker/forwarder
  can make the static cap-graph lie about real authority. So the cap-chain witness
  certifies "you were *permitted*"; what a cell can *eventually* do is behavioral,
  **recovered from the log** — "truth is the log, not the cap-graph." The badge
  carries the permission proof; the log carries the authority. `LinearityClass`
  rides on the cap; conservation (§3) keeps it honest.

- **Proof = the PCA witness projection of the turn-generator.** Composition of the
  four chips (§3) into one statement per turn; turns fold into strands (deferred
  recursion, §5).

---

## 3. The metatheory entry — step-complete PCA, and the seam as law

Metatheory (`./metatheory`, Lean4) entry for this candidate = **PCA + a
step-complete per-turn proof + `no_general_matcher` + the witness-emitting-solver
contract.**

### 3.1 The step-complete turn statement (the soundness-critical path)

`StepInv` (`decisions.md §2`) is the conjunction the per-turn proof must attest —
and **soundness holds *iff* every step attests all of it** (a non-contractive step
"permits a drifting future" under coinduction, worse than "sees only a past"):

```
StepInv  =  Auth ∧ Conservation ∧ ChainLink ∧ ObsAdvance
```

The **6-clause auth-in-proof** statement (the "Auth" conjunct, `discoveries.md §5`,
`decisions.md §3`), each clause a cryptographic step, all cross-PI-bound to the
canonical turn:

```
  key  →  delegation  →  policy-entailment  →  effect-fold  →  replay  →  cell-root
```

- **key**: a PI root authority commitment (owner key / cap root / reflected seL4
  cap-handle hash) heads the chain.
- **delegation**: each attenuation = a real signature (`schnorr_air` /
  `native_signature` exist) + the order relation `child ⊆ parent`.
- **policy-entailment**: the Mina-`spec_eval`-shaped permission lattice / Garg
  `says`/`controls` fragment — **kept decidable in-circuit**; delegation-*path*
  search is pushed to the untrusted prover (the seam, one level up).
- **effect-fold**: `EFFECTS_HASH` **re-derived in-circuit** as a rolling Poseidon2
  absorb over the canonical-DFS effect stream — no host-commitment exemption.
- **replay**: bound to `TURN_HASH` / `ACTOR_NONCE` / `PREVIOUS_RECEIPT_HASH` (the
  anti-malleability spine).
- **cell-root**: `OLD_COMMIT` / `NEW_COMMIT`, full-width (4-felt floor, no 32→4
  truncation).

**The second rib — per-asset value-conservation folded *into the proof*.**
Conservation is not a side-check: the headline theorem `conservation_comp` —
**Σ_k is a strong monoidal functor `(TurnCat,⊗,I) → (ℕ,+,0)`, constant on every
non-mint/burn hom-set** (`discoveries.md §3.2`) — becomes a per-`LinearityClass`
sum-check chip on the *same effect-stream rows* the effect-fold absorbs, sharing
the in-proof bus (no cross-PI matching). Invariance (`=`), stronger than a
Coecke–Fritz monotone; mint/burn are explicit typed generators. This is the
clause that makes a badge a *value*-bearing artifact, not just a state-transition
attestation.

### 3.2 The seam, as a theorem: `no_general_matcher`

The metatheory states the universal principle as a reduction and its dual:

- `no_general_matcher`: **`HOU ⪯ GeneralMatch`** (Coq synthetic-undecidability
  style — axiomatize HOU, prove the one reduction). *Finding* a fill / a
  delegation path / a handler / an order is undecidable.
- `firstOrderMatch_decidable`: certifies the tractable fragment (the RingSolver /
  Miller-pattern shape).
- `MatcherPlugin` / `…Plugin` contract: **soundness-by-verification only.**
  Completeness and termination are *explicitly not required* of any plugin. A
  plugin may promise only structured-tractable cases (interval / single-item /
  submodular; Winner-Determination is NP-hard with no PTAS).

### 3.3 The vat-boundary law (the sharp target — LAST)

Stated **coinductively** (a live cell is codata, `νC. µI. StepProof I × (Turn ⇒ C)`;
`decisions.md §2`): the case-split (seL4 integrity lifted) is

- *intra-vat*: positional authorization (`∃ cap ∈ caps`, a mediator slot-read)
  admits the **trivial** witness — no proof needed within one trust-root.
- *cross-vat*: admissibility ⇔ `Discharged P w` (`Verify P w = true`).

The crypto substitution is **literally replacing the positional ∃ with the
decidable verification** — a freely-copyable, verifier-checkable object, no
off-island mediator. Companion `LossyMorphism` theorem: **structural
unforgeability → cryptographic unforgeability, loss = revocation-by-construction**
(Φ⁻¹ needs a trusted minter; PCA recovers public verifiability + richer
predicates, *not* confinement or cheap revocation — a stated loss, not a slogan).
`sound_of_step_complete` is a bisimulation to the Lean golden oracle. **Crypto
soundness of the witness is a circuit obligation — never merged into the law.**

---

## 4. How it nails trustless collaboration (the Robigalia payoff)

- **Run anyone's untrusted code safely.** You never run their code on your
  authority; you accept a turn iff its badge verifies against your tiny TCB. A
  malicious solver can at worst *fail to produce* a valid badge — it can never
  forge `accept`. "Developers collaborate on untrusted code without getting
  hacked" = the verify/find seam: their code is a witness-emitter; your verifier is
  the wall.
- **Collaboration = exchanging badges.** Two parties (or two phones over
  Bluetooth) trade `WitnessedReceipt`s. Each verifies the other's strand-head badge
  in milliseconds **without replaying** the other's turns — O(1) verification of an
  O(n) history (the asymmetric prove/verify saving grace).
- **Checkpoint / restore / replay / debugger, native.** The retained **log is the
  inputs** (houyhnhnm orthogonal persistence). Checkpoint = a commitment; restore =
  re-derive bytes from witnesses; replay = re-run the held-effect list. The
  **deferred-prover** *is* checkpoint-export: prove-from-the-kept-log lazily at a
  boundary. **Rejuvenation** (`decisions.md §5`): across a vat / on vk-rotation →
  *re-prove from the log* (non-malleable, always available); inside a vat →
  controlled malleability (re-randomize, epoch-rebind). A degraded/stale badge
  re-anchors by re-proof; this composes with schema-upgrade (re-prove under the
  migrated AIR). The debugger reads witnesses, not opaque bytes.

---

## 5. Tradeoffs (honest)

- **Prover cost.** Auth-in-circuit (each signature = thousands of non-native
  constraints) + in-circuit effects-fold dominate; a complete turn proof with a
  short cap-chain is plausibly seconds on a laptop, tens of seconds on a phone;
  deep chains / many-cell aggregation push to minutes (`03 §10.1`). Mitigation:
  asymmetric verify (phones only verify gossiped heads) + batching — but batching
  **delays truth**, so provisional state is allowed only if **never gossiped** and
  **never authorizes a downstream turn** until proved (proof at every *boundary*,
  not every keystroke).
- **The step-completeness audit is the real risk.** Soundness holds *only if* the
  live AIR attests **all four** `StepInv` conjuncts in-circuit. Memory/`discoveries`
  flag auth-checked-outside-the-proof, intent-predicates-unenforced, graph-folding-
  flat. **If not step-complete, nothing downstream is sound** — and the fix is
  step-completion, not more recursion (`decisions.md §7`, the highest-priority
  finding in the whole swarm).
- **What is NOT in the TCB (the whole point, stated as a cost).** No solver, no
  matcher, no ordering engine, no executor, no policy interpreter is trusted —
  which means *none of them get to be a fast happy-path that bypasses the verifier.*
  Every concern pays the witness-emit + verify tax. The TCB is a proof-checker +
  signature/hash axioms + `Verify`; **crypto soundness of the proof system itself
  is the irreducible trust** (the unaudited PCS/Fiat-Shamir layer is where Orion &
  Gemini broke — needs the adversarial checklist).
- **What the proof cannot do — stated, not hidden.** PCA gives *validity*, never
  *canonicity*. Fork (free, no permission), genesis (no proof-only bootstrap — a
  trusted setup, a reflected seL4 cap, or a quorum act), and binding-PI-canonicity
  are all "which valid history is canonical?" = **ordering**. Under this candidate,
  ordering is **not exempt from the principle**: it is one more untrusted
  find-an-order search emitting a checkable order-witness (I-confluence on tier-1;
  the FinalityRule `admits` check as a soundness gate; `Σ_k` tier-independent,
  pruning the order search only). The verifier never blesses an order it can't
  check — but it also never *chooses* one. The IVC/`RecursionBackend` for
  succinct-unbounded strand-heads is **deferrable**: bounded depth = security
  param, no unconditional/arbitrary-depth/NP-witness IVC.

---

## 6. What's distinctly dregg2

1. **Soundness-by-verification as the universal principle** — one seam (verify
   cheap / find intractable) applied uniformly to auth, intent, ordering, schema,
   and handler-selection, each a witness-emitting plugin checked by one tiny TCB.
   Not "proof is truth" (which over-claims canonicity) — *soundness is by
   verification* (which claims exactly, and only, what holds).
2. **The badge as a first-class transmissible artifact** — `WitnessedReceipt` is
   the product, not a log row; collaboration is badge exchange; the agent/zkRPC
   **settled-call return-projection** (a tool result wearing a verifiable badge) is
   the flagship face.
3. **The two ribs folded into the proof** — auth-in-proof (rib 1) *and* per-asset
   value-conservation as a strong-monoidal-functor sum-check (rib 2) — so a badge
   attests *permission* and *value* in one step-complete statement.
4. **Verifier-TCB minimalism as the explicit security argument** — the
   l4.verified analogue: the trusted surface is a proof-checker + axioms, and the
   vat-boundary law (intra-vat trivial witness / cross-vat `Verify P w`) is the
   one theorem the architecture rests on.

---

## Abstract (≤250 words)

Candidate B makes dregg2 a **verifier**. Its trusted computing base is a
proof-checker plus signature/hash axioms and one decision procedure,
`Verify P w : Bool`; *everything else* — delegation, policy, conservation,
ordering, intent-matching, schema migration, handler choice — is defined inside
**checkable witnesses produced by untrusted solvers**. The organizing law is the
**verify/find seam** promoted to a universal principle: every *gate* is cheap to
check; every *search* is intractable and must be an untrusted plugin emitting a
witness. **Soundness is by verification, never by construction; the TCB is the
verifier, never the solver.** The primary object is the **proof-carrying turn**
(Appel–Felten PCA + IVC); soundness rests on **step-completeness** — each turn
proof attests `Auth ∧ Conservation ∧ ChainLink ∧ ObsAdvance`, with auth folded in
as a 6-clause derivation (key→delegation→policy→effect-fold→replay→cell-root) and
per-asset value-conservation folded in as a strong-monoidal-functor sum-check (the
"second rib"). A cell is the equivalence class of valid proof-chains agreeing on a
commitment; the ledger is a memo table. This realizes Robigalia — run anyone's
untrusted code safely (you trust the proof, not the code; collaboration = exchanging
**badges**), with checkpoint/replay/rejuvenation riding the retained log via
re-prove-from-log. Metatheory: PCA + step-complete proof + `no_general_matcher`
(HOU⪯GeneralMatch) + a soundness-only plugin contract; the vat-boundary law
replaces the positional ∃ with decidable verification. Honest costs: heavy prover,
a load-bearing step-completeness audit, and that the proof gives validity, never
canonicity — so ordering is itself an untrusted, witness-emitting search.

---

## 7. The keys-as-caps token layer — proof-chain *or* cheap non-proof credential?

The keys-as-caps axioms (the vat-boundary law, `discoveries.md §4–5`) land concretely on
`Authorization::Token { encoded, key_ref, discharges }` + `TokenKeyRef`
(`turn/src/action.rs:422–450`) — the carriers by which authority crosses the vat boundary as a
transmissible object. The membrane split:

- **biscuit** (`eb2_…`, `TokenKeyRef::BiscuitIssuer`) = **cross-vat**, public-key-verifiable offline
  by anyone (UCAN-class attenuation-chain = keys-as-caps as a provenance log).
- **macaroon** (`em2_…`, `TokenKeyRef::CellScopedMacaroon`) = **intra-vat**, cell-scoped HMAC
  (`discoveries.md §6.3`: not third-party-verifiable, so never cross-domain).

The caps↔keys conversion is the same here as everywhere: positional caps-as-caps inside a trust
root; `ρ_out` serializes to a biscuit/macaroon key-as-cap on exit; `ρ_in` re-mints; both lossy and
**attenuation-only** (the Φ forgetful functor dropping confinement + revocable forwarders, §3.3's
`LossyMorphism`).

**Under THIS candidate's center, the token layer poses a live question this candidate alone must
answer: is `Authorization::Token` *subsumed* by the PCA derivation, or kept as the cheap NON-proof
fast-path credential?** Candidate B's whole claim is "the proof-chain IS the credential" — the
6-clause derivation (key→delegation→policy→effect-fold→replay→cell-root) already *is* a verifiable
attenuation-chain badge, making the biscuit a *degenerate witness* whose `Verify P w` is a signature
check rather than a STARK check. The honest resolution: **keep the token as the cheap non-proof
credential on the verify/find seam's cheap side** — a biscuit is the O(signatures) fast-path the
same tiny TCB checks, escalating to a full PCA badge only when a clause needs proof (policy
entailment over private state, conservation). Both are witnesses; they differ only in cost.

**Discharge is where the token layer and the await family literally merge.** A 3rd-party caveat is
*the* `Await` engine of the universal gate: the discharge **gateway** = the named resolver, the
discharge **token** (`discharges`) = the resolution, `bindForRequest = H(M'.sig :: M.sig)` = the
binding-site (`discoveries.md §4`, isomorphic to `ConditionalTurn`). In a verifier-centric system
this is exact: a discharge token is a *witness for a deferred clause*, checked by the same `Verify`.

**Revocation is the one consensus seam** — a **negative discharge**, a STARK non-membership proof
against an attested revocation root (the de-facto dual of the path-proof), the only globalism, and
only **root-epoch agreement**. It is the clause `Verify` cannot evaluate purely locally.
