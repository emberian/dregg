# Decisions — ZK recursion/PCS rollup (Path B, reconciled)

**For:** the rebuild-driving agent (holds `docs/rebuild/00-synthesis.md`, `pdfs/discoveries.md`).
**What this is:** the reconciliation of **nine** decision/study memos — the 5 `DECISION-*.md` (engineering zoo) and the 4 `PATHB-*.md` (Path-B research) — plus the user's three relaxations (code not precious; pre-quantum-interim OK if a PQ path exists; the p3/kimchi stack is **partial, under-integrated, never audited** — treat as green-field). It supersedes the conservative verdict in `DECISION-recursion-strategy.md` where the relaxations change it, and records the honest journey: **we accepted Path B, then the research relocated it.**

Tags: `[G]` grounded-in-paper · `[C]` grounded-in-code · `[F]` forward-design · `[T]` theorizing.

Source memos: `DECISION-{recursion-strategy,folding-variants,proximity-pcs,field-and-soundness,recursion-feasibility-lookups}.md`; `PATHB-{mina-proofsystems-study,accumulation-abstraction,pq-hashnative-track,coinductive-rejuvenation}.md`.

---

## 0. TL;DR — the through-line

1. **The soundness-critical path is NOT recursion.** It is making the **per-turn proof step-complete** (`Conservation ∧ Authority ∧ ChainLink ∧ ObsAdvance`) + the guarded receipt-chain + the log. This is bounded, recursion-layer-independent, and *the* priority. Coinductive soundness then holds as a bisimulation (`PATHB-coinductive-rejuvenation` [G/T]).
2. **Succinct-unbounded recursion is a separate, deferrable feature** (teleport / late-join / audit), not a soundness requirement. Don't let it block the critical path or leak into the Lean law.
3. **Keep the leaf prover: FRI over BabyBear/Poseidon2** [C]. Plan a later swap **FRI → WHIR** to cut the recursive-verifier cost (`DECISION-proximity-pcs` [G]).
4. **Put recursion behind ONE swappable `RecursionBackend` trait now** (`MAX_DEPTH: Option`, `needs_cycle: bool`; **never add an `additive_combine` method** or you fork into two IVC layers) — this is the PQ-migration hinge and the only no-regret structural move (`PATHB-accumulation-abstraction` [G]).
5. **The recursion-layer *impl* is a genuine toss-up, and it's deferrable** behind that trait. Interim realization = the **~80%-built Pickles/IPA Halo-accumulation port** (pre-quantum, cheap per-step, coinductively clean, audited upstream). PQ target = **lattice IVsC / lattice folding**. Hash-native **recursive-STARK** is the alternative primary *if* two measurements come back favorable.
6. **`prove_full_turn` → `HidingFriPcs`** for ZK; **LogUp** for range/auth; never merge crypto-soundness into the Lean law (`DECISION-recursion-feasibility-lookups` [C/G]).
7. **The unaudited stack is the real risk.** `soundness_tests.rs` tests only AIR-witness rejection — nothing at the PCS/Fiat-Shamir layer, where Orion & Gemini broke. Add the adversarial checklist (`DECISION-field-and-soundness` [C/G]).

---

## 1. The reframe (why the conservative verdict moved)

`DECISION-recursion-strategy` concluded "STARK-native recursion + bounded aggregation, stay BabyBear," resting on three pillars the user removed:
- "must be PQ" → eliminated the folding line. **Relaxed:** pre-quantum-interim OK with a PQ path → folding/accumulation reopened.
- "already in-tree, don't rewrite" → **moot:** code isn't precious, written in a week.
- "[C] confirmed working" → **the stack is partial/unaudited.** The memos' "it works, finish the wiring" = "scaffolding exists." There is no trustworthy baseline to preserve.

Then the Path-B research delivered the actually-decisive correction: **the recursion layer was never the soundness question** (§0.1–0.2). That subsumes the Path-A-vs-B fight — both are *feature* choices, made behind a trait, off the critical path.

---

## 2. Coinductive soundness (the keystone, `PATHB-coinductive-rejuvenation`)

- A live cell is **codata** — an element of the final coalgebra `νF`, `F X = Obs × (AdmissibleTurn ⇒ X)` (Moore/DFA coalgebra shape) [G/T].
- The proof structure is the **nested fixpoint** `Cell = νC. µI. StepProof I × (Turn ⇒ C)` (Danielsson–Altenkirch stream-processor): **bounded per-turn proof = the inductive inner-µ; the unbounded life = the coinductive outer-ν.** Bounded depth is *correct here*. The user's "bounded = fixed pasts" worry is **refuted** — but the real failure mode of a *step-incomplete* proof is worse than "sees only a past": it **"permits a drifting future"** (a chain that locally type-checks while slowly leaking `Σ_k`), because coinduction makes a non-contractive step's failure *unbounded*.
- The guard = the `previous_receipt_hash` link = Birkedal's `▶` ("later") modality (head now, tail later) → productive, uniquely-solved corecursion [G/T].
- **Theorem shape:** soundness = a **bisimulation** carrying `StepInv` to the Lean golden-oracle Spec, and it holds **iff each step attests the complete `StepInv = Conservation ∧ Authority ∧ ChainLink ∧ ObsAdvance`.**
- **Metatheory consequence:** state the vat-boundary law and conservation **coinductively** (`TurnCoalg`, a coinductive `Sound`/`IsBisim`, `theorem sound_of_step_complete`, a coinductive `BoundaryRespecting`) — covers non-halting cells, collapses "forever" to one guarded step, types the chain-guard as `▶`, and matches the §9 differential-oracle contract. Don't state it inductively over `List Turn`.
- **The urgent audit (top open item):** is the live AIR *actually* step-complete? Memory flags "intent predicates unenforced," "graph-folding flat," and `discoveries.md` flags auth-checked-outside-the-proof. **If not step-complete, the soundness theorem does not yet hold — and the fix is step-completion, not more recursion.** This is the single highest-priority finding in the whole swarm.

---

## 3. The layered architecture (what to build)

```
            ┌─ Rejuvenation: re-prove-from-log (cross-vat) │ controlled-malleability (intra-vat)
            │
  Feature ──┤  Succinct-unbounded history  [DEFERRABLE, not soundness]
  layer     │     via RecursionBackend trait (swappable):
            │       interim:  Pickles/IPA Halo-accumulation  (pre-quantum, ~80% built)
            │       PQ target: lattice IVsC / lattice folding (Neo/SuperNeo/Lova)
            │       alt:       recursive-STARK (hash-native)  [gated on 2 measurements]
            │
  Critical ─┤  Per-turn STEP-COMPLETE proof  = Conservation ∧ Authority ∧ ChainLink ∧ ObsAdvance
  path      │     + guarded receipt-chain + retained log   ⇒  coinductive soundness
            │     ZK via HidingFriPcs · range/auth via LogUp
            │
  Leaf ─────┴─ FRI over BabyBear/Poseidon2   (→ WHIR later, to cheapen the recursive verifier)
```

- **Leaf prover — keep FRI/BabyBear** [C]; migrate to **WHIR** later (univariate+multilinear, ~2.1–2.5× fewer verifier hashes → directly shrinks any recursion circuit). STIR is the fallback. Stay on the prime field; Binius/lattice-field only past explicit thresholds (`DECISION-field-and-soundness` [G]). Re-derive query counts (don't inherit `num_queries=50`; reconcile the `plonky3_prover` 50/blowup-3 vs `stark.rs` 80/blowup-4 disagreement and set a soundness-bit target).
- **Critical path — step-complete per-turn proof.** The 6-clause auth-in-proof statement (key→delegation→policy→effect-fold→replay→cell-root, `discoveries.md`) + `ObsAdvance`. Range/underflow + small auth/permission sets → **LogUp** (FRI-native running-sum column; *not* Lasso, which is multilinear/sumcheck — impedance mismatch) [C/G]. ZK → port `prove_full_turn` onto **`HidingFriPcs`**; hard-rule-out FFT-type quotient splits (Haböck/Al-Kindi footgun) [G].
- **Feature layer — recursion behind the trait.** `RecursionBackend` (superset of `AccumulationScheme`, because the recursive-verifier impl is unbounded-but-not-an-accumulation-scheme). Quarantine the homomorphism leak in `MAX_DEPTH: Option<u64>` (`None`=unbounded; `Some(d)`=hash-spot-check) + `needs_cycle: bool`. One IVC/orchestration layer; migration = `Box<dyn RecursionBackend>` swap. **Do not add a homomorphism-specific method** (e.g. `additive_combine`) — that's what would split it into two layers (`PATHB-accumulation-abstraction` [G]).

---

## 4. The recursion-impl toss-up (deferrable; user's call when it comes due)

Both candidates are **unaudited** and rest on **heuristic Fiat-Shamir** (so neither is a soundness downgrade vs the other, nor vs Pickles).

| | Pickles/IPA Halo-accumulation | Recursive-STARK (FRI-verifier-in-circuit) | Lattice (Neo/SuperNeo/Lova) |
|---|---|---|---|
| PQ? | ✗ pre-quantum (Pasta) | ✓ | ✓ |
| hash-native? | ✗ | ✓ | ✗ (Ajtai/SIS) |
| succinct-unbounded? | ✓ (Halo defer-MSM, constant/step) | ✓ (Plonky2 ~43 KB) [G] | ✓ |
| per-step cost | cheap (defer the MSM) | **unmeasured** — FRI-verify-in-circuit is the expensive thing | low (SuperNeo) [G] |
| built today | **~80%, "OPERATIONAL"** (`backends/mina`, ~21k LOC; `stark_in_pickles.rs`) [C] | partial; **in-AIR-Merkle gap** (CG-1 checks BLAKE3 *natively*, not in-AIR → not truly recursive yet) [C] | unbuilt; months-old, unaudited [G] |
| coinductive fit | **strong** — Halo deferral *is* the `▶` productivity guard; decider = the eventual observation [G/T] | fine | fine |
| audited upstream? | ✓ (Mina kimchi/poly-commitment) | ✗ | ✗ |

- **Note:** "folding" (Nova-style) is **vapor even in Mina** — `arrabbiata`'s decider is `unimplemented!()`. The homomorphic move we'd actually want is **Halo *accumulation* (defer-the-MSM), not Nova folding** [C]. Likewise dregg never built folding (`ivc.rs` is a hash-chain placeholder) [C].
- **Reconciliation of the two camps:** they agree on the *stack* — **FRI/BabyBear = leaf prover; the recursion layer sits above it** (`stark_in_pickles.rs`: STARK → Kimchi-verifier-circuit → constant-size wrap). "Folding on FRI" stays impossible.
- **Recommendation:** **defer this choice; build the trait + the interim Pickles impl** (fastest route to a *working* unbounded-IVC, since it's 80% built and coinductively clean), and treat **lattice IVsC as the PQ target** behind the same trait. Promote **recursive-STARK to primary iff** two measurements land: **(M1)** FRI-verifier-in-circuit per-step prover cost on degree-7 BabyBear AIRs is acceptable; **(M2)** the in-AIR-Merkle gap is closed (algebraic Poseidon2 Merkle verified *in-AIR*, not native BLAKE3). Until then, "PQ-now/hash-native primary" is aspirational, not real.
- **On the user's "as PQ-now/hash-native as possible":** it's satisfiable *eventually* as the primary (recursive-STARK or lattice-IVsC behind the trait) — but the **honest near-term PQ realization is the leaf** (FRI/BabyBear is already PQ/hash-native); the *recursion layer's* PQ-ness is the deferred part. Don't pay the Pickles-pre-quantum cost on the critical path — it's only the interim recursion-feature impl.

---

## 5. Rejuvenation (grounded — `PATHB-coinductive-rejuvenation`)

`Rejuvenate(Proof, FreshnessCtx)`, two layers, by location:
- **Across a vat boundary / on vk rotation → re-prove (or re-fold) from the retained log.** Always available because log-is-truth; inherits full simulation-extractability / **non-malleability**. The default, and the dual of the deferred-prover.
- **Inside a vat → controlled malleability** for `T`-admissible refreshes only (re-randomize, epoch-rebind, Nova-style slack-reset). Faonio–Russo: *linear homomorphism is the only admissible malleability*; Chakraborty et al.'s bounded-depth extractability ("extraction must terminate at a real witness") mirrors the coinductive guard.
- **The safety reconciliation:** you want **non-malleability for soundness** (sumcheck-zkSNARKs-non-malleable 2026/335) **and controlled malleability for rejuvenation** (malleable-SNARKs 2025/311) — resolved by *where*: maul inside, re-prove across. A "degraded" proof (accumulator slack, stale state, old AIR version) re-anchors via re-proof; this composes with schema-upgrade (re-prove under the migrated AIR).

---

## 6. Carried-over engineering decisions (still stand, from the 5 DECISION memos)

- **PCS:** FRI → **WHIR** (verifier-cost-under-recursion); vendoring a WHIR impl is the key external dep [G].
- **Field:** **stay BabyBear + degree-4 ext**; Binius only if >50% prover time is bit-level *and* audited *and* off-nightly; lattice only if structured-PQ mandated [G].
- **Lookups:** **LogUp**, not Lasso [C/G].
- **ZK:** **HidingFriPcs**, ban FFT-type quotient splits on masked paths [G].
- **Aggregation:** depth-1 bounded-fan-in (Ceno/segment shape) for the per-turn obligation set — this *is* the inductive inner-µ; not unbounded IVC [G].
- **Soundness tests:** add the 11-item PCS/Fiat-Shamir adversarial checklist (proximity-gap forgery, distance-preserving randomization, query/blowup downgrade, grinding bypass, challenge-reuse, cross-round consistency, …) tied to Orion-1164 + Gemini-565 [C/G].

---

## 7. Ordered next actions (soundness-critical first)

1. **AUDIT step-completeness** of the live turn proof — is `StepInv` actually all four conjuncts in-circuit? (Memory says intent-predicates/auth/graph-folding are *not* yet.) This gates whether the soundness theorem even holds. **Highest priority.**
2. **Make the per-turn proof step-complete** (auth-in-proof 6-clause statement + effects-fold + conservation + chain-link + obs-advance). Recursion-independent.
3. **Write the `RecursionBackend` trait** (`MAX_DEPTH`, `needs_cycle`, no `additive_combine`); route all IVC through it. No-regret; the PQ hinge.
4. **Add the PCS/Fiat-Shamir adversarial soundness tests**; reconcile the FRI-param disagreement; set a soundness-bit target.
5. **LogUp** for range/auth; **port `prove_full_turn` → `HidingFriPcs`**.
6. **Run M1 + M2** (FRI-verifier-in-circuit per-step cost; close/measure the in-AIR-Merkle gap) → decide the recursion-impl primary.
7. **Finish/harden the interim Pickles recursion** behind the trait (it's 80% built); keep a **lattice-IVsC** spike behind a flag as the PQ target; keep AIRs CCS-expressible as the portability hedge.
8. **WHIR** migration beneath the recursion (differential-test FRI-vs-WHIR; re-derive queries).

---

## 8. Open questions / measurements / audits

- **(M1)** FRI-verifier-in-circuit per-step prover cost on degree-7 BabyBear AIRs (the recursive-STARK-vs-Pickles trigger).
- **(M2)** Is any recursive-FRI verifier truly **in-AIR**, or does CG-1 check BLAKE3 Merkle paths **natively**? (Gates "true recursion vs summary-glue.")
- **Audit:** does the existing mina in-circuit IPA gadget *constrain* vs merely *witness*? Does the live AIR attest the full `StepInv`?
- **`finality.rs`** (from `discoveries.md`): heads summarized by **hash, not vector-clock counters** (BEC §4.2 forgeability).
- **Vocabulary/name check:** the "WARP" label on `linear-time-accumulation-2025-753` (one memo asserted it; I earlier found no "WARP" paper — verify before using upstream).
- **Reconcile** the two coexisting FRI-verifier gadgets; confirm the recursion config can consume a hiding-PCS inner proof.

---

## 9. Net

You accepted **Path B**; the research **relocated** rather than refuted it. Path B's *insight* (a swappable accumulation/recursion backend; homomorphic-now, PQ-later, abstraction preserved) is **right and confirmed real** — but it lives in the **deferrable feature layer**, not the critical path, because **succinct-unbounded recursion is orthogonal to soundness**. The soundness-critical, recursion-independent, highest-priority work is the **step-complete per-turn proof + guarded chain + log** — and the honest near-term answer to "as PQ-now/hash-native as we can be" is that **the leaf already is** (FRI/BabyBear); the recursion layer's PQ-ness is a deferred swap, with lattice-IVsC the cleanest PQ target and the 80%-built Pickles port the fastest interim. The biggest live risk is not the recursion choice — it's that **the unaudited AIR may not yet be step-complete, in which case nothing downstream is sound.**
