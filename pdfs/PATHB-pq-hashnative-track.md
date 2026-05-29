# PATH B — The PQ / hash-native recursion track (the parallel constraint)

> **Decision agent verdict (one line):** dregg's PQ-now, hash-native recursion target is **(d)
> recursive-STARK / FRI-verifier-in-circuit (Plonky2/3-style)** — it is the *only* option that is
> simultaneously PQ, hash-native, **succinct-unbounded TODAY**, transparent, and **already in
> dregg's tree** (`plonky3_recursion_impl.rs`, `RecursiveFriAir`). Its soundness is *heuristic
> Fiat-Shamir* — but **so is Pickles'**, so adopting it is not a soundness *regression* vs Path B's
> accepted Mina-reference, it is the *same heuristic at PQ security*. **Fractal** is the same family
> (holographic transparent recursion) but research-grade and still RO-heuristic at recursion;
> **lattice folding (Neo/SuperNeo)** is the genuine "preserve-the-folding-abstraction" PQ target but
> is a **commitment-layer transplant** that is months-old and unaudited. So: **recursive-STARK is
> PQ-now-primary; lattice folding is the watch-list migration that preserves accumulation later.**
> The "homomorphic-now → PQ-later" framing of Path B is **not necessary for unbounded recursion** —
> hash-native unbounded recursion is achievable *now*; it is only necessary if you insist on keeping
> the *folding/accumulator* abstraction specifically.

Legend: **[G]** grounded in a read paper · **[C]** grounded in dregg code/docs (the two DECISION memos) · **[F]** forward design / decision-call.

---

## The options (one paragraph each)

**Fractal (Chiesa–Ojha–Spooner, 2019/1076) — holographic transparent recursion.** [G] Fractal is the
*first* demonstrated post-quantum **and** transparent recursive proof composition. Its insight: recursion
is *simpler for preprocessing SNARKs* (a verifier whose work is polylog in circuit size), and you can get a
PQ+transparent preprocessing zkSNARK by mapping a **holographic IOP** for R1CS into a preprocessing SNARG
in the random-oracle model, then recursing it. It is real, not a sketch — they expressed a SNARK verifier
checking **2 million constraints using only 1.1 million constraints** [G], "the first demonstration of
post-quantum transparent recursive composition in practice." **Cost/maturity caveats:** arguments are
80–160 kB at 128-bit over a **181-bit prime field** [G] (two orders larger than pre-quantum SNARKs);
proving "takes several minutes" [G]; and crucially its security holds in the RO model that is then
**"heuristically instantiated via a cryptographic hash function"** [G] — i.e. its recursion soundness is
*heuristic Fiat-Shamir, exactly like Plonky2/3*. Fractal is the **theoretical ancestor** of dregg's chosen
path, but the *engineering* lineage that productionized this idea (small field, fast recursion) is Plonky2,
not Fractal itself. → **Same family as (d), research-grade instantiation. Not the production target.**

**Recursive STARKs / FRI-verifier-in-circuit (Plonky2, 2022; Plonky3 in-tree) — (d).** [G][C] Each step's
circuit re-executes the inner proof's FRI/PLONK verifier as an AIR; the outer proof attests "the inner
proof verified." Plonky2 swaps PLONK's polynomial test for FRI, encodes the witness in a **64-bit field**
for prover speed, and **"shrink[s] any proof to about 43 kilobytes"** of constant size — i.e. *genuine
unbounded recursion* (300 ms recursive proof on a laptop) [G]. No homomorphic commitment, no curve cycle:
**the only requirement is a hash + a FRI-verifier-as-circuit, both of which dregg already has and ships
default-on** (`p3-recursion`, `RecursiveFriAir`/`FriVerifierGadget`) [C]. The price, named by SuperNeo's
own abstract, is that **"hash-based schemes (e.g., Arc) incur large verifier circuits"** [G] — correctness
is free, *prover cost per recursion step* is the tax. This is the most battle-tested PQ recursion in the
field (Plonky2/3, RISC-Zero, SP1). → **The PQ-now primary.**

**Lattice folding — LatticeFold+ (2025/247), Neo & SuperNeo (2026/242), Lova (2024/1964) — (a).** [G]
These replace the *discrete-log* homomorphic commitment of Nova/HyperNova with a **lattice (Ajtai /
Module-SIS or unstructured-SIS)** homomorphic commitment that is plausibly PQ and works over **small
fields** — so they are the *one* PQ option that **preserves the folding/accumulation abstraction**
(fold two instance-witness pairs into one; verifier ≈ a weighted sum of commitments). **LatticeFold+**
makes the prover faster and the verifier circuit simpler than LatticeFold via a *purely algebraic* range
proof + double commitments, but still uses **cyclotomic-ring arithmetic** [G]. **Neo** adapts HyperNova to
lattices with *pay-per-bit* Ajtai commitments and **folds CCS — which generalizes R1CS, Plonkish, and
AIR** — over Goldilocks, but **requires SIMD constraint systems** [G]. **SuperNeo** removes the SIMD
restriction and is *the first scheme to hit all six* of {PQ · pay-per-bit · field-native · general
(non-SIMD) constraints · small-field (Goldilocks) · low recursion overhead} [G] — explicitly contrasting
itself against "hash-based schemes (e.g., Arc) [which] incur large verifier circuits." **Lova** is the
first folding scheme from *unstructured* SIS, with a Rust implementation using hardware-friendly
power-of-two moduli (no finite-field arithmetic) [G] — the simplest assumption, but the least general
(an exact-Euclidean-norm-proof gadget, not a general AIR folder). → **The genuine "preserve-folding" PQ
migration target; SuperNeo is the realistic one, but unaudited and months old.**

---

## Comparison table

| Option | PQ? | Hash-native? | Succinct-**unbounded** now? | Soundness: provable vs heuristic | Preserves folding/accumulation abstraction? | Maturity |
|---|---|---|---|---|---|---|
| **Fractal** (2019/1076, holographic) | ✔ [G] | ✔ (RO instantiated by hash) [G] | ✔ unbounded recursion *demonstrated* [G] | **heuristic** — secure in RO, recursion "heuristically instantiated via a hash" [G] | ✗ (recursive-verifier, not folding) | research-grade; 181-bit field, 80–160 kB, minutes to prove [G] |
| **(d) Recursive-STARK / FRI-in-circuit** (Plonky2/3, in-tree) | ✔ [G][C] | ✔ **native — it IS the STARK** [C] | **✔ unbounded — shrinks any proof to ~43 kB constant** [G] | **heuristic** Fiat-Shamir (same RO impossibility, Valiant/2022-542) [G] | ✗ (recursive-verifier, no accumulator instance) | **highest — in-tree default-on**; Plonky2/3, RISC-Zero, SP1 [C] |
| **(a) Lattice folding** — SuperNeo/Neo/LF+/Lova | ✔ plausible (SIS/Module-SIS) [G] | **✗ — homomorphic (Ajtai) commitment, replaces FRI/Merkle** [G] | ✔ unbounded IVC/PCD (folding → IVC) [G] | folding KS proofs are *provable under SIS*, but **IVC-from-folding still RO-heuristic at the recursion step** [G] | **✔ YES — this is its whole point** [G] | **low** — SuperNeo 2026, no audit; LF+ Aug-2025; Lova has a Rust impl [G] |
| Nova/HyperNova/ProtoStar (for contrast) | ✗ | ✗ (Pedersen/MSM) | ✔ | heuristic (RO) | ✔ | high but **non-PQ; eliminated** [C] |

**Reading the table:** the two columns that decide it are **"hash-native?"** and **"preserves folding?"** —
they are *mutually exclusive across the PQ options*. Recursive-STARK/Fractal are hash-native but throw away
folding; lattice folding keeps folding but throws away the hash commitment. **You cannot have both PQ AND
hash-native AND the folding abstraction** with anything that exists today. dregg already chose hash-native
(BabyBear+Poseidon2+FRI) [C], so the folding abstraction is the thing that does not survive PQ-now.

---

## On heuristic Fiat-Shamir soundness (recursive-STARK & Pickles both) — is it acceptable?

**Yes — and it is the central, decisive realization of this memo.** Be precise about what is and is not
proven:

1. **Valiant (TCC'08) + Hall-Andersen–Nielsen (2022/542)** prove that **unbounded IVC cannot be sound in
   the *standard* random-oracle model without computational assumptions**, under two mild extra conditions,
   *one of which is that the proof system is zero-knowledge* [G]. dregg wants ZK and is FRI/RO-based, so a
   *ZK + ROM + unbounded-IVC* system sits **exactly inside that impossibility**. This is not a defect of any
   particular scheme — it is a statement that **no hash-native unbounded IVC can be *proven* sound in the
   idealized ROM**. The escape is the same for *everyone*: instantiate the RO with a concrete hash
   (Poseidon2) and accept that soundness is now a **heuristic** (the Fiat-Shamir / random-oracle heuristic),
   not an ROM theorem.

2. **This is the same heuristic Pickles relies on.** Path B accepted Pickles (Mina) as the homomorphic
   reference. Pickles' recursion is *also* Fiat-Shamir-heuristic: its soundness is argued in the ROM and
   then the oracle is instantiated by a concrete hash (Poseidon). **Pickles does not have an ROM-provable
   unbounded-IVC theorem either** — it lives under the *exact same* Valiant/2022-542 ceiling. So choosing
   recursive-STARK over Pickles is **not a downgrade in the *kind* of soundness assumption**; both are
   "sound in practice under the FS heuristic, not provable-in-idealized-ROM." The honest framing:

   > **Recursive-STARK unbounded IVC is "sound in practice under the Fiat-Shamir heuristic, not
   > provably-sound in the idealized ROM" — and this is *categorically identical* to Pickles' situation,
   > except at post-quantum (hash) security instead of discrete-log security.**

3. **dregg's own architecture already routes around the sharpest edge.** The feasibility memo
   (`DECISION-recursion-feasibility-lookups.md`) decided dregg's *per-turn* obligation is **bounded-depth
   aggregation, not unbounded IVC** [C] — a turn is finite by construction (flattened CallForest ≤ 5
   aspects ≤ N cells), and across the receipt chain dregg *hash-chains segments in the clear* rather than
   folding an ever-growing instance. Bounded aggregation **sidesteps the impossibility entirely** (there is
   no "verifier knows only genesis, witness arrives incrementally" structure to attack), and
   Campanelli–Fiore–Pancholi's **depth-boosting** is the on-demand escape if a long segment ever needs a
   single succinct proof. So for dregg, the heuristic only bites at the *optional* unbounded top — and even
   there it is the industry-standard heuristic Pickles also accepts.

**Verdict on acceptability: ACCEPTABLE.** Refusing heuristic FS would mean refusing *all* practical
recursion (Pickles included) and waiting for iO+LWE IVC-for-NP (2025/1546) [G], which is not a deployable
primitive. The honest posture is: *document* that recursive-STARK IVC soundness rests on the FS heuristic,
keep the load-bearing obligations in **bounded aggregation** where no ROM impossibility applies, and treat
the unbounded top as the same calculated bet Mina/Pickles already shipped.

---

## VERDICT: migration-target ranking + can any be PQ-now-primary?

**Ranked as a Path-B migration target (preserving the accumulation abstraction where possible):**

1. **(d) Recursive-STARK / FRI-verifier-in-circuit — PRIMARY, PQ-NOW.** It is the only option that is PQ
   ✔, hash-native ✔, succinct-**unbounded today** ✔, transparent ✔, small-field ✔, **and already built &
   default-on in dregg** [C]. It does *not* preserve the folding abstraction — but the strategy memo already
   established dregg never started folding (`ivc.rs` is a hash-chain placeholder; the `*fold*` files are
   attenuation-set folding, not Nova folding) [C], so there is **no folding abstraction to preserve in the
   first place**. The accumulation abstraction dregg actually has is "recursively verify the inner STARK and
   bind its PI," and (d) *is* that. **This makes "PQ-now" real, not aspirational.**

2. **(a) Lattice folding — SuperNeo — WATCH-LIST / FUTURE MIGRATION.** The realistic PQ-folding target:
   SuperNeo is the only scheme that folds **general AIR over a small field, PQ, with low recursion
   overhead** [G]. It is the migration to take **if and only if** the recursive-STARK per-step prover tax
   ("large verifier circuits") becomes the binding constraint on deep cap-chains / many-cell aggregation
   [C]. But it is a **commitment-layer transplant** (rip out FRI/Merkle, install Module-SIS) on a scheme
   that is months old with **no audited implementation**, so it is *not* PQ-now-primary. Of the four:
   **SuperNeo > Neo** (Neo needs SIMD constraints) **> LatticeFold+** (cyclotomic-ring arithmetic, not
   small-field-native to the same degree) **> Lova** (cleanest assumption + a Rust impl, but a
   norm-proof gadget, not a general AIR folder — keep as the *simplest-assumption* fallback).

3. **Fractal — REFERENCE ONLY.** It is the *proof that PQ+transparent recursion is possible at all* and the
   intellectual ancestor of (d), but its concrete instantiation (181-bit field, 80–160 kB args, minutes to
   prove) is superseded by the Plonky2/3 engineering dregg already runs. Cite it as the soundness/feasibility
   anchor; do not target it.

**Can any be PQ-now-primary? YES — (d), and it already is, in-tree.** The "homomorphic-now → PQ-later"
necessity claim of Path B is **false for *unbounded recursion as such*** — hash-native unbounded recursion
is a solved, shipped problem (Plonky2/3). It is **only true if the requirement is specifically to keep the
*folding/accumulator* abstraction** (constant tiny recursion circuit, prover work ≈ commit cost). If dregg
values *that* abstraction, then yes: homomorphic-now (Pickles) → PQ-folding-later (SuperNeo) is the path,
because PQ folding is not yet mature. **Deciding constraints, stated plainly:**

- **dregg is hash-native already (BabyBear/Poseidon2/FRI) [C]** → the recursive-STARK path is *zero
  migration*; the lattice-folding path is a *full commitment-layer rewrite*.
- **dregg never built folding [C]** → there is no accumulation abstraction whose loss is a cost; the
  "preserve folding" argument that would favor (a) has no purchase here.
- **The only real win (a) offers over (d) is per-step prover cost** (small recursion circuit). That is an
  *efficiency* lever, not a *capability* or *PQ* lever — so it is a fallback trigger, not a reason to delay.
- **Soundness is heuristic-FS either way** (Pickles, recursive-STARK, and even lattice-folding *IVC* at the
  recursion step) → soundness does not discriminate between them; it only rules out demanding an
  ROM-provable unbounded IVC, which nobody can supply without iO.

**Therefore: run recursive-STARK as the PQ-now PRIMARY immediately; do NOT gate "PQ" behind a future
lattice migration.** Keep Pickles as the Mina-interop / homomorphic reference only (it is non-PQ) [C].

---

## What to build / the parallel-track plan

This is *not* "two parallel proving stacks." dregg's hash-native track **is** the primary, and the
lattice-folding track is a thin, well-isolated *watch-list spike*. Concretely:

1. **Primary track (do now):** finish wiring `RecursionMode::Recursive` (`plonky3_verifier_air.rs`) into
   composition — promote it from available-but-unwired to the default; replace `ivc.rs`'s
   accumulated-hash step with the in-circuit FRI verify; make cross-cell aggregation a recursive-verify
   `AggregationAir` rather than a Σ-fold [C]. This is the deliverable of `DECISION-recursion-strategy.md`;
   nothing here changes it — this memo *confirms it is also the PQ track*.
2. **Keep obligations in bounded aggregation** (depth-1 wrapper, static fan-in) per the feasibility memo, so
   the FS heuristic only ever rides the *optional* unbounded top, not the per-turn validity proof [C].
3. **Benchmark the recursion-step prover cost** on BabyBear with the degree-7 AIRs (`log_blowup=3` forced)
   [C]. This single number is the **trigger gate** for the lattice track: if the "large verifier circuit"
   tax is prohibitive on deep chains, *that* is when SuperNeo becomes worth its transplant cost.
4. **Parallel watch-list spike (low priority, behind a feature flag):** prototype a SuperNeo-style
   Module-SIS folding accumulator for the *one* hottest aggregation site (cross-cell N-way), measured
   head-to-head against the recursive-STARK aggregator. Goal is a *migration-readiness* datapoint, not a
   second production path. Track CCS-encoding of dregg's AIRs (CCS subsumes AIR [G]) as the portability hedge.
5. **Document the soundness posture once, centrally** (a metatheory/README caveat): recursive-STARK IVC
   soundness = Fiat-Shamir heuristic = same class as Pickles; bounded aggregation is ROM-impossibility-free;
   unbounded top is the calculated, industry-standard bet. **Never merge the crypto-soundness claim into the
   Lean laws** (per the synthesis: it is a circuit obligation, not a metatheory theorem).

---

## Risks & open questions

- **[C→confirm] Recursion-step prover cost on BabyBear degree-7 AIRs is the make-or-break number.** It
  decides whether (d) stays primary forever or whether the SuperNeo migration is ever triggered. Measure
  end-to-end recursion-layer prove time before committing to deep cap-chains.
- **[C→confirm] Two FRI-verifier gadgets coexist** (`p3-recursion` and the hand-rolled `RecursiveFriAir`);
  pick `p3-recursion` as canonical, do not maintain both. Also confirm the recursion gadget can consume a
  *hiding* (`HidingFriPcs`) inner proof, or apply ZK only at the outermost layer.
- **[G] SuperNeo/Neo are unaudited and months old (2026).** A commitment-layer transplant onto an unaudited
  folding scheme is a far larger soundness risk than the well-understood FS heuristic of recursive-STARK.
  This is a strong argument *against* rushing (a) and *for* (d)-now.
- **[G] The Valiant/2022-542 impossibility is permanent for *idealized-ROM* unbounded IVC** — no scheme
  (hash or lattice) escapes it; only iO+LWE (2025/1546) gives IVC-for-NP from "standard" assumptions, and iO
  is not deployable. So "provable unbounded IVC" is **off the table for everyone**; the only honest choices
  are heuristic-FS or bounded-aggregation. dregg uses both.
- **[F] CCS-as-AIR portability hedge.** Both (d)'s AIRs and (a)'s folder can speak CCS (CCS subsumes AIR
  [G]). Keeping dregg's constraint systems expressible as CCS keeps the SuperNeo door open at low cost — do
  this even while (d) is primary.
- **[F] "Hash-native AND folding" may become possible.** Accumulation-without-homomorphism (2024/474) is
  Merkle-native folding but **depth-bounded** [C] — if a future version lifts the depth bound, it would be
  the holy-grail "hash-native folding." Park it on the same watch-list as SuperNeo.
</content>
</invoke>
