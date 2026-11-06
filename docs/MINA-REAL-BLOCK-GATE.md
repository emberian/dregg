# MINA-REAL-BLOCK-GATE.md — a real Mina block, driven through our checks, per check

**Date:** 2026-07-28. **Status:** the gate is OPEN and green; **C3 is no longer carried**,
**group elements are no longer untouched** (§6.1 rungs 5a–5d), **a commitment is now
opened** (§6.1 rungs 5e–5f), and **the terminal `⟨s, srs.g⟩` MSM is no longer deferred**
(§6.1 rung 5h) — subject to the premises §6.1 names and does not discharge, P10 above all.
**Artifacts:** `metatheory/fixtures/pickles-extractors/` (extractors + fixtures, tracked —
`src/main.rs` for the scalar side, `src/bin/wrap_group_export.rs` for the group side),
`metatheory/mina_real_block_proof.json` and `metatheory/mina_real_block_wrap_group.json` (the
dumps),
`metatheory/Dregg2/Circuit/Emit/MinaRealBlockGate.lean` (18 theorems, axiom-clean),
`metatheory/Dregg2/Circuit/Emit/MinaRealBlockTranscript.lean` (13 theorems, axiom-clean — the
Fiat–Shamir derivation),
`metatheory/Dregg2/Circuit/Emit/MinaWrapGroupGate.lean` (15 theorems, axiom-clean — the `ft_comm`
assembly on real Pallas points, `lake build` 25 s),
`metatheory/Dregg2/Circuit/Emit/MinaWrapAggregationGate.lean` (7 theorems, axiom-clean — the
47-term polyscale aggregation, 93 s),
`metatheory/Dregg2/Circuit/Emit/MinaWrapPublicCommGate.lean` (11 theorems, axiom-clean — rung 5e,
`public_comm` derived from the 40-element public input, 159 s) and
`metatheory/Dregg2/Circuit/Emit/MinaWrapOpeningGate.lean` +
`MinaWrapOpeningWeld.lean` (26 + 1 theorems, axiom-clean — rung 5f, **the IPA opening relation**,
153 s + 75 s),
`metatheory/Dregg2/Circuit/Emit/PastaIpaFold.lean` (14 theorems, axiom-clean — the group-side
twin of `sVec_eq_bPoly`: the generator FOLD identity and the bit-plane MSM identity that actually
makes 5h tractable) and
`metatheory/Dregg2/Circuit/Emit/PastaMsmBound.lean` (Lean-authored AIR, axiom-clean — §6.1 rung
**5h-AIR-BOUND**, the exact-public generator table that makes the emitted constraints FORCE a row's
`SRC` to be `srs.g` at the absolute index the manifest names; artifacts under
`circuit/tests/fixtures/pasta-sg-bound/`, re-derived by `scripts/regen-pasta-bound.sh`),
`metatheory/Dregg2/Circuit/Emit/PastaMsmOnCurve.lean` (Lean-authored AIR, axiom-clean — §6.1 rung
**5h-AIR-CURVE**, the on-curve + non-degeneracy gate that forces both operands of every emitted RCB
add to be POINTS of the Pallas curve; it closed a forgery the `5h-AIR-BOUND` descriptor PROVES AND
VERIFIES — an all-`(0,0,0)` accumulator carrying the real generators — and its artifacts are
re-derived by `scripts/regen-pasta-oncurve.sh`) and
`metatheory/Dregg2/Circuit/Emit/MinaWrapSgCore.lean` and the four `MinaWrapSgChunk` modules
(13 + 32 theorems, axiom-clean — **rung 5h, the `2^15`-term terminal MSM**; the chunks were retired 2026-11-06, see metatheory/docs/MINA-PICKLES-RESCUE.md), over the generated
fixtures `MinaWrapSrsG.lean` (the 32768 SRS generators) and `MinaWrapSgParts.lean`.

All seven are wired into `metatheory/Dregg2.lean` — the first four by `06de765e9` / `73853b50f`,
the three new ones by `ec839066d` (a sibling orphan-sweep lane; this lane reported the import
lines rather than editing the root itself, per house practice):

```
import Dregg2.Circuit.Emit.MinaWrapPublicCommGate
import Dregg2.Circuit.Emit.MinaWrapOpeningGate
import Dregg2.Circuit.Emit.MinaWrapOpeningWeld
```

`#floor_ratchet` reads the environment of that root and nothing else, so a module it cannot see
cannot arm it. **Measured before the wiring landed, with the three added lane-locally on hbox
(`lake build Dregg2`, 10413 modules): still exactly 1**, and the same name —
`Emit.AutomataflRevealRefine.not_revealColl_of_hash4NoCollision`, the violation
`docs/DREGG-IN-DREGG-BUILD.md` records as pre-existing. Expected, and worth saying why: these
modules bind no floor at all. Every theorem is `by decide` or `#guard` over concrete
`Nat`/`ZMod` values, so there is no `CommitSurface`, no injectivity hypothesis and nothing for the
gate to promote.

⚑ **Re-measured 2026-07-29 with `PastaMsmBound` wired in, on a COMPLETE root build** (hbox lane
`mina-sg-bound`, `lake build Dregg2`, **10450/10451 jobs**): **still exactly 1, and still the same
name** — `Emit.AutomataflRevealRefine.not_revealColl_of_hash4NoCollision`, with `#teeth_wired`
confirming 14 teeth modules. That is the whole of the build's error output; the ratchet is the sole
failure, exactly as `docs/DREGG-IN-DREGG-BUILD.md` records. Said at the right resolution: this is a
MEASUREMENT, not the pre-commit `check-floor-baseline-preflight`, which is a source scan and would
not have caught a floor arriving through an import.

---

## 0. What changed, in one paragraph

`docs/PICKLES-VERIFIER-SCOPE.md` said, correctly, that P0's residual was "**no real Wrap fixture**
— that needs a mainnet block through mina-rust's `verify_block`". Everything the campaign had ever
run on was ours: `KimchiRealProofGate` used a proof **we** generated from `create_circuit(0, 5)`,
and `PicklesRecursion` P0–P2 used **synthetic witnesses at a `2^5` domain**. That residual is now
closed. A real Mina devnet block's Wrap proof — Pallas-committed, `k = 15`, `prev_challenges = 2`,
`public = 40`, domain `2^14` — is a committed fixture, **o1-labs' own Kimchi verifier accepts it**,
and it runs through the assembled Lean decision, which accepts it and rejects every tamper.

## 1. Where the proof came from

* Mina **devnet**, chain id `29936104443aaf264a7f0192ac64b1c7173198c1ed404c1bcff5e562e05eb7f6`,
  genesis `3NL93SipJfAMNDBRfQ8Uo8LPovC74mnJZfZYB5SK7mTtkL72dsPx`.
* Block **539508**, state hash `3NLmVB6Fs3dm4kXNkgwheHXzJXNpCCwEDe76RpTVeBTNujm12zNk`.
* Fetched read-only over GraphQL from the public node `api.minascan.io/node/devnet` on 2026-07-28.
  No keys, no transactions, no mainnet writes. The raw response is pinned in
  `metatheory/fixtures/pickles-extractors/mina_devnet_block.json`; the proof is the base64url of
  the binprot `Mina_base.Proof.Stable.V2`, 11138 bytes.

## 2. That Mina's own verifier accepts it

Asserted in the extractor, in order, before anything is emitted (see the README for why
`verify_block` is assembled from its two halves rather than called whole, and why that
substitution is self-checking):

| # | check | code that runs | verdict |
|---|---|---|---|
| 1 | devnet blockchain VK loads | openmina `BlockVerifier::make()` | `public=40 prev_challenges=2 domain=2^14 max_poly_size=2^15 zk_rows=3` |
| 2 | `sg` accumulator discharge | openmina `accumulator_check` → `batch_dlog_accumulator_check` | **true** |
| 3 | the Wrap Kimchi proof | **o1-labs `kimchi::verifier::verify::<Pallas,…>`** | **`Ok(())`** |

Plus six Rust cross-checks tying our numbers to `proof.oracles(...)` — the C8 fold over the 47 `es`
entries reproduces `combined_inner_product`; the C5 body reproduces `ft_eval0`; `zkPolyR`
reproduces kimchi's permutation vanishing polynomial; `ω^(n−3)` reproduces `index.w()`; and K4c's
`bEval` reproduces `RecursionChallenge::evals` at ζ and ζω for **both** carried accumulators.

And, added 2026-07-28 with C3, **three transcript cross-checks** — the extractor replays *both*
Fiat–Shamir sponges with the real upstream `DefaultFqSponge`/`DefaultFrSponge` and asserts each
challenge against `oracles(...)`:

```
[c3] phase-1 Fq-sponge (fp_kimchi over Fp) replay reproduces beta, gamma, alpha', zeta', digest : true
[c3] phase-2 Fr-sponge (fq_kimchi over Fq) replay over 91 absorbed elements reproduces v', u' : true
[c3] order controls: ft_eval1-after-public-evals and no-prev-challenge-digest BOTH move v' : true
```

## 3. Our side, check by check

`shapeOkRec`/`prevChalFoldOk`/`kimchiVerifyDecisionFieldRec` are the P6 retirement a sibling lane
landed the same day; this is the first time any of them has seen a Mina object.

| our check | on the real block | verdict |
|---|---|---|
| **C1 `shapeOk`** (K5, frozen at `prevLen = 0`) | `prev_challenges = 2` | **REFUSES the real block** — `real_block_refused_by_freeze`. The freeze was not conservative; it rejected Mina. |
| **C1 `shapeOkRec`** at the real index | `idxPrev = 2, prev = 2, public = 40, w = 15, σ = 6, coeff = 15, t = 7, chunk = 1` | **accepts**; 6 single-count tampers reject |
| **P6 recursion fold** `prevChalFoldOk` | the 2 leading `es` entries at ζ and ζω vs. the 2×15 carried challenges | **accepts** — the exposed accumulator evaluations ARE K4c's b-polynomial of the carried challenges |
| **K4c `bEval` / `sVec_eq_bPoly`** | `bEvalSq ZETA CHALS_i`, `bEvalSq ZETAW CHALS_i`, i∈{0,1} | **reproduces all four**, and `bEvalSq_eq_bEval` ties the value to the object `sVec_eq_bPoly` is about |
| **C8 `combinedInnerProduct`** | 47-entry `es` list **including** the recursion prefix, `ξ`/`r` from `oracles()` | **reproduces `combined_inner_product`**; 4 tampers reject |
| **C5-inv** witnessed inverse | `(ζ − ω^{n−3})(ζ − 1) · DINV = 1` in `ZMod qN` | **holds** (no `Field (ZMod qN)` instance needed) |
| **C5 `ftEval0R`** | real `n = 2^14`, real ω, ζ, β, γ, α^21..α^23, w[0..6], σ[0..5], shift[0..6], linearization constant term | **reproduces `ft_eval0`**; 3 tampers reject |
| **composed `kimchiVerifyDecisionFieldRec`** | all of the above at once | **ACCEPTS the real Mina block**; 4 tampers reject; the pre-P6 decision refuses it outright |
| **C3 the Fiat–Shamir transcript** (`MinaRealBlockTranscript`) | both sponges, over the block's own commitment coordinates and evaluations | **DERIVES β, γ, α′, ζ′, the digest, the prev-challenge digest, ξ′ and r′**; the endo lifts give α, ζ, ζω, ξ, r; 15 non-vacuity pins |
| **the group assembly** (`MinaWrapGroupGate` / `MinaWrapAggregationGate`) | the block's 7 `t_comm` chunks, the index's `sigma_comm[6]`, all 47 aggregation commitments | **reproduces `ft_comm` and `Σ ξⁱ·Cᵢ`** over the real group law; `ft_comm` is pinned by o1-labs' own `SRS::verify`; 9 tampers reject — §6.1 rungs 5a–5d |
| **`public_comm`** (`MinaWrapPublicCommGate`) | 40 SRS Lagrange points × the block's 40-element public input, + the `+1·h` blinder | **DERIVES the commitment C3 absorbs**; 5 tampers reject — §6.1 rung 5e |
| **the IPA opening relation** (`MinaWrapOpeningGate` / `…Weld`) | `lr[0..14]`, `sg`, `delta`, `u_base`, the 47-term aggregate, at challenges continued from the block's own sponge | **`c·Q + delta − z1·sg − z1·b0·U − z2·H = O`**; 9 tampers reject — §6.1 rung 5f, **the rung that opens a commitment**, on the premises §6.1 names |
| **the terminal `⟨s, srs.g⟩`** (`MinaWrapSgCore` / `MinaWrapSgChunk0..3`) | all **32768** SRS generators against the `2^15` s-vector entries the kernel DERIVES from the block's 15 IPA challenges | **reproduces `opening.sg`**, in 32 index-pinned chunks that provably tile `srs.g` in order, plus the re-sum; a perturbed partial rejects — §6.1 rung 5h, **the rung that stops deferring the big MSM** |

Everything above is `by decide`/`rfl`/`#guard`, no `sorry`, no `native_decide`;
`#assert_namespace_axioms` reports **18 theorems pinned kernel-clean** for the gate, **13** for the
transcript, **15 / 7** for the two group modules, **11** for `public_comm` and **25 / 1** for the
opening rung. `lake build` on hbox: **82s** gate, **14s** transcript, **25s / 93s** group,
**159s** `public_comm`, **153s / 75s** opening.

### C3, retired — what the transcript module derives (2026-07-28)

The Wrap proof is **Pallas**-committed, so by `curve.rs:62-72,87-104` its two sponges are the
*mirror* of the Vesta-committed Step fixture `PastaPoseidonFq` was built on: **phase 1 is
`fp_kimchi` over `Fp`** (K3's own constants — `core_is_Ref_at_Fp` proves the instantiation IS
`PastaPoseidon.Ref`), and **phase 2 is `fq_kimchi` over `Fq`** (`PastaPoseidonFq`). One parametric
absorb schedule runs both; there is no second transcription to get wrong.

| value | how | pin |
|---|---|---|
| β, γ | raw 128-bit squeezes of the phase-1 sponge after 37 absorbed `Fp` elements (index digest · 2 recursion commitments · public commitment · 15 witness commitments) | `wrapPhase1`; `derived_beta`/`derived_gamma` tie the `Nat` to the `Fq` element C5 consumed |
| α′ → α | + `z_comm`, squeeze, `endoMap ENDO_R` | `derived_alpha`; `derived_alpha_powers` ties α to C5's α²¹/α²²/α²³ |
| ζ′ → ζ, ζω | + `t_comm` (7 chunks), squeeze, `endoMap` | `derived_zeta` |
| fq digest | `squeeze_field()` reinterpreted in `Fq` (the mirror of the Step side's `Fp`) | `wrapPhase1` |
| prev-challenge digest | a FRESH `fq_kimchi` sponge over the **30** carried challenges — an EVEN-length absorb, the branch the 07-27 double-permute defect lived on | `Core.hash fqParams CHALS_FLAT`, with the double-permute anti-value pinned |
| ξ′ → ξ, r′ → r | phase-2 sponge over 91 `Fq` elements, two squeezes (lanes 0 and 1 of one permuted state), `endoMap` | `wrapPhase2`; `derived_v`/`derived_u` |

⚑ **The phase-2 tape is not a second copy of the evaluations.** `absorb_evaluations`' 86-element
stream is exactly entries 4.. of the gate's own C8 columns, interleaved ζ/ζω, read through
`ZMod.val`; `ft_eval1` is `EVZW[3]` and `p(ζ)`/`p(ζω)` are `EVZ[2]`/`EVZW[2]`. A prover cannot show
one set of evaluations to the transcript and another to the aggregation.

`real_block_accepts_on_derived_challenges` restates the gate's accept with **every** challenge
argument replaced by the derived expression, and is proved by rewriting — not by a second `decide`.

**Two order facts, verified against `verifier.rs`/`plonk_sponge.rs` at the pinned tag (`0.3.0` =
`a73ca6ed58`) rather than off a doc, and MEASURED on this object:** `ft_eval1` is absorbed at
`:382`, **before** the public evaluations at `:391-392`; and the prev-challenge digest (`:290-299`)
sits between the fq digest and `ft_eval1`. Both mis-orderings produce a **different ξ′** — asserted
in Rust and pinned in Lean. Both are dead at `prev_challenges = 0`; this block carries 2.

### What could NOT be fed, and why

* **C9 / the terminal `msm == 0`** — the IPA opening-soundness FLOOR (P10) is unchanged and
  inherited. Its two arithmetic halves are not: (B) is rung 5f and (A) is rung 5h, both now
  in-kernel. Verified ≠ sound; P10 is the difference.
* **The commitment arithmetic** — *superseded the same day, twice.* This bullet used to read
  "nothing in-kernel touches them"; then, after 5a–5d, "nothing yet checks that a commitment
  commits to anything". **Both are now out of date.** `MinaWrapGroupGate` /
  `MinaWrapAggregationGate` compose K4a's RCB complete add and K4b's ladder over the block's own
  `t_comm` chunks, the index's `sigma_comm[6]` and all 47 aggregation commitments (5a–5d);
  `MinaWrapPublicCommGate` **derives** `public_comm` from the block's 40 public inputs, so C3 no
  longer eats those two coordinates (5e); and `MinaWrapOpeningGate` states the IPA **opening
  relation** over `lr`, `delta`, `sg`, `u_base` and the aggregate (5f). What remains true: C3
  still eats the `(x, y)` of the two RECURSION commitments and of `w_comm`/`z_comm`/`t_comm` —
  the group gates check curve membership of every point they consume, but the transcript itself
  does not — and a `RecursionChallenge`'s `comm` is still not checked to be
  `⟨b_poly_coefficients(chals), G⟩` (5g) — though 5h now does exactly that computation for the
  OPENING's `sg`, so 5g is a fixture away. See §6.1 for what 5f and 5h establish versus assume.
* **The verifier-index digest is DERIVED — 2026-08-06.** ~~Still an input.~~
  `Dregg2.Circuit.Emit.MinaWrapVkDigestChain` runs `index.digest::<EFqSponge>()`
  (`verifier_index.rs:399-524`) as **28 more links of `dregg-pasta-fp-chainlink::v1` — the same
  descriptor the 27 phase-1 links use, no new AIR** — over the sha256-pinned
  `mina-devnet-wrap-blockchain-vk.json`'s 7 `sigma_comm` + 15 `coefficients_comm` + 6 selector
  commitments = 28 points = 56 coordinates. `the_vk_wire_blocks_are_equal` welds link 27's outgoing
  lane 0 to the phase-1 tape's element 0, 32 felts elementwise. Harness:
  `circuit/tests/mina_wrap_vk_digest_chain_proves.rs`.
  ⚠ **Two things it does NOT establish, both stated there as theorems.** (1) kimchi's `digest()`
  binds `domain`, `max_poly_size`, `zk_rows`, `public`, `prev_challenges`, `shift`, `w`, `endo` to
  `_`, so the digest is a function of the 28 commitments **alone** and does not name the circuit.
  (2) That the pinned fixture is *this block's* verifier index is a **sha256 against a byte copy** —
  a build-tree fact; the devnet *transaction* Wrap index runs the same 28 links to its own digest.
  So this removed a CARRIER, not a trust assumption: one opaque 254-bit constant became 56
  coordinates a byte-pinned fixture determines.
* **`KimchiVerify.frPhase2Inputs` is the `prev_challenges = 0` helper only** — it hard-codes the
  prev-challenge digest as `Ref.hash []` *and* runs over `fp_kimchi`/`pN`, which is right for a
  Vesta-committed Step proof and wrong on both counts for a Wrap proof. Its one caller
  (`KimchiRealProofGate`) is a `nPrev = 0` Step fixture, so nothing is presently wrong; the
  recursive/Wrap phase-2 model is `MinaRealBlockTranscript.fqTape2`. Named as debt, not fixed here.
* **The deferred STEP values** — `expand_deferred`'s Fp outputs (`b`, `combined_inner_product`,
  `xi`, `perm`, `zeta_to_domain_size`, shifted Type1) are dumped and are the P3/P4 input, but no
  Lean check consumes them yet.

## 4. Corrections to `docs/PICKLES-VERIFIER-SCOPE.md`, measured

That document is being edited by a sibling lane, so the corrections are recorded here rather than
applied in place.

1. **P0's "no real Wrap fixture" residual is CLOSED**, and the fixture is a devnet block, not a
   mainnet one — see §5.
2. **The wrap domain is not always `2^15`.** §D says wrap domain `∈ {2^13, 2^14, 2^15}` keyed by
   `proofs_verified` (`0→13, 1→14, 2→15`). The real devnet **blockchain** VK has
   `domain = 2^14` while `branch_data = {proofs_verified: N2, domain_log2: 16}`. `branch_data`
   describes the **Step** side (2^16, two previous proofs); the Wrap VK's own domain is 2^14 and
   its `max_poly_size` is 2^15. Any model that reads "Wrap ⇒ 2^15 domain" off §A is wrong; 2^15 is
   `max_poly_size` / the SRS depth, and `chunk_size = 1` because `2^14 < 2^15`.
3. **`prev_challenges = 2` is not "Wrap_hack padding" on this block — it is real.** The proof
   carries two genuine `challenge_polynomial_commitments`, so `verify.ml:361-364`'s pad-to-2 is a
   no-op here (the extractor asserts it rather than padding silently).
4. **A new, measured cost wall.** `ftEval0R` raises ω to `n−3`, `n−2`, `n−1` and ζ to `n` through
   unary `Monoid.npow`. At `KimchiRealProofGate`'s `n = 32` that is free; at the real `n = 2^14` it
   is ~65k kernel multiplications in `ZMod qN` and it is why the file needs
   `set_option maxRecDepth 100000`. It still builds (82s total), but C5 has no `sqIter` ladder the
   way the b-polynomial does, and the next domain size up doubles it.

## 5. A measured openmina defect: mainnet block verification is broken at HEAD

At openmina `82480cd468`, `crates/ledger/src/proofs/data/mainnet_*_verifier_index.json` are in a
**stale serde format** — `PolyComm` as `{unshifted, shifted}`, no `zk_rows`, `domain` as a
172-byte arkworks-0.3 int array — while the pinned proof-systems `0.3.0` `SerdeAs` reads a hex
string from any human-readable format. `BlockVerifier::make()` therefore **panics** on mainnet with
`invalid type: sequence, expected a hex encoded string`. Not feature-dependent: `serde_json` is
always human-readable. The devnet files were regenerated and are fine. Reproduction:
`cargo run --release -- mainnet` in the extractor. A real mainnet block header (height 359606) is
committed alongside so that the moment the index is regenerated, `verify_block` can be called
literally.

## 6. The honest distance to "we verify a real Mina block"

Ordered by effort, with the synthetic-witness estimates replaced by what the real object cost.

| # | what | measured status |
|---|---|---|
| 0 | get a real Mina proof and confirm Mina accepts it | **DONE.** ~1 build of openmina's `mina-tree` (1m41s incremental once the lockfile is seeded) + a GraphQL read. |
| 1 | C1 at the real Wrap shape | **DONE** (P6's shape half, sibling; measured here). |
| 2 | the recursion fold into C8 (P6 arithmetic half) | **DONE** on real data. |
| 3 | C8 / C5 / the witnessed inverse on real Wrap scalars | **DONE**. |
| 4 | **C3 — the Fiat–Shamir transcript re-derived instead of carried** | **DONE, 2026-07-28.** `MinaRealBlockTranscript.lean`, 13 theorems + 15 `#guard` pins, `lake build` 14s. All six challenges plus both digests fall out of the two sponges over the block's own commitments and evaluations; `real_block_accepts_on_derived_challenges` is the gate's accept with every challenge argument replaced. The estimate ("a day, not a week") held. What it needed that was NOT in the dump: the verifier-index digest, the public commitment's coordinates, the prev-challenge digest and `endo_r` — added to the extractor, which now also **replays both sponges in Rust** against `oracles(...)`. |
| 5 | the Wrap **group** check | **5a–5f AND 5h DONE, 2026-07-28** — no longer one block. Broken into rungs and re-priced below. 5f is the rung that opens a commitment; 5h is the terminal `2^15`-term MSM and is now checked, not asserted; 5g is the same shape as 5h, re-priced from "~36 h / ~14 TB" to a few hours with bounded memory, and unbuilt only for want of a fixture. P10 is untouched by all of it. |
| 6 | P3/P4 — `finalize_other_proof` + the transcript-equality binding | **NOT STARTED**, and the real block now supplies the inputs: `step_deferred_values` in the dump is `expand_deferred`'s output, Type1-shifted, with the unshifted values alongside. P4 remains the single hardest buildable item. |
| 7 | P7/P8/P9 — base case, wrap-VK model, Mina's instantiation | **NOT STARTED**, but P8/P9's *data* is now concrete rather than notional: the devnet blockchain VK is a loadable object with known counts. |
| 8 | P10 — the IPA `msm == 0` opening-soundness floor | **INHERITED, undischarged**, as before — and rungs 5f/5h are exactly the place to keep saying so. 5f states the verifier's opening *check* in-kernel and it passes; 5h now states the other half of that check, the `sg` leg, and it passes too. **P10 is the claim that passing them implies the prover KNOWS an opening, and neither rung moves it by one inch.** Closing 5h means the terminal MSM is VERIFIED, not that the argument behind it is SOUND. The temptation to read "the whole of `SRS::verify` now runs in the kernel" as "the IPA is sound" is live, and false. |

### 6.1 Item 5 opened up — the Wrap group check, rung by rung

"Weeks, the largest genuinely-unbuilt block" was an estimate over an unmeasured object. Measured,
it is **eight rungs of very unequal size**, and the two facts that reorder them are:

1. **The devnet blockchain Wrap index has ZERO `linearization.index_terms`.** Every selector,
   coefficient and witness column the linearization could reference has its evaluation *supplied*
   by the proof, so kimchi folds it into the linearization **constant term** — the scalar C5 /
   `ftEval0R` already reproduces on this block. The only column with no supplied evaluation is
   `sigma_comm[PERMUTS−1]` (`s` carries `PERMUTS−1 = 6` evaluations, not 7). So the "linearization
   commitment MSM" that item 5 named as a major sub-block is a **one-term MSM**.
2. **The terminal `msm == 0` is 82 non-SRS points plus `|srs.g| = 32768`.** Counted from
   `ipa.rs:170-285` on this block: `H`, `sg`, `u`, 2×15 `lr`, the 47 combined commitments, `u`
   again, `delta`. Everything expensive is the one `⟨s, G⟩` term.

**Unit of cost, RE-MEASURED 2026-07-28 with isolated micro-benchmarks rather than extrapolated
off a rung.** The atom is the RCB complete add: 2048 bare `rcbAddM` cost **3.0 s** over a 2.1 s
empty-module baseline, i.e. **≈ 1.5 ms** each (every `by decide` pays it twice — elaborator, then
kernel recheck). Everything else is that atom times a count. A 255-bit double-and-add ladder is
`2 × 255 = 510` complete adds and measured **0.94 s** (8 ladders → 9.1 s, 24 → 25 s; marginal
0.99 s). Time is linear in complete adds. **Memory is not** — it tracks the largest single
`decide`, which is why the 5h work is cut into 32 chunk theorems across 4 modules.

**Both numbers this section used to quote for 5h were wrong, and they are retired.** The ~18 h
came from reading 2 s per *term* off 6.1d's 47-term Horner — which pays considerably more than one
ladder per term — and multiplying by 32768; the honest naive figure is `32768 × 0.94 s ≈ **8.6
hours**. The ~7 TB was an upper bound on a shape nobody should build: peak RSS tracks the largest
single `decide`, so chunking bounds it at **~14 GB per 1024-term chunk** no matter how large the
total is. Measured peak for the whole of 5h: **~28 GB**, not 7 TB — a factor of 250,000 out.

**A third measured wall, which no extrapolation would have found.** The kernel's `whnf` builds a
`List.foldl` accumulator as a THUNK CHAIN of depth `nbits × terms`; at `255 × 1024 ≈ 2.6·10^5`
frames it does not slow down, it **aborts** — `Stack overflow detected.`, exit 134, and
`ulimit -s unlimited` does not help because Lean checks its own `--tstack`. That is why a 1024-term
chunk below is evaluated as two 512-term folds ADDED, not as one 1024-term fold.

### ⚑ What gate the `*-AIR-*` rows below are priced against — read before their numbers

Rungs `5a`–`5h` are **kernel** results: `decide`d equalities over `ZMod`, where the Pasta arithmetic
is exact by construction. The seconds and gigabytes in those rows measure Lean.

The `5h-AIR`, `5h-AIR-BOUND` and `5h-AIR-CURVE` rows measure something else — **emitted AIRs put
through the deployed STARK prover** — and every constraint count, column count, row count,
millisecond and proof-byte figure in them is denominated in `Dregg2.Circuit.Emit.PastaField`'s
EMITTED multiply: `fpMulCore`, ONE degree-2 gate of 81 cross-products, with `"ranges": []`, no
carry pins, and `pastaLimbRange` emitted nowhere in the tree. Measured on the checked-in bytes
(`circuit/descriptors/by-name/pasta-rcb-windowed.json` and the eight `pasta-rcb-sg-slice-*`):
the only booleanity gates are on `BIT` and `DBL`; the 19 carry/borrow columns and the 126 quotient
columns are free, each local to one constraint, with coefficients that are nonzero mod
`p_babybear`. **So in the field the prover checks, those gates hold at every operand triple**
(`PastaField` §6.4) — the emitted objects do not enforce their own field arithmetic, and the
descriptor parser folds their 495-bit ℤ coefficients into felts to read them at all
(`circuit/src/lean_descriptor_air.rs::parse_int_field`).

A multiply that IS sound at BabyBear is a different encoding — 13-bit limbs, 20 of them, ≈10³
constraints (§1b of `LightClientMinaAir`, and `LightClientMinaLinkAir` §"Why (iii) is a wall") —
so a complete RCB add goes from 33 constraints to ≈1.6·10⁴ and **every millisecond and row figure
in those three rows is ~10³ short of the sound object's.** Nothing is retracted: they are correct
measurements of what is on disk, and the forgeries they refuse (a substituted generator, a
`(0,0,0)` accumulator, a flipped digit) are refused by the exact-public LogUp balance and the
curve gates, which owe nothing to the multiply. What does NOT survive the correction is reading
"1,056,896 rows pads to `2^21` exactly" as *nearly affordable*: for a sound gate it is ~10³ past
the ceiling, which is why the standing verdict is **defer the IPA leg, do not optimise it**
(`PastaMsmLayouts` §7.2) and the reachable architecture is the Mina-side shrink terminal.

| rung | what | scalar-muls | status |
|---|---|---|---|
| **5a** | `f_comm` = the linearization MSM (`perm_scalars · sigma_comm[6]`) | 1 | **DONE** — `MinaWrapGroupGate.fComm_reproduces_kimchi` |
| **5b** | `chunk_commitment(t_comm, ζ^{2^15})` — Horner over the block's 7 real `t_comm` points | 6 | **DONE** — `chunkedT_reproduces_kimchi` |
| **5c** | **`ft_comm`** = `chunk(f_comm) − (ζⁿ−1)·chunk(t_comm)`, Maller's optimization | 10 | **DONE** — `ftComm_reproduces_kimchi`, and the gold is **pinned by o1-labs' own `SRS::verify`** on the real opening proof (refuted at `ft_comm + G`) |
| **5d** | `combine_commitments` — the 47-term `Σ ξⁱ·Cᵢ` aggregation that feeds the terminal MSM | 46 | **DONE** — `MinaWrapAggregationGate.combinedComm_reproduces_kimchi`, and `combinedComm_from_our_ftComm` fills the `ft_comm` slot with 5c's kernel-computed point rather than the dumped gold |
| **5e** | `public_comm` = `MSM(lagrange[0..40], −public_input)` + blinder | 40 | **DONE** — `MinaWrapPublicCommGate.publicComm_reproduces_kimchi`, 11 theorems, **159 s**. And `publicComm_is_the_transcript_preimage`: the point the kernel builds from the block's 40 public inputs IS the `(x, y)` C3 absorbs third, so the public-commitment coordinates are **derived, not eaten**. Pinned by o1-labs' `commit_public` and refuted at `public_comm + G` through their own `SRS::verify`. The blinder is a FIXED `+1·h` (`mask_custom` with `PolyComm::one`), and `tamper_blinder_dropped` says it is load-bearing anyway. |
| **5f** | **`check_bulletproof` minus `⟨s,G⟩`** — the `lr` fold, `sg`, `delta`, `u_base`, `c` | 34 | **DONE — this is the rung that opens a commitment.** `MinaWrapOpeningGate.opening_relation_holds`, 26 theorems, **153 s**; plus `MinaWrapOpeningWeld` (**75 s**, 80 ladders in one `decide`) which re-states it with the 47-term aggregate supplied by 5d's own kernel fold rather than the dumped gold. See "what 5f establishes vs assumes" below. |
| **5g** | the recursion commitments as `⟨b_poly_coefficients(chals), G⟩` | 2 × 2^15 | **NOT BUILT — but RE-PRICED, and the old price was the thing stopping it.** "~36 hours and ~14 TB, twice 5h" was twice a figure that was itself wrong twice over. 5g is the SAME OBJECT as 5h — an `⟨sVec(chals), srs.g⟩` against the same 32768 generators, just with the two carried accumulators' challenge lists instead of the opening's — so it collapses identically: **2 × ~3.5 h of serial kernel, or ~3.5 h of wall at the 2-way parallelism 5h actually ran at** by §6.1's measured route, memory bounded by the chunk width exactly as 5h's is. What it needs that 5h did not is only DATA: the two `RecursionChallenge` challenge lists, their `comm` points, and 2 × 32 chunk partials from the extractor. It is the obligation K4c prices (`sVec_eq_bPoly`, `deferral_compression`); P1 (`accumulator_check_splits`) proved the real MSM splits into these blocks; and openmina's `accumulator_check` asserts it on THIS block in Rust (ground truth 2). **It is now a fixture-and-scheduling item, not a wall.** |
| **5h** | **`⟨s, G⟩`** — the 2^15-term SRS MSM inside the terminal `msm == 0` | 32768 | **DONE, 2026-07-28. NOT deferred, in this kernel, on this block.** `MinaWrapSgCore` + `MinaWrapSgChunk0..3`: 32 index-pinned chunk theorems over all 32768 real SRS generators, plus the re-sum to the block's own `sg`. **The 32768 scalars are DERIVED in-kernel** — `PastaIPA.sVec` of the block's 15 IPA challenges, which `MinaRealBlockTranscript`/`derived_ipa_challenges` derive from its own sponge — so this rung eats `srs.g` and nothing else. Measured end to end, not extrapolated: **105 min of wall at 2-way module parallelism = ~3.5 h of serial kernel, ~28 GB peak** (plus 128 s for `MinaWrapSgCore` and ~32 s per build just to ELABORATE the 32768-literal SRS fixture, before any `decide` runs), against the retired estimate of 18 h / 7 TB. Independently cross-checked outside Lean: an arkworks-free Python reimplementation of `sVec` + the Pallas group reproduces all 32 partials and their re-sum to `sg`, so three implementations agree. |
| **5h-AIR** | the SAME `⟨s, G⟩` leg as a **STARK PROOF**, cut FOUR ways | 4 × 8192 | **BUILT AND PROVED, 2026-07-29 — and it is a DIFFERENT OBJECT from 5h above.** `Dregg2/Circuit/Emit/PastaMsmSliced.lean`: four Lean-authored AIR instances, each NAMING ITS OWN SLICE, riding in ONE batch STARK proof with per-instance `degree_bits`. `slicedRowDesc_extends_windowed` proves `PastaMsmWindowed`'s 45 constraints are still a PREFIX of the emitted 78, so the row layout is reused rather than re-authored; the slice offset is a LITERAL in the emitted gate, and `[lo,hi)` plus the 27-limb partial are public inputs. `slices_compose` (slice-count-independent, arbitrary `AddCommGroup`) is the theorem that the four partials sum to the whole MSM. Measured: 4 instances, `degree_bits [7,7,7,7]`, prove 514 ms, verify 14 ms, 314,077-byte proof; **nine tampers REFUSED by the deployed verifier**, each naming its instance. ⚑ **READ THE DIFFERENCE.** Rung 5h binds the CONTENTS — the real `srs.g`, the real derived `sVec` — and produces NO proof object. 5h-AIR produces a proof object and does **not** bind the contents: nothing in the emitted constraints says a row's `SRC` carries `srs.g[lo+t]`. Neither subsumes the other, and "rung 5h is proved" is ambiguous between them. ⚑ **THAT CONTENT GAP IS NOW CLOSED — see `5h-AIR-BOUND` below**, which is what the "named, unbuilt rung" (an exact-public table of `(absolute index, generator limbs)` plus a threaded index column with a per-row lookup) turned into. This row stands as the contents-UNBOUND object, and `circuit/tests/pasta_bound_sg_prove.rs::substituted_generator_before_and_after` now uses it as the BEFORE half of a measurement: it PROVES AND VERIFIES a trace in which one term is a different real Mina SRS generator. ⚑ **AND THE CUT IS AT THE CEILING, not half of it:** 1,056,896 raw rows PADS TO `2^21` exactly, so "50.4%" is 50.4% of the raw rows and 100% of the committed domain. The cut that leaves headroom once padding is priced is EIGHT (4,096 generators, 528,512 rows, padding to `2^20`). The prover wall itself is elsewhere: measured linear at ~1.05 µs/cell from `2^7` to `2^18` (138M cells, 287 s) with no failure, so a `2^21` instance extrapolates to ~38 min and the real cut to ~2.5 h — a scheduling problem, not a structural one. What is PROVED is the same Lean `def` at width 8; the width-8192 descriptors are ACCEPTED by the deployed structural checker and their traces are not proved. |
| **5h-AIR-BOUND** | the same leg with the row CONTENTS forced to be `srs.g` | 4 × 31 proved (the leg is 4 × 8192) | **BUILT AND PROVED, 2026-07-29 — this is the rung between "a proof of a shape" and "a proof of the Mina claim".** `Dregg2/Circuit/Emit/PastaMsmBound.lean` (Lean-authored AIR; `boundRowDesc_extends_sliced` proves `PastaMsmSliced`'s 78 constraints are still a PREFIX of the emitted 82). Each descriptor declares an EXACT-PUBLIC table whose rows are `(row key, absolute generator index, digit, 27 generator limbs)` for the REAL `srs.g[31k .. 31k+31)`, plus a threaded row-index column `TIDX` (first-row `.boundary` pin + a `windowGate` thread), a threaded absolute-index column `GIDX` (resets to the slice's own literal `lo` after each doubling row) and ONE `(1−DBL)`-guarded per-row lookup. ⚑ **The primitive is stronger than a subset lookup**: `DescriptorIR2.PublicLookupBalanced` demands the trace's lookup multiset be a PERMUTATION of the descriptor-carried manifest, so the manifest says THESE ROWS AND NO OTHERS. **`row_tuple_is_its_manifest_row` is the deliverable and it is ROW-COUNT-INDEPENDENT** — pure membership plus `manifest_key_unique` (no counting, no pigeonhole); `i`, `w` and `planes` occur in no bound. It buys more than the generators: `bound_forces_doubling`/`bound_forces_dbl_off` DERIVE the `DBL` pattern `PastaMsmWindowed` §6.1 left hypothesised, `bound_forces_digit` pins the digit, `bound_forces_gidx` pins the absolute index, and `manifest_names_slice_index` + `slice_generator_is_sliceAt` join the forcing to `slices_compose`'s `sliceAt w k gens`. **MEASURED** (`pasta_bound_sg_prove.rs`, 9 tests green): 4 slices × 31 real generators × 4 planes = 128 rows × 529 columns each, 4 + 512 batch instances, prove **782 ms**, verify **113 ms**, proof **2,409,649 bytes** — against the contents-UNBOUND cut at the same trace geometry on the same box (4 instances, 539 ms / 15 ms / 314,077 bytes), so the table costs **+2 trace columns, +4 constraints, 128x30 = 3,840 manifest cells and +512 batch instances per cut**, i.e. **+0.47 ms prove and +4.1 KB of proof per manifest row** (a 7.7x proof and 7.6x verify blow-up, 1.45x prove); the manifest is differentially checked, cell by cell, against the checked-in `MinaWrapSrsG.lean` (496 rows, 124 distinct generators). **THE TAMPER THIS RUNG EXISTS FOR FIRES**: one conditional-add row rebuilt around a DIFFERENT REAL Mina SRS generator with the whole trace regenerated around it — arithmetically perfect, forged only in its TERMS — is ACCEPTED by the contents-unbound descriptor and REFUSED here with the deployed verifier's own `LookupError("GlobalCumulativeMismatch(None): ir2_exact_public_47")`. Six further tampers (row key, absolute index, digit, one source limb, declared bound, a DROPPED term) all refused. ⚠ **WHAT IT DOES NOT DO.** (i) The DEPLOYED exact-public tooth caps a manifest at `MAX_EXACT_PUBLIC_ROWS = 128` / `MAX_EXACT_PUBLIC_CELLS = 4096` and `instance_airs` spends ONE batch AIR instance per manifest row; because the balance is a PERMUTATION, **manifest rows = trace rows**, so a contents-bound instance is at most 128 rows tall. The real four-way cut needs 1,048,704 manifest rows (**8,193× the cap**) and the eight-way cut 524,416 (**4,097×**) — so **the table does not fit the real cut at any of the cuts on the table**, and that is a REALIZATION limit, not a row-count limit in the theorems. What would carry it is a multiplicity-bearing single-instance table (the shape the byte table already has), i.e. a new `Ir2Air` arm — named, unbuilt. (ii) The manifest's GENERATORS are Mina's; its SCALARS are synthetic — binding the s-vector to the block's 15 IPA challenges is a different rung (`MinaWrapSgCore.SVEC` derives it in the kernel; nothing here touches it). (iii) The ℤ↔felt gap and P10 are untouched. ⛑ **(iii-a) THE RCB-FORMULA→GROUP-LAW TRANSPORT IS NO LONGER MERELY "UNTOUCHED" — IT WAS A LIVE FORGERY AGAINST THIS EXACT DESCRIPTOR, and it is half closed: see `5h-AIR-CURVE` below.** The descriptor on this row PROVES AND VERIFIES a trace whose accumulator is `(0,0,0)` throughout, carrying these same real Mina generators and these same declared digits. |
| **5h-AIR-CURVE** | the same leg with both RCB operands forced to be POINTS OF THE CURVE | 4 × 31 proved (the leg is 4 × 8192) | **BUILT AND PROVED, 2026-07-29 — and what it closed was a LIVE FORGERY, not a bookkeeping residual.** `Dregg2/Circuit/Emit/PastaMsmOnCurve.lean` (Lean-authored AIR; `onCurveRowDesc_extends_bound` proves `PastaMsmBound`'s 82 constraints are still a PREFIX of the emitted 98, and the exact-public manifest is byte-identical — checked on the EMITTED BYTES by `pasta_oncurve_gate.rs`, not only in the kernel). ⚑ **THE HOLE.** Every rung up to `5h-AIR-BOUND` (and `PastaMsmScalarBound`, the scalar half) forces `hornerRefFrom` — a fold of the RCB **FORMULA** over projective triples. RCB'15 Thm 1's hypothesis is that the operands are ON THE CURVE and **nothing in the emitted constraints said so**. RCB Alg. 7 at `Q = O` returns `Y₁·(X₁,Y₁,Z₁)`, so at `Y₁ = 0` it is `(0,0,0)`, which is **ABSORBING** (`origin_is_absorbing`, a `ring` identity for every addend) and passes `PastaMsmAir`'s terminal `X ≡ 0 ∧ Z ≡ 0` predicate. **MEASURED, BEFORE AND AFTER**: `pasta_oncurve_gate.rs::absorbing_state_before_and_after` takes the free initial accumulator to `(0,0,0)` — nothing pins it — keeps the REAL Mina generators in `SRC` and the REAL declared digits in `BIT`, so every RCB add, carry, quotient, thread, `DBL` pin and the whole exact-public lookup still hold EXACTLY; the `5h-AIR-BOUND` descriptor **PROVES IT AND THE DEPLOYED VERIFIER ACCEPTS IT**, publishing a partial that passes the terminal predicate. That is the Mina claim, forged, with every binding rung green. The curve-gated descriptor **REFUSES it** (`OodEvaluationMismatch { index: Some(0) }`). ⛑ **AND THE CURVE EQUATION ALONE CANNOT CLOSE IT**: `Y²Z = X³ + bZ³` is HOMOGENEOUS, so `(0,0,0)` **satisfies it**. What closes it is a NON-DEGENERACY witness — `Y·YINV ≡ 1`, i.e. `Y` a unit — which on Pallas (prime order ⇒ no 2-torsion) is EQUIVALENT to "this triple is a point of `P²` on the curve", and is the same condition RCB needs for `P + O` to return a correct representative. **EMITTED**: 8 constraints / 135 columns per gated point (5 `fpMulCore`, 1 `fpSMulCore`, 1 bespoke degree-2 curve head with a `+2p` constant so ONE non-negative quotient group covers it, 1 inverse head), on BOTH operands of every row's add. `OP` needs no gate (`condRef_is_a_curve_point`); `OUT` needs none (the emitted thread makes it the next row's `ACC`). **PRICE**: 82 → **98 constraints**, 529 → **799 columns**; manifest, row count, table id, PI count all UNCHANGED. Prove **838 ms**, verify **53 ms**, proof **495,512 bytes** across 8 batch instances (against 782 ms / 113 ms / 2,409,649 bytes for `5h-AIR-BOUND` before `ExactPublicTable` landed). **THEOREMS**: `onCurve_forces` (the emitted 8 gates ⟹ the point is on the curve with `Y` a unit); `fold_accumulator_is_a_curve_point`, which composes `PastaMsmWindowed.windowedRows_forces` UNMODIFIED so *every* accumulator the whole fold passes through is a curve point; `skip_is_projective_identity` (the `O`-skip is a no-op **exactly because** `Y` is a unit — `PastaMsmWindowed` §6.3's wound, as a theorem); `terminal_is_the_identity` **+** `origin_is_not_the_identity` (the terminal predicate finally MEANS the identity; before the gate it accepted a non-point). **SATISFIABLE AT BIRTH**: the honest cut proves AND verifies, and **500 of 512** honest accumulators are NON-AFFINE — a gate accepting only `Z = 1` would have refused every honest trace, so the exhibit is on the shape the fold really produces. **ALL THREE TAMPERS LIVE ON ONE INSTANCE**: curve (`OodEvaluationMismatch index 0`), substituted-generator (`LookupError GlobalCumulativeMismatch: ir2_exact_public_47`), flipped-digit (`OodEvaluationMismatch index 4`), plus a forged `Y = 0` accumulator and an off-curve source. 10 tests green. ⚠ **WHAT IT DOES NOT DO, and read WHICH half.** RCB'15 Thm 1 named two things. Its **HYPOTHESES** — operands on the curve — were checked by NOTHING and are now **FORCED**. Its **CONCLUSION** — that `rcbOutG` at on-curve inputs IS the group sum — remains an **inherited citation**. Discharging it needs (1) a formal Pallas group law (mathlib's `WeierstrassCurve.Projective` instantiated at `p, a=0, b=5`) and (2) a cofactor certificate for a **degree-12 identity in 6 variables**, produced outside Lean and checked inside it — a distinct formalization, not a deferral. And one hypothesis can never be a gate: **Pallas has cofactor 1** is a fact about the curve's ORDER, inherited from `mina-curves`, and it is what makes the `Y ≠ 0` gate a non-degeneracy rather than an over-restriction. **So a verified proof of this AIR constrains a formula fold OVER CURVE POINTS — not yet a group-law MSM.** ℤ↔felt (K1) and P10 untouched. |

**What rung 5f establishes, and what it assumes — both, in the same breath.**

`SRS::verify` (`poly-commitment/src/ipa.rs:118-300`) folds two independent statements into one
randomised MSM with independent randomisers `rand_base` and `sg_rand_base`:

```text
(A)  sg == ⟨s, srs.g⟩                                    -- rung 5h; CHECKED in-kernel (2026-07-28)
(B)  c·Q + delta − z1·sg − z1·b0·U − z2·H == O            -- rung 5f; THIS
     where  Q = Σⱼ (chal_invⱼ·Lⱼ + chalⱼ·Rⱼ) + Σᵢ ξⁱ·Cᵢ + cip·U
```

**Establishes.** (B) holds in the Lean kernel, over K4a's complete add and K4b's 255-bit ladder,
on the block's own 15 `lr` pairs, `sg`, `delta`, the 47-term aggregate and a derived `u_base` —
and **at challenges the block's own transcript samples, not carried ones**. §3's sponge continues
from `o.fq_sponge` (the state right after ζ′, since `oracles` takes its `digest()` on a clone)
through `absorb_fr(shift_scalar(cip))` → `challenge_fq` → 15 `absorb_g(L)/absorb_g(R)/squeeze`
rounds → `absorb_g(delta)`, and **all 16 challenges of the opening argument fall out of it**.
`b0` is re-derived as `b_poly(chal, ζ) + r·b_poly(chal, ζω)` at the gate's own ζ and `r`;
`chal_inv` is checked to be the inverse of `chal`; `cip` is proved equal to the gate's `CIP`,
which C8 already proved is the (ξ, r)-fold of the block's **claimed evaluations**. So (B) is the
first statement in this campaign whose truth says a *committed polynomial has the evaluation the
proof claims*.

`u_base` is derived too: the SvdW group map (`groupmap/src/lib.rs:65-125`) is run in-kernel on the
full `challenge_fq` squeeze, with the inverse `alpha` and the square root as witnesses, and — this
is the part that is easy to skip — **the two skipped candidate x's are certified as non-residues
by Euler's criterion**, so the branch `get_xy`'s search takes is derived rather than transcribed.
The one thing that is not: which of `±y` arkworks' `sqrt()` returns. `tamper_u_base_sign` bounds
that by showing the other root breaks the relation, so the sign is pinned by o1-labs' output.

**Assumes, and does not discharge:**

1. **P10.** (B) is the verifier's *check*. That a prover passing it must KNOW an opening is the
   IPA/dlog extraction argument, undischarged here and everywhere in this stack. **"We opened a
   commitment" means "the opening check passes", not "the opening is sound".**
2. **(A) — DISCHARGED 2026-07-28, so this is no longer an assumption of 5f.** (B) uses `sg` as the
   IPA's final `G`. Rung 5h now proves in-kernel that that `sg` really is
   `⟨b_poly_coefficients(chal), srs.g⟩`, with the coefficient vector derived from the 15 challenges
   rather than supplied. What (A) still rests on is **the SRS itself**: that the 32768 points in
   `MinaWrapSrsG` ARE the devnet blockchain Wrap SRS. They are a fixture, emitted from openmina's
   `vi.srs().g`, and nothing in-kernel derives them — see residual 3, which 5h makes considerably
   more load-bearing than it was.
3. Poseidon's collision resistance; `p` prime (Euler); and the SRS itself — that `srs.g` and
   `srs.h` are what they claim is checked by nothing here. **Since 5h this is the largest single
   piece of trusted data in the stack**: 32768 committed points, on-curve-checked in-kernel
   (`srs_g_on_curve`) but not derived. The real derivation is `point_of_random_bytes` over a
   BLAKE2b counter (`ipa.rs`), which needs an in-kernel BLAKE2b and the SvdW map at 32768 inputs —
   a named, buildable item, and now the honest next rung of this arc.

**Order to build them in:** 5g is next and cheap now — same shape as 5h, needs only the two
accumulators' fixtures. Then item 6 (P3/P4). Neither moves P10, which is the extraction argument
and belongs with the FRI/IPA floor work; and neither derives `srs.g`, which is residual 3.

---

## 7. 2026-07-29 — the first of this content DEPLOYED, and the measured wall in front of the rest

Everything above runs in a `lake build`. The observer that actually watches Mina
(`bridge/src/mina_observer.rs`) called **none** of it: it passed a compile-time constant,
`NEUTRAL_PICKLES_OK = true`, for the Pickles conjunct of its light-client gate, because
`bestChain` did not fetch `protocolStateProof`. That constant is **deleted**.

**What is deployed now.** `bestChain` fetches `protocolStateProof`; `bridge/src/mina_pickles.rs`
decodes the base64url binprot `Mina_base.Proof.Stable.V2` byte-exactly (every `PaddedSeq`
terminator, every `Option` tag, canonical binprot integer widths, canonical field elements against
both Pasta moduli, and **exact-fit** — on the real block, 294 field elements checked and all 11138
bytes consumed); and the decoded counts cross into a new `@[export]`,
`Dregg2.Bridge.PicklesWrapShapeGate.dregg_mina_wrap_shape_ok`, whose decision
`picklesWrapShapeOk_is_shapeOkRec` proves **is** `KimchiVerify.shapeOkRec` plus two length
agreements a recursive Wrap proof owes (accumulator commitments = challenge vectors, and
`lr.len() = log₂ max_poly_size`). `real_block_wrap_shape_accepts` and
`real_block_wrap_shape_refused_by_freeze` pin both directions on block 539508. Fail-closed: an
absent export is a REFUSAL, and the Rust decode refusals fire **before** the gate, so they have
teeth with no archive at all.

**The Rust decoder independently confirms this document's own numbers**, from the block's bytes
rather than from openmina: `prev_challenges = 2`, `w_comm = 15`, `t_comm = 7`, `s = 6`,
`coefficients = 15`, `lr = 15`, and `branch_data = {proofs_verified: N2, domain_log2: 16}` — §4.2's
correction, re-measured by a third implementation.

**⚑ The measured wall, which is the finding.** Nothing else in §3 is runtime-evaluable, for two
independent reasons and it is worth being precise about both:

* **DATA.** Every arithmetic theorem here is `by decide` over *literal constants of one extracted
  block*. The values are not on the wire — the proof's `messages_for_next_step_proof.app_state` is
  literally `()`, so a Wrap proof does not even carry the block it proves — and reconstructing them
  needs the verifier index, `srs.g`, `endo_r`, the linearization and the 40-element public input,
  i.e. openmina + `proof-systems`, a dependency graph deliberately kept out of the breadstuffs
  lockfile (see the extractor's `[workspace]` stanza).
* **COST.** Even given the data, these are kernel `decide`s, not functions of a proof: 82 s for
  C5/C8, 153 s + 75 s for the opening rung, ~3.5 h of serial kernel and ~28 GB peak for 5h — **per
  block**. A light client at one block per ~3 minutes cannot spend hours per block.

So the honest split is: **the preamble is runtime-evaluable and now runs; the arithmetic is
fixture-bound and does not.** The next rung that genuinely crosses the line is *curve membership*
of the ~58 group elements the decoder already parses — `y² = x³ + 5` in **compiled** Lean over
`ZMod` is microseconds per point, not kernel-`decide` hours — and it is deliberately not written in
Rust. After that, the proof↔block binding (the public-input assembly), which is the same object
P8/P9 needs.

**Say it at the right resolution, again:** the observer now refuses a block whose blockchain SNARK
is absent, malformed, or of the wrong shape. It does not verify that SNARK, it does not check the
SNARK belongs to that block, and it does not do fork choice. Verifying each block's proof is
necessary for a Mina light client and nowhere near sufficient.

**Say it at the right resolution:** we do not verify a Mina block. We check, in-kernel, on a real
Mina block, that its shape is the shape the real verifier index demands, that the accumulator
evaluations it exposes are the b-polynomial of the challenges it carries, that its aggregated
opening value and `ft(ζ)` are what the claimed evaluations and the sampled challenges produce,
that **those challenges are the ones its own transcript samples** rather than the ones it hands
us, and — since rungs 5e–5f — that its public commitment is a commitment to its public input and
that **the IPA opening relation holds for the aggregate of all 47 of its commitments**. Two
sentences that were true this morning are now false: *"no group element is touched by any check"*
and *"no check says a commitment is a commitment to anything."* A third sentence went false on 2026-07-28: *"and it rests on
`sg == ⟨s, srs.g⟩`, which is measured in Rust and not in this kernel."* It is measured in this
kernel now — all 32768 terms of it, against a coefficient vector the kernel builds from the
block's own 15 challenges. What is still true, and is the whole of the remaining distance: the
opening relation is the verifier's **check**, not the extraction argument behind it (P10); the
32768 SRS generators are trusted data, not derived (residual 3); and the two recursion
commitments are still unchecked (5g). The gap between here and a light client is 5g, item 6 and
`srs.g`'s derivation, on top of that floor.

## 8. 2026-07-29 — the proof↔block binding: what it actually is, and the half that closed

§7 ended by naming the next rung: *"the proof↔block binding (the public-input assembly)."* That
framing was right about the object and wrong about the shape of the problem, and getting it exact
is most of this section's value.

### 8.1 The question, stated precisely

The attack is: an endpoint serves **block A's proof under block B's header**. Every check §7
deployed still passes — the state-hash decode, the canonicality, the parent linkage, the height
contiguity, the byte-exact binprot decode, and `dregg_mina_wrap_shape_ok`. In its cheap form this
is not subtle: **one** real Mina proof, replayed under 290 fabricated headers, manufactured any
confirmation depth for free, and the "availability obligation" §7 claimed to buy cost an adversary
exactly one proof.

### 8.2 Where the block actually enters — measured, from both implementations

A Wrap proof's `messages_for_next_step_proof.app_state` is literally `()` on the wire
(`mina/src/lib/pickles/proof.ml:121`; openmina's generated type has `app_state: ()` with an
`always_unit` deserializer). The block enters only as the **verifier-supplied** `app_state`:

* OCaml `pickles/verify.ml:159` builds the prepared statement with
  `{ t.statement.messages_for_next_step_proof with app_state }` — the wire `()` is *overwritten* by
  the caller's value — and `blockchain_snark_state.ml:384` fixes what that value is:
  `to_field_elements (t : Protocol_state.Value.t) = [| (Protocol_state.hashes t).state_hash |]`.
  **One field element: the block's state hash.**
* openmina `verification.rs:750` `verify_block` does the same, discarding the wire field with a
  literal `app_state: _, // unused` and passing `MinaHash::hash(&protocol_state)`.

That value is absorbed by `hash_messages_for_next_step_proof` — a prefix-free Poseidon over
`index_to_field_elements(dlog_plonk_index)` (56 elements, the VK) `++ [state_hash]` (1) `++` the
two `(commitment, 16 challenges)` accumulator groups (36) = **93 field elements** — and the digest
lands at **public-input slot 12 of 40** (`prepared_statement.rs`, `to_public_input`).

**Slot 12 is the ONLY block-dependent slot.** The other 39 are functions of the proof alone.

### 8.3 The consequence, which is not the one §7 anticipated

Because the public input is *derived* from `(block, proof, VK)`, computing it is never a check — it
always succeeds. **The binding is not a comparison anyone can make; it is a conjunct of the full
Wrap verification.** The shortest closed loop from a block's `stateHash` to a value the proof
itself exhibits is: slot 12 → the 40-word public input → `public_comm` (a 40-point MSM over the
Lagrange basis) → the Fq-sponge → `β, γ, α′, ζ′`, which *are* on the wire in the proof's own
statement. And six of those 40 words — `combined_inner_product`, `b`, `zeta_to_srs_length`,
`zeta_to_domain_size`, `perm`, `xi` — are **dropped from the wire proof** and recoverable only by
`expand_deferred`, i.e. the front half of a Kimchi verifier.

⚑ **The public API is NOT the obstruction, and this reverses a plausible prior guess.**
`stateHash` + `protocolStateProof.base64` + the blockchain VK is provably sufficient to assemble
all 40 words: the extractor already does exactly this and o1-labs' own `kimchi::verifier::verify`
accepts the result (§2, ground truth 3). What is missing is **computation, not a source.**

(A separate and real GraphQL gap, which the `subWindowDensities` lane also found: you cannot
*re-derive* `state_hash` from the served header. `Filtered_external_transition.Protocol_state` drops
`genesis_state_hash` and `constants` before GraphQL sees them, and `sub_window_densities`,
`genesis_ledger_hash` and the whole `ledger_proof_statement` have no resolver. So the binprot
`Protocol_state.Value` — libp2p RPC or a precomputed-block file, not the public API — is what a
verifier would need to check that a served `stateHash` is the hash of a served header. That is a
different hole from this one, and it is open.)

### 8.4 What DID close: the proof↔**proof** chain

Pickles recursion makes block N's Step proof verify block N−1's Wrap proof, so block N's own bytes
carry **two fingerprints of its parent's proof**, in the clear, comparable with zero arithmetic:

| in block N's proof | equals, in block N−1's proof |
|---|---|
| `messages_for_next_step_proof.challenge_polynomial_commitments[0]` | `bulletproof.challenge_polynomial_commitment` (`sg`) |
| `messages_for_next_step_proof.old_bulletproof_challenges[0]` | `statement.proof_state.deferred_values.bulletproof_challenges` (16) |

MEASURED on **40 consecutive real devnet blocks (539761…539800)**, 39 adjacent pairs: **39/39 on
both fingerprints**, 40/40 distinct `sg`, 0 self-naming blocks, and 0 non-adjacent coincidences.
Five of them are tracked at `metatheory/fixtures/pickles-extractors/mina_devnet_run.json`.

Deployed as `@[export] dregg_mina_proof_chain_ok`
(`Dregg2.Bridge.PicklesProofChainGate`), called once per adjacent pair by
`MinaObserver::check_proof_chain`. `chainOk_adjacent_proofs_differ` proves the payoff — **an
accepted segment cannot serve the same proof twice in a row** — and `chainOk_pins_every_seam`
proves every adjacency is checked, so runs cannot be spliced, shuffled or padded.
`real_devnet_run_chains` pins the accept on 539795→539796→539797 and
`real_devnet_chain_discriminates` pins fourteen refusals (replay, swap, reorder, splice, coordinate
tamper, challenge tamper, arity, degenerate accumulator) on the same real objects.

⚑ **TRUSTED, named:** that accumulator index `[0]` is the *blockchain* parent's rather than the
transaction SNARK's. That is an empirical reading of those 39 pairs, not a theorem about Pickles.
Index `[1]` took only 4 distinct values over the 40 and is deliberately not projected.

### 8.5 So say it at the right resolution

The observer now requires the exhibited proofs to be a **genuine consecutive run of real Mina Wrap
proofs, in order, of the length claimed**. Replay, shuffle, splice and pad are refusals, and depth
past the real chain's own production is a refusal. **It is still not a proof↔`stateHash` binding:**
an adversary holding a genuine run can re-label the headers those proofs are served under. Closing
*that* means `expand_deferred` + the MSM + two sponges, and the honest cost note is that all three
are compiled-Lean-feasible (milliseconds, not the kernel-`decide` hours §7 measured) — the work is
fidelity to `expand_deferred`, not arithmetic throughput.

And it remains **not a Mina light client**: fork choice is formalized nowhere in this tree, and a
sibling proved Samasika `select` is a **tournament** rather than an order (genuine 3-cycles at real
mainnet constants), so a chain follower needs strictly more than a better binding.

### 8.6 ⚑ A defect §7 shipped, found by pointing the observer at a real node

`bestChain { … protocolStateProof … }` — the query §7 landed — **does not fetch the proof.**
`protocolStateProof` is a GraphQL *object* (`mina_graphql/types.ml:1768`) with `base64` and `json`
fields, and a bare selection returns `{}`. Measured 2026-07-29 against
`api.minascan.io/node/devnet/v1/graphql`: `"protocolStateProof":{}`, with no `errors` array. Every
real block therefore parsed to an empty proof and was refused as `WrapProofAbsent`, so the observer
shipped 2026-07-29 unable to confirm a single live settlement. Fixed to
`protocolStateProof { base64 }`, with a test asserting the subselection is in the query. The
fail-closed posture is exactly why this was survivable rather than silent — but note what found it:
**a real request to a real endpoint**, not any amount of in-tree testing against a mock that had
never seen the server's actual response shape.

## 9. 2026-07-29 — the proof↔`stateHash` binding: what §8 got wrong, and what closed

§8.5 named the next rung and proposed a route to it. The route does not exist. Measuring that is
most of this section's value, and the measurement is reproducible:
`metatheory/fixtures/pickles-extractors/src/bin/state_hash_binding_export.rs`
(`cargo run --release --bin state_hash_binding_export`), over **six real devnet blocks** —
539795…539799 consecutive plus the anchor 539508.

### 9.1 ⚑ The binding is REAL and TIGHT, and o1-labs' verifier says so

| ground truth | result |
|---|---|
| `kimchi::verifier::verify` on each block under its OWN `stateHash` | **6 / 6 `Ok`** |
| ⚑ the same proof under EVERY FOREIGN block's `stateHash` | **30 / 30 `Err`** |
| public-input words other than 12 that move when only the header is swapped | **0**, asserted per word per pair |
| our 93-element `to_fields` transcription vs openmina's private one | **6 / 6 equal** |
| our 32-element `messages_for_next_wrap_proof` transcription | **6 / 6 equal** |

So word 12 — `Poseidon_fp(dlog_plonk_index(56) ‖ state_hash(1) ‖ accumulators(36))` — is the sole
carrier of the block, and moving it alone is enough to make the real verifier refuse. That is no
longer an argument from the type; it is thirty measured refusals from o1-labs' own code.

### 9.2 ⚑ THE HYPOTHESIS §8.5 SHIPPED IS FALSE

§8.5 wrote: *slot 12 → the 40 words → `public_comm` → the Fq-sponge → β, γ, α′, ζ′, **which are on
the wire***. They are not. On the same six blocks, every adjacent pair:

  * child `statement.proof_state.deferred_values.plonk.{beta,gamma,alpha,zeta}`
    vs the parent's Wrap oracles — **0 / 5**;
  * child `sponge_digest_before_evaluations` vs the parent's Wrap `fq_digest` — **0 / 5**.

The reading behind the guess was that a Wrap statement's `deferred_values` describe the previous
Wrap proof. They describe the **Step** proof that Wrap wrapped. A Wrap proof's own Fiat–Shamir
challenges are absorbed into no served field, of its own block or of its child.

**Consequence, and it is the load-bearing sentence of this section:** the only conjunct of
`kimchi::verifier::verify` that a wrong word 12 can falsify is the **terminal IPA opening**. Every
step before it is a derivation that always succeeds. And the opening's honest per-block cost
includes the `2^15`-point `⟨s, srs.g⟩` MSM of §6.1 rung 5h — the family unrooted at `228e51de7`
for being unaffordable in the kernel, and ~2^15 255-bit ladders in compiled code. **There is no
cheap per-block equation. Anyone who writes one down again should re-read §9.2 first.**

### 9.3 What landed

`Dregg2.Bridge.MinaStateHashWordGate`, `@[export] dregg_mina_state_hash_word_ok`, rooted through
`Dregg2/FFI.lean` (the archive boundary — rooting in `Dregg2.lean` emits no `:c` facet):

  * `word12` / `word11` computed from the SERVED `stateHash` and the served proof bytes, in
    **compiled** Lean. The 62 raw 128-bit prechallenges are expanded through
    `KimchiVerify.endoMap` **in Lean** (`expandTick` at `ZMod pN` with Vesta's `endo_r`,
    `expandTock` at `ZMod qN` with Pallas's) — `bridge/src/mina_pickles.rs` was extended to
    project them RAW, so no field arithmetic exists on the Rust side to drift.
  * Pins: 6 real blocks accept, all **30** ordered foreign-header assignments refuse, plus
    accumulator-group swap, per-element tamper, arity, over-wide prechallenge, absent hash, and the
    Fp/Fq parameter mixup. All `#guard` (the compiled evaluator) — the kernel proves the CHECKER
    (`headerOk_entails`, `word12_preimage_is_93`, `state_hash_is_at_index_56`,
    `word12_preimage_carries_the_chain_accumulator`), the differential checks the INSTANCE.
  * ⚑ `word12_preimage_carries_the_chain_accumulator` welds this gate to
    `PicklesProofChainGate`: the accumulator inside word 12's preimage IS the one the chain gate
    compares against the parent block's own `sg`, on both the commitment and the 16 raw
    prechallenges. Word 12 therefore commits the served header **and** the proof's position in the
    chain.
  * `Dregg2.Circuit.Emit.MinaWrapPublicInputFromHeader` (kernel, unrooted) welds word 12 and word
    11 to `MinaWrapPublicCommGate.PUBLIC_INPUT[12]` / `[11]` — the literals C3, C5, C8 and rungs
    5a–5h are stated over. **§3's whole ladder now reads "against the header a devnet node served
    for block 539508", not "against forty numbers".** `no_other_measured_block_is_the_anchor`
    keeps that from being true of a constant.
  * `MinaObserver::check_header_binding`, called from `observe_settlement`, with its own refusal
    variant `ObserveError::HeaderBindingMismatch` — never laundered into `WrapProofNotChained` (a
    chain claim) or `VerifiedGateUnavailable` (a cold path). Tests fire both ways on real bytes:
    the served header accepts, all five foreign real headers refuse.
  * **MEASURED per-block cost: 28.9 ms** through the real C ABI (base64 + binprot decode +
    Base58Check + two Poseidons + 62 endomorphism expansions), `header_binding_is_per_block_cheap`.

### 9.4 A defect this lane paid for, worth one line

Calling the export before `initialize_Dregg2_Dregg2_Bridge_MinaStateHashWordGate` **SIGSEGVs**.
The Mina gates before this one decide over their arguments only; `headerOk` reads top-level
constants (`VK_INDEX`, `fpParams`, `fqParams`), which live in initialized module data. The crash
looks exactly like the missing-archive SIGABRT that `docs/BUILD-BUDGET.md` warns about, and it is
not that. The initializer is now in `lean_init.c` next to the extern.

### 9.5 The distance to a Mina light client, restated

Unchanged in shape and shorter by one item. What remains between here and verifying a Mina block
per-block: `expand_deferred` (the six wire-dropped words — rendered from BOTH implementations in
this lane's research and NOT implemented; they are functions of the proof alone, so they carry no
header), the 40-word assembly, and then the opening — of which 5f is in-kernel at literal
challenges and **5h's `2^15`-point MSM is the wall**. Beyond that: the Wrap VK is trusted config
(P8/P9), the SRS Lagrange basis and `srs.g` are trusted data, and the IPA opening-soundness floor
(P10) is inherited. **And fork choice is still formalized nowhere** — a sibling proved Samasika
`select` is a TOURNAMENT rather than an order at real mainnet constants. None of this is a Mina
light client, and none of it may be described as one.
