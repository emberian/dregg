# DECISION — Field & code choice + PCS soundness

Legend: **[C]** = grounded in `circuit/` code; **[A]** = analysis/inference; **[F]** = from a paper in `pdfs/`.

---

## Exec summary (~10 lines)

1. **[C]** dregg runs on **BabyBear** (`p = 2^31 − 2^27 + 1`) with a **degree-4 binomial challenge extension** (`BinomialExtensionField<BabyBear,4>`, ~124-bit challenge space), FRI-based (log_blowup=3, 50 queries / standalone path 80 queries, blowup≥4), Poseidon2 Merkle, via Plonky3. This is the modern small-prime STARK sweet spot.
2. **RECOMMENDATION: STAY on BabyBear+FRI.** A field/code change is a full rewrite of the prover, all AIRs, the recursion layer, and the verifier. The current stack is mature, transparent, and *already plausibly PQ* (hash-based). Nothing in the option set clears the bar.
3. **[C]** A **Binius (binary-tower) backend already exists** as an optional, `nightly`-gated, `Experimental`-tier *parallel* path (Merkle-membership + fold-step BLAKE3 gadgets only, with a stub fallback). Keep it exactly as that — a research lane, not the spine.
4. **[A]** Binary towers (Binius) win *only* if dregg's dominant cost becomes **bit-level work** (hashing, XOR, range/lookup) AND we are willing to carry a nightly, less-audited toolchain. Threshold below.
5. **[A][F]** Lattice PCS (Greyhound/Hachi) buys **structured-assumption PQ + tiny proofs (~53–55 KB)** but verification is the bottleneck and it abandons the transparent, assumption-light hash model dregg relies on. Not worth a rewrite now.
6. **If** dregg ever moves to a **sumcheck/multilinear AIR**, pair it with a **FRI-based multilinear PCS already in this corpus (BaseFold / WHIR / DeepFold)** — same field, same hashing, same trust model — *not* a new-field PCS.
7. **[F] Soundness lesson (Gemini-565):** the broken "optimization" reused the challenge across recursion rounds (ρ^(2^j) per step) and **dropped a consistency check** between rounds → forge any evaluation. The *original* Gemini and HyperKZG are fine. Lesson: never trust a blog-post "optimization" of a folding/recursive PCS without a soundness proof; test cross-round consistency adversarially.
8. **[F] Soundness lesson (Orion-1164):** even the *patched* Orion was still unsound; the fix (Scorpius) requires the **outer SNARK to actually perform the column-proximity check** and a **distance-preserving code randomization**. Lesson: code-based PCS soundness lives or dies on (a) minimum relative distance and (b) the proximity/consistency check not being elided by an optimization.
9. **MUST-ADD adversarial tests** (none exist at the PCS layer today — **[C]** current soundness tests are AIR-witness-rejection only): proximity-gap forgery, Fiat-Shamir challenge-reuse, grinding/query-count downgrade, extension-field embedding (tininess) checks. Checklist below.
10. **Deciding factor:** alignment with the existing Plonky3 + BabyBear + FRI stack. Every "move" option breaks that alignment for a benefit dregg does not currently need.

---

## dregg's constraints ([C] from `circuit/` vs [A]) — current field, rewrite cost

- **[C] Native field:** BabyBear, `p = 2^31 − 2^27 + 1 = 2013265921` (`circuit/src/field.rs`). Canonical-form `BabyBear(u32)` with normalizing `Eq`/`Hash` to kill malleability — already a soundness-conscious design.
- **[C] Challenge/extension field:** `type EF = BinomialExtensionField<P3BabyBear, 4>` (`circuit/src/plonky3_prover.rs`); `ExtensionMmcs<BabyBear, EF, _>` for FRI challenge commitments. So the *cryptographic* field is ~`p^4 ≈ 2^124`, the *arithmetization* field is the 31-bit prime. This is exactly the ethSTARK/Plonky3 small-field design that Binius's own authors **[F]** describe as the post-2022 norm.
- **[C] A separate `babybear8.rs`** implements the degree-8 tower `BabyBear^4[y]/(y^2−11)` (p^8 ≈ 2^248) — but for **Schnorr ECC** (`schnorr_curve.rs`), not for the PCS. Do not confuse this with a binary tower; it is a prime-field tower for curve security.
- **[C] FRI config:** Plonky3 path `log_blowup=3, num_queries=50, query_pow=16`; the standalone `stark.rs` path documents `NUM_QUERIES=80, MIN_BLOWUP=4`, "FRI security: NUM_QUERIES * log2(blowup) bits." `blowup_for_degree` scales with constraint degree (Poseidon2 S-box degree 7 ⇒ log_blowup≥3). **[A]** These two paths disagree on query count — see Open Questions.
- **[C] Hashing:** Poseidon2 over BabyBear (Merkle + Fiat-Shamir DuplexChallenger). Transparent, no trusted setup, hash-based ⇒ **already plausibly PQ**.
- **[C] Binius backend exists but is peripheral:** `circuit/src/backends/binius.rs` (1352 lines), git-pinned to IrreducibleOSS rev `46eef325`, feature `binius`, **requires nightly**. It implements *only* `prove/verify_merkle_membership` and `prove/verify_fold_step` via the `binius_circuits::blake3::compress` gadget + channels; everything else (predicate AIRs, note-spending, recursion) is **not** ported. Without the feature it emits a **structural stub** that cannot pass real verification, and `proof_tier.rs` classifies Binius as **Experimental**, not Production. **[A]** So Binius is a parallel experiment, not a migration in progress.
- **[A] Rewrite cost to move off BabyBear/FRI = very high:** all `*_air.rs` AIRs, `plonky3_prover.rs`, `plonky3_recursion*.rs`, the verifier-in-circuit (`plonky3_verifier_air.rs`, `poseidon_stark_verifier_circuit.rs`), proof serialization, and the recursion/IVC layer are field- and PCS-specific. This is the spine of the system.

---

## The options (one paragraph each)

**Option A — STAY: BabyBear + degree-4 ext + FRI (Plonky3).** **[F]** The Binius paper itself frames 32-bit-prime + FRI (Plonky3, RISC Zero) as today's "fastest, production-oriented" design. Transparent, hash-based ⇒ plausibly PQ, no structured assumption. Mature, audited, already integrated end-to-end including recursion. Weakness: arithmetization field must be ≥ trace length (the "trace-length barrier" Binius breaks), and bit-level work (hashing, XOR, lookups) pays for embedding into a 31-bit prime.

**Option B — MOVE to binary towers (Binius / Diamond–Posen).** **[F]** Multilinears over the binary tower `GF(2) ⊂ … ⊂ GF(2^128)`; "ring-switching" reduces tiny-field (bit-valued) commitment to a large-field BaseFold-style scheme **with no embedding overhead**. Native 1-bit columns make hashing/bitwise/lookups dramatically cheaper. **[A]** But it is a *different arithmetization model* (commit at `BinaryField1b`, sumcheck over binary towers, Groestl/Grøstl Merkle), younger, **nightly-only in dregg's pin**, and a full rewrite of every AIR. dregg has it wired for two gadgets only.

**Option C — MOVE to lattice PCS (Greyhound / Hachi).** **[F]** Greyhound: first concretely-efficient PCS from *standard* lattice (Module-SIS) assumptions, ~53 KB proofs at N=2^30, composed with LaBRADOR for polylog proofs; verifier `O(√N)`. **[F]** Hachi improves verification ~12.5× via sumcheck + ring-switching over cyclotomic `R_q = Z_q[X]/(X^d+1)`, ~55 KB proofs. PQ under a *structured* assumption (vs hash-based). **[A]** Verification is still the documented bottleneck (Hachi note: hash-based verifies ~2 orders of magnitude faster), it adds a new hardness assumption, and it is a total rewrite. Attractive only if tiny on-chain proof size becomes the hard constraint and we accept Module-SIS.

**Option D (conditional) — sumcheck/multilinear AIR with a FRI multilinear PCS.** If dregg ever swaps univariate STARK/FRI for a sumcheck-based (HyperPlonk-style) arithmetization, the PCS should **stay field-aligned and hash-based**: BaseFold / WHIR / DeepFold (all in this corpus). **[F]** Samaritan and Gemini are *univariate→multilinear* transforms but are KZG-based (trusted setup, pairings, not PQ) — wrong trust model for dregg. **[F]** Fold-DCS (divide-and-conquer sumcheck) cuts sumcheck rounds and soundness error to logarithmic and pairs with a multilinear PCS — useful *if* we go multilinear, orthogonal to the field choice.

---

## Comparison table

| Option | PQ? | Arithmetization field / PCS | Prover / verifier tradeoff | Rewrite cost from Plonky3-prime | Maturity | Known soundness issues |
|---|---|---|---|---|---|---|
| **A. STAY — BabyBear+ext4+FRI** | Yes (hash-based, plausible) | 31-bit prime + deg-4 ext; FRI/RS | Fast prover, log verifier, ~10s–100s KB STARK proofs | **0 (status quo)** | **High** — shipped, recursion done | FRI/RS proximity-gap params must be set conservatively; Fiat-Shamir must bind all transcript |
| **B. MOVE — Binius binary towers** | Yes (hash-based) | `GF(2)`-tower (1b…128b); BaseFold+ring-switching | Best for bit/hash/lookup; no embedding overhead; sumcheck prover | **Very high** — new model, all AIRs, nightly toolchain | **Medium** — newer, fewer audits; **[C]** dregg ports 2 gadgets only | Soundness rests on BaseFold/proximity + ring-switching reduction; younger ⇒ more attack surface |
| **C. MOVE — Lattice (Greyhound/Hachi)** | Yes (Module-SIS, *structured*) | Cyclotomic `R_q`; lattice PCS (+LaBRADOR / sumcheck) | Tiny proofs (~53–55 KB); **verifier is the bottleneck** | **Very high** — new assumption + new prover/verifier | **Low–Medium** — research-grade, prior lattice PCS extractability broken **[F]** | Adds a structured hardness assumption; historical lattice-PCS knowledge-assumption breaks (classical & quantum) **[F]** |
| **D. Sumcheck-AIR + FRI MLPCS (BaseFold/WHIR/DeepFold)** | Yes (hash-based) | Same prime field; FRI multilinear | Linear-ish prover, log verifier; smaller than univariate STARK in some regimes | **Medium** — arithmetization swap, keep field+hash | **Medium-High** — BaseFold/WHIR maturing fast | FRI proximity again; sumcheck Fiat-Shamir round-binding (see Gemini lesson) |
| **(anti-option) KZG MLPCS (Samaritan/Gemini/Zeromorph)** | **No** | Pairing groups, trusted setup | Smallest proofs (368 B–6 KB) | n/a — wrong trust model | High (but not for dregg) | Gemini "optimization" broken **[F]**; needs SRS/trusted setup |

---

## Recommendation (stay vs move + threshold; deciding factor)

**STAY on Option A (BabyBear + degree-4 extension + FRI / Plonky3).** Keep the existing Binius backend as a feature-gated `Experimental` research lane; do **not** promote it to the spine.

**Deciding factor:** *alignment with the existing Plonky3 + BabyBear + FRI stack.* dregg already has the property each "move" is chasing — **transparent, hash-based, plausibly post-quantum** — without a rewrite and without a new hardness assumption. Moving trades a known, integrated, recursion-complete stack for a younger one (Binius) or a structured-assumption one (lattice), for benefits dregg does not currently need.

**Thresholds that would justify moving (revisit only if one fires):**

- **Move to Binius (Option B) if** profiling shows that **> ~50% of prover time is bit-level work** (Poseidon2/BLAKE3 hashing, XOR-heavy circuits, big lookups/range checks) *and* the embedding penalty into the 31-bit prime is the measured culprit, *and* the Binius toolchain reaches a stable (non-nightly), independently-audited release. Below that, the embedding cost does not justify a full-AIR rewrite + nightly dependency.
- **Move to lattice (Option C) if** an external requirement forces **structured-assumption PQ** *or* **on-chain proof size must drop to ~50 KB** (e.g., an L1 calldata budget) *and* verifier cost is acceptable off the critical path. dregg's current bridge/recursion model does not impose this.
- **Adopt Option D (sumcheck-AIR + FRI MLPCS) if** dregg's arithmetization shifts to HyperPlonk/Spartan-style multilinear constraints — then take a **FRI-based** multilinear PCS (BaseFold/WHIR/DeepFold) to preserve field + hash alignment, optionally with Fold-DCS to shrink sumcheck rounds. **Never** take a KZG-based MLPCS (Samaritan/Gemini/Zeromorph): trusted setup + pairings + non-PQ contradict dregg's design goals.

---

## Soundness-testing checklist (concrete adversarial tests, citing Orion/Gemini lessons)

**[C]** Current `circuit/src/soundness_tests.rs` covers *AIR-witness rejection* (bit-flip output, forged Merkle parent, wrong position/key/nullifier/preimage). That is necessary but tests the **constraint system**, not the **PCS/Fiat-Shamir** layer where Orion and Gemini broke. Add the following.

PCS / proximity (Orion lesson — **[F]** soundness dies if the proximity/consistency check is elided or the code's minimum distance degrades):
1. **Proximity-gap forgery:** commit a matrix where one row is **far from any codeword**; confirm the random-linear-combination column-consistency check rejects with overwhelming probability. Assert the verifier actually *runs* the `Σ γ_i D_ij` column check (Orion's bug was the outer proof failing to perform it).
2. **Distance-preserving randomization:** if/when ZK masking is added to a code-based path, verify the masking does **not** reduce minimum relative distance (the exact Orion/Scorpius failure). Test with a masked codeword crafted to sit just inside the (broken) distance bound.
3. **Query-count / blowup downgrade:** a prover/proof that declares fewer FRI queries or a smaller blowup than policy must be **rejected**. **[A][C]** Also reconcile the two FRI paths: `plonky3_prover.rs` uses 50 queries while `stark.rs` documents 80 — pin one policy and test that under-parameterized proofs fail. Soundness bits = `num_queries * log2(blowup)`; assert the configured value meets the target (e.g. ≥100).
4. **Grinding/PoW bypass:** submit a proof with insufficient proof-of-work bits (`query_proof_of_work_bits`); must reject.

Fiat-Shamir / recursion (Gemini lesson — **[F]** the broken optimization **reused the challenge across rounds** (ρ^(2^j)) and dropped the cross-round consistency check, letting a prover forge any evaluation):
5. **Challenge-reuse attack:** construct a transcript that reuses or mis-derives a per-round challenge; verifier must reject. Explicitly test the recursion/fold steps (`fold_air.rs`, `plonky3_recursion*.rs`, and the Binius `prove_fold_step`).
6. **Cross-round consistency:** for any folding/recursive opening, forge `f^(j+1)` inconsistent with `f^(j)(ρ)`, `f^(j)(−ρ)` (the exact Gemini relation); confirm rejection. This is the test whose *absence* is the Gemini-565 vulnerability.
7. **Transcript completeness:** mutate any value that should be absorbed into Fiat-Shamir (public inputs, commitments, prior-round messages) and confirm the derived challenge changes and verification fails — i.e. nothing is forgeable by leaving a value out of the transcript.

Field / embedding (Binius/tiny-field lesson — **[F]** naive embedding "fails to guarantee tininess of the prover's input," a security requirement):
8. **Non-canonical field element:** **[C]** dregg already normalizes `BabyBear` in `Eq`/`Hash`; add a test that a deserialized `v + p` is treated as `v` everywhere a commitment/nullifier/signature is checked (no malleability fork).
9. **Tininess enforcement (only if Binius path is ever promoted):** prove that a committed "1-bit" column actually contains bit-values; a witness with an out-of-range value in a tiny-field column must be rejected (embedding-overhead soundness gap from the Binius paper).
10. **Extension-field challenge sampling:** confirm challenges are drawn from the full `BinomialExtensionField<BabyBear,4>` (~2^124), not accidentally from the 31-bit base field (which would collapse soundness). Test a proof whose challenges are base-field-only and assert it does not gain acceptance probability.

Process:
11. **No-optimization-without-proof rule:** any PCS micro-optimization (challenge schedules, batched openings, dropped checks) must come with a soundness argument *before* merge — the Gemini-565 break was an un-proven blog optimization that got widely implemented.

---

## Open questions to confirm in code

1. **[C] FRI query mismatch:** `plonky3_prover.rs` sets `num_queries=50` (log_blowup=3) while `stark.rs` documents `NUM_QUERIES=80, MIN_BLOWUP=4`. Which path is on the production verification route, and what is the *actual* claimed soundness-bit target? Confirm both meet the same bar (and that the proximity/conjectured-vs-provable-soundness regime is documented).
2. **[A] Conjectured vs provable FRI soundness:** is the query count chosen for *provable* RS proximity soundness or the (tighter) *conjectured* regime? This corpus has `proximity-gaps-reed-solomon-2025-2055.pdf` and `stir/whir` — confirm which bound dregg assumes.
3. **[C] Binius backend status:** is `backends/binius.rs` reachable from any default/production code path, or strictly behind `--features binius` (nightly)? Confirm the **stub fallback cannot be mistaken for a real proof** at the `proof_tier`/verification boundary (it is marked `Experimental`, but verify the tier is not a no-op gate — the docs say "tier is informational only and NOT used for verification acceptance," so the *cryptographic* check must independently reject stubs).
4. **[A] Recursion/IVC Fiat-Shamir audit:** do the in-circuit verifier AIRs (`plonky3_verifier_air.rs`, `poseidon_stark_verifier_circuit.rs`, `fold_air.rs`) absorb *all* prior-round commitments and public inputs into the challenge derivation (Gemini lesson #5–7)? This is the highest-value place to add tests 5–7.
5. **[C] `babybear8` scope:** confirm `babybear8.rs` / `schnorr_curve.rs` is used *only* for ECC and never as a PCS/commitment field — and that its ~124-bit Pollard-rho security target matches the rest of the system's security level.
