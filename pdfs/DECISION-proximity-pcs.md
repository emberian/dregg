# DECISION — Proximity testing & PCS for the STARK backend

Legend: **[C]** grounded in dregg's `circuit/` code · **[A]** assumption / external claim from the papers · **[F]** future / proposed work.

## dregg's constraints ([C] from `circuit/` vs [A])

- **[C] Field = BabyBear**, `p = 2^31 − 2^27 + 1`. Defined in `circuit/src/field.rs:3`; native type `BabyBear(u32)`. This is a two-adic FFT-friendly prime (2-adicity 27), *not* a Mersenne prime.
- **[C] Extension = BinomialExtensionField<BabyBear, 4>** (degree-4, ~124-bit ext) — `circuit/src/plonky3_prover.rs:61`, and used as the challenge field in `quantified_absence.rs`.
- **[C] PCS = `TwoAdicFriPcs`** (FRI over Reed–Solomon), Poseidon2-width-16 Merkle MMCS, `Radix2DitParallel` DFT. `circuit/src/plonky3_prover.rs:83`.
- **[C] FRI params** (`plonky3_prover.rs:103`): `log_blowup = 3` (rate ρ = 1/8), `num_queries = 50`, `query_proof_of_work_bits = 16`, `max_log_arity = 3`, `log_final_poly_len = 0`. Blowup is 3 (not the more common 1 or 2) because the **Poseidon2 S-box is degree 7** → `log_blowup ≥ log2_ceil(6) = 3`.
- **[C] The AIR is univariate STARK** — everything goes through `p3-uni-stark` (`Proof<StarkConfig>`, `RowMajorMatrix`, row-pair `eval_constraints`). The Effect-VM AIR (`circuit/src/effect_vm/air.rs`, `effect_vm_p3_air.rs:293`) is a wide (≈ `EFFECT_VM_WIDTH`-column) selector-gated execution trace evaluated as a univariate AIR. **No sumcheck / multilinear / GKR path exists in the STARK backend** (`rg` finds zero WHIR/STIR/BaseFold/circle references in `circuit/src`).
- **[C] Recursion already works through FRI**: `plonky3_recursion_impl.rs` wraps `p3-recursion`'s in-circuit FRI verifier; `log_blowup=3` is reused for the recursion config. The recursion AIR re-proves "the inner FRI proof verifies." **The dominant cost of that recursion AIR is the number of FRI query openings × Poseidon2 hashes per Merkle path** — i.e. verifier *hash complexity* is the thing we re-prove. This is the lever.
- **[C] A multilinear/sumcheck path already exists, but only in a *separate* backend**: the Binius backend (`circuit/src/backends/binius.rs`) runs sumcheck-over-multilinear-in-binary-tower + binary-RS FRI + Groestl Merkle. It is *not* the BabyBear STARK and is not recursion-integrated.
- **[C] Dependencies pinned**: `p3-fri`, `p3-uni-stark`, `p3-recursion` are wired; **`p3-circle` is NOT a dependency**, and no WHIR/STIR Rust crate is pinned (`circuit/Cargo.toml`). Migration is therefore a real dependency + glue effort, not a flag flip.
- **[A] Deciding factor (from the prompt and confirmed by the papers): verifier succinctness *under recursion*.** Every FRI query that the inner verifier makes becomes constraints in the outer recursion AIR. Fewer queries / fewer verifier hashes ⇒ a smaller recursion circuit ⇒ cheaper, deeper recursion. Argument size matters less than *verifier hash count* here.

## The options (one paragraph each)

- **FRI (status quo).** [C] The current `TwoAdicFriPcs`. Soundness rests on the proximity-gaps line (deep-FRI 2019 + proximity-gaps 2025). [A] Query complexity is `O(λ·log d)` — the *most* queries of any option, ≈ 5.6–8.5 khashes of verifier work at d = 2^24–2^28 (WHIR Table, §6.3.2). Maximally mature: it is what Plonky3, recursion, and every dregg AIR run on today. It is univariate-RS native, so it matches the current AIR perfectly.

- **STIR** (`stir-2024-390`, "Shift To Improve Rate"). [A] An IOPP for *univariate* Reed–Solomon that recursively improves the code rate, cutting query complexity to `O(log d + λ·loglog d)`. Concretely ≈ 2.7–3.4 khashes (≈ **2.1–2.5× fewer verifier hashes than FRI**) and 1.25–2.46× smaller arguments, with prover/verifier times similar to FRI. It is a near-drop-in for FRI because it tests the *same* univariate RS codes — so it aligns with dregg's current univariate AIR with no AIR rewrite.

- **WHIR** (`whir-2024-1586`, by the STIR authors). [A] An IOPP for *constrained* Reed–Solomon codes that expresses **both univariate AND multilinear** queries, and is an explicit drop-in replacement for "FRI, STIR, BaseFold, and others." Same verifier hash count as STIR (≈ 2.7–3.4 khashes, ~2.1–2.5× under FRI) but a **dramatically faster verifier: ≈ 1.0–1.2 ms vs FRI's 3.9–5.5 ms (3.6–4.6×)**, the lowest of any hash-based scheme. Prover is ~1.2–1.6× slower than FRI. Crucially, WHIR sits on the univariate→multilinear boundary, so it serves *both* today's univariate AIR *and* a future sumcheck AIR with the same PCS.

- **BaseFold** (`basefold-2023-1705`). [A] Field-agnostic **multilinear** PCS from foldable codes; `O(log² n)` verifier, `O(n log n)` prover. Pairs with multilinear PIOPs (HyperPlonk-style sumcheck). Its win is field-agnosticism (works over any large field, incl. non-FFT fields), but for dregg's already-FFT-friendly BabyBear that benefit is moot, and its query count is *higher* than STIR/WHIR.

- **DeepFold** (`deepfold-2024-1595`). [A] BaseFold improved by pushing to the *list-decoding* radius (DEEP technique), giving ~3× smaller proofs than BaseFold and fewer query repetitions, same prover profile. Still a multilinear-only PCS; strictly a better BaseFold, but WHIR dominates it on verifier time and breadth (uni+multi).

- **ARC** (`arc-reed-solomon-codes-2024-1731`, "Accumulation for RS Codes"). [A] A *hash-based, PQ, transparent accumulation/folding* scheme for RS-proximity claims with **unbounded** accumulation depth (removes the bounded-depth limit of prior RO-only folding), accumulating up to list-decoding radius. This is not a PCS replacement for FRI — it is the *recursion/folding substrate* (PCD without homomorphic/elliptic-curve VCs). It belongs to the sibling **DECISION-recursion-strategy.md** decision, but it is RS-native so it composes with whatever RS-proximity PCS we pick.

- **Circle STARKs** (`circle-starks-2024-278`). [A] STARKs over the circle curve x²+y²=1, enabling FFT/AIR over **Mersenne-31** (`p = 2^31−1`). The paper's own benchmark: Mersenne31 circle-STARK is **1.4× faster than a BabyBear STARK**. But it is a *field+domain* change, not a proximity-test change — and dregg is on BabyBear, not Mersenne31. Adopting it means migrating the field of every AIR, every Poseidon2 instance, and the recursion config.

- **FRIDA** (`frida-das-from-fri-2024-248`). [A] FRI-as-data-availability-sampling (erasure-code commitment from any consistent IOPP). Not a recursion/verifier-cost play at all — it is relevant only if dregg wants DAS / light-client data-availability on top of its FRI commitments. Out of scope for the PCS-under-recursion decision; noted for completeness.

## Comparison table

| Option | Field-fit (BabyBear) | Univariate / multilinear | Verifier cost under recursion | Query count / arg size | Maturity / prod impls | Migration cost from FRI |
|---|---|---|---|---|---|---|
| **FRI** (now) | [C] native (two-adic) | univariate RS | **highest** — `O(λ log d)`, ≈5.6–8.5 khashes [A] | 50 queries [C]; 306–430 KiB [A] | **highest** — Plonky3 + p3-recursion, all dregg AIRs [C] | **zero** (status quo) |
| **STIR** | native (two-adic RS) | univariate RS | low — `O(log d+λ loglog d)`, ≈2.7–3.4 khashes (~2.3× under FRI) [A] | ~2.1× fewer queries; 1.25–2.46× smaller [A] | medium — ref impl; no p3 crate pinned [C] | **low** — same code, same AIR; swap PCS |
| **WHIR** ⭐ | native (two-adic RS) | **both** uni + multilinear | **lowest** — ≈2.7–3.4 khashes *and* 1.0–1.2 ms verifier (3.6–4.6× under FRI) [A] | ~2.1× fewer queries; ≈ STIR arg size [A] | medium — ref impl (Rust); no p3 crate pinned [C] | **low–med** — swap PCS; AIR unchanged today, multilinear-ready |
| **BaseFold** | works (field-agnostic, no BabyBear bonus) | multilinear only | medium — `O(log²n)`, more queries than STIR/WHIR [A] | larger than STIR/WHIR [A] | medium — multiple impls | **high** — requires AIR→sumcheck rewrite |
| **DeepFold** | works (field-agnostic) | multilinear only | medium-low — ~3× smaller proofs than BaseFold [A] | fewer reps than BaseFold [A] | low — newer, fewer impls | **high** — AIR→sumcheck rewrite |
| **ARC** | native RS | proximity-claim accumulation (PCS-agnostic) | n/a (folding layer, not a PCS) — composes; unbounded depth [A] | small # MT openings rel. to rate [A] | low — research, no prod impl | **n/a here** — belongs to recursion memo |
| **Circle STARK** | **wrong field** — wants Mersenne31; 1.4× faster *if migrated* [A] | univariate (circle AIR) | same family as FRI (still FRI proximity) | same as FRI | medium — `p3-circle` exists upstream, **not pinned** [C] | **very high** — field migration of every AIR + Poseidon2 + recursion |
| **FRIDA** | native | FRI variant (DAS) | n/a (data-availability, not recursion) | — | low | out of scope |

## Recommendation

**Primary: migrate the proximity test from FRI to WHIR, keeping BabyBear + degree-4 extension and the univariate AIR exactly as-is. [F]**

Deciding factor — **verifier succinctness under recursion**: the recursion AIR re-proves the inner verifier's hash work, so the metric that matters is *verifier hash complexity* (and, for native verification, verifier wall-clock). WHIR and STIR both cut FRI's ≈5.6–8.5 khashes to ≈2.7–3.4 khashes (~2.1–2.5×), which directly shrinks the recursion circuit by roughly the same factor. WHIR is chosen over STIR because (a) it adds a **3.6–4.6× faster native verifier** at *no* extra hash cost, and (b) it is the **only option that spans univariate *and* multilinear** — so it is a single PCS that serves today's univariate Effect-VM AIR *and* survives a future move to a sumcheck/multilinear AIR without a second PCS migration. STIR would force a *second* migration the day the AIR goes multilinear; WHIR does not.

**Reject:** BaseFold/DeepFold (multilinear-only ⇒ require an AIR→sumcheck rewrite *now* for *zero* recursion benefit over WHIR — WHIR already covers multilinear); Circle STARKs (a field migration off BabyBear for a 1.4× *prover* speedup that does nothing for verifier-under-recursion — wrong lever, very high cost); FRIDA (DAS, orthogonal). **ARC is not rejected** — it is deferred to the recursion memo: if dregg adopts hash-based accumulation/PCD, ARC's unbounded-depth RS-proximity accumulation composes cleanly on top of a WHIR (or FRI) commitment, since both are RS-native.

**Migration path (FRI → WHIR), staged so the chain never loses a working prover:**
1. **[F] Stay on FRI; keep it as the verified baseline.** No ProofTier downgrade, no experimental flag (per project policy). FRI remains the production path until WHIR passes parity.
2. **[F] Add a WHIR PCS behind the existing `Pcs` trait** as an *additional* config (`DreggStarkConfigWhir`), reusing the same BabyBear, degree-4 extension, Poseidon2-16 Merkle MMCS, and the unchanged univariate AIR. Pin/vendor a WHIR Rust crate (none in `circuit/Cargo.toml` today — this is the main external dependency to land). Run both PCSes on the same trace and assert identical accept/reject on the soundness-test suite.
3. **[F] Port the in-circuit verifier** in `plonky3_recursion_impl.rs` from the FRI verifier to the WHIR verifier; measure the recursion-AIR column/row count drop (expect ≈2× from the khash reduction). This is where the real win lands.
4. **[F] Flip the default** once parity + recursion-cost win are demonstrated, retire the FRI config path (keep FRI verification for any already-issued proofs / interop).
5. **[F] Optional, later:** if/when the Effect-VM AIR is reformulated as a multilinear/sumcheck relation (a separate, large decision), WHIR already supports it — no further PCS change, which is the whole point of preferring WHIR over STIR.

## What to build

- **[F]** Vendor or pin a WHIR implementation over BabyBear + `BinomialExtensionField<BabyBear,4>` (the missing dependency).
- **[F]** A `Pcs`-trait WHIR config (`create_config_whir()`) mirroring `create_config()` in `plonky3_prover.rs`, reusing the exact Poseidon2-16 hash/compress/MMCS so the recursion verifier's hash gadget is unchanged.
- **[F]** A differential test harness: every AIR + every case in `circuit/src/soundness_tests.rs` proven under both FRI and WHIR, asserting identical verdicts (incl. the adversarial/should-reject cases).
- **[F]** A WHIR in-circuit verifier in `plonky3_recursion_impl.rs`, plus a benchmark that reports recursion-AIR width/height and prover time FRI-vs-WHIR — this is the acceptance gate for flipping the default.
- **[F]** A short interop/versioning note: WHIR proofs must carry a distinct proof-system tag so verifiers route to the right verifier (FRI proofs remain verifiable).

## Risks & soundness caveats

- **[A] Conjectured vs provable soundness.** WHIR/STIR's headline numbers (and dregg's current 50-query/16-PoW FRI) assume *conjectured* list-decoding soundness (decoding to capacity / list-decoding radius), not the provable Johnson-bound regime. The proximity-gaps 2025 paper sharpens exactly these bounds: it shows ε* = 0 at the Johnson radius needs only `O(n)` exceptional z's, but also a **lower bound** — going *beyond* Johnson with small loss requires Ω(n^1.99) exceptions, and any such improvement *requires* a corresponding RS list-decoding improvement. Net: if dregg relies on past-Johnson conjectures, document it explicitly and re-derive query counts when picking WHIR parameters; do not silently inherit FRI's `num_queries=50` — recompute for WHIR's soundness profile.
- **[A] WHIR/STIR are newer; fewer audited production deployments than FRI.** Mitigated by the staged migration (FRI stays as verified baseline; differential tests gate the swap).
- **[C] Degree-7 Poseidon2 forces `log_blowup ≥ 3`.** This rate (ρ=1/8) interacts with the proximity-test soundness/query trade-off. Whatever PCS we pick must be parameterized at the *actual* AIR constraint degree, not a textbook ρ=1/2. (A lower-degree hash/AIR would relax blowup and shrink proofs across *all* options — orthogonal but worth flagging.)
- **[A] Prover regression.** WHIR's prover is ~1.2–1.6× slower than FRI. For a recursion-dominated system this is an acceptable trade (recursion verifier cost dominates), but measure it; if prover time becomes the bottleneck, STIR (prover ≈ FRI) is the fallback that still gives the query-count win.
- **[C] Single-PCS coupling.** The recursion config currently *reuses* the prover's FRI config. The migration must keep prover-PCS and recursion-verifier-PCS in lockstep, or recursion breaks.

## Open questions to confirm in code

- **[C?]** Confirm `num_queries=50` + `query_proof_of_work_bits=16` + `log_blowup=3` corresponds to which security target (≈100-bit conjectured? provable?). The 124-bit extension suggests a 100-bit-class target, but the FRI param derivation isn't documented in `plonky3_prover.rs` — find/derive the soundness calculation before reusing query counts for WHIR.
- **[C?]** Is there a Mersenne31 / circle-STARK ambition anywhere else in the workspace (other crates), or is BabyBear final? (Affects whether circle-STARKs should even stay on the table.) `rg` found nothing in `circuit/src`.
- **[C?]** Does `p3-recursion`'s in-circuit verifier abstract over the PCS, or is it FRI-specialized? This determines whether step 3 (WHIR recursion verifier) is a config swap or a from-scratch gadget. Inspect the `RecursivePcs`/`FriRecursionConfig` traits referenced in `plonky3_recursion_impl.rs`.
- **[C?]** Is the Binius (multilinear/sumcheck, binary-tower) backend a candidate to *converge with* the STARK path, or strictly a parallel backend? If dregg ever unifies on multilinear, WHIR-over-BabyBear vs Binius-over-GF(2) becomes a real fork — out of scope here but flagged.
- **[F?]** Coordinate with **DECISION-recursion-strategy.md** (not yet written): if that memo lands on ARC-style hash accumulation/PCD, confirm ARC's RS-proximity accumulation is parameter-compatible with the chosen WHIR code/rate.
