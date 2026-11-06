# Pickles reality-gate extractor — a REAL Mina block, verified by Mina's own verifier

This produces `metatheory/mina_real_block_proof.json`, which
`metatheory/Dregg2/Circuit/Emit/MinaRealBlockGate.lean` consumes. Unlike everything that came
before it in this campaign, the object here was not made by us:

| gate | object | provenance |
|---|---|---|
| `KimchiRealProofGate` | one Kimchi proof, `k = 16`, Vesta-committed | **we** proved `create_circuit(0, 5)` |
| `PicklesRecursion` P0–P2 | Step/Wrap decision runs | **synthetic** witnesses at a `2^5` domain |
| **`MinaRealBlockGate`** | **a Mina devnet block's Wrap proof**, `k = 15`, Pallas-committed, `prev_challenges = 2` | **Mina produced it**; a public devnet node served it |

## The block

* network **devnet**, chain id `29936104443aaf264a7f0192ac64b1c7173198c1ed404c1bcff5e562e05eb7f6`
* genesis `3NL93SipJfAMNDBRfQ8Uo8LPovC74mnJZfZYB5SK7mTtkL72dsPx`
* state hash `3NLmVB6Fs3dm4kXNkgwheHXzJXNpCCwEDe76RpTVeBTNujm12zNk`, blockchain length **539508**
* fetched 2026-07-28 from `https://api.minascan.io/node/devnet/v1/graphql`, query
  `bestChain(maxLength: 1) { stateHash protocolStateProof { base64 } … }` — **read-only, no keys,
  no transactions.** The response is pinned verbatim in `mina_devnet_block.json`; the proof field
  is the base64url of the binprot `Mina_base.Proof.Stable.V2` (11138 bytes).

## The ground truth — asserted, in this order, before a single number is emitted

1. `ledger::proofs::verifiers::BlockVerifier::make()` — openmina's own embedded **devnet
   blockchain verifier index**, loaded unmodified: `public = 40`, `prev_challenges = 2`,
   `domain = 2^14`, `max_poly_size = 2^15`, `zk_rows = 3`.
2. `ledger::proofs::accumulator_check::accumulator_check(&srs, &[proof]) = true` — openmina's own
   `sg` accumulator discharge on Vesta (`batch_dlog_accumulator_check`).
3. `kimchi::verifier::verify::<Pallas, …> = Ok(())` — **o1-labs' own Kimchi verifier**, on the
   Wrap proof re-marshalled from the wire types, against the 40-element public input assembled by
   openmina's own `PreparedStatement::to_public_input`.

2 and 3 are the body of openmina's `verification::verify_block`
(`= accumulator_check && verify_impl`; `verify_impl = verify_with` — the call in 3 — plus
`run_checks`, a private feature-flag/domain check).

**Why not literally call `verify_block`?** It takes a whole `MinaBlockHeaderStableV2` so it can
compute the protocol-state hash, and public Mina GraphQL does not serve blocks in binprot. We take
the block's own `stateHash` and decode it to `Fp` instead. That substitution is **self-checking**:
the protocol-state hash is the `app_state` folded into `messages_for_next_step_proof`'s digest,
which is part of the Wrap public input, which is absorbed by the Fq-sponge — one wrong bit and
step 3 rejects. It does not.

Then, still in Rust and still as `assert!` rather than prints, the extractor checks that the
emitted numbers reproduce `proof.oracles(...)`:

```
[cross-check] C8 fold over 47 es-entries reproduces oracles().combined_inner_product : true
[cross-check] C5 body over the emitted inputs reproduces oracles().ft_eval0 : true
[cross-check] Lean zkPolyR == kimchi permutation_vanishing_polynomial : true
[cross-check] omega^(n-3) == index.w() : true
[cross-check] K4c bEval reproduces RecursionChallenge::evals[0] : zeta=true zeta_omega=true
[cross-check] K4c bEval reproduces RecursionChallenge::evals[1] : zeta=true zeta_omega=true
```

## Build and run

The crate is deliberately **outside** the breadstuffs workspace (its own `[workspace]`), so that
arkworks 0.5 / proof-systems 0.3.0 / the forked `num-bigint` never enter the breadstuffs lockfile.
It expects `mina-rust` as a **sibling checkout** of this repo (`../../../../mina-rust`), openmina
rev **`82480cd468`** (v0.19.0).

```
cd metatheory/fixtures/pickles-extractors
cargo run --release -- devnet > ../../mina_real_block_proof.json
```

### The second binary — the GROUP side

`src/main.rs` dumps the **scalar** side. `src/bin/wrap_group_export.rs` dumps what a **group**
check needs: the linearization MSM's `(commitment, scalar)` pairs, the chunked `t_comm`, `ft_comm`,
and the 47 commitments `combine_commitments` feeds to the terminal MSM.

```
cargo run --release --bin wrap_group_export > ../../mina_real_block_wrap_group.json
```

`kimchi::verifier::to_batch` is **private**, so `f_comm` / `ft_comm` are rebuilt here from
`verifier.rs:897-963` using o1-labs' own `perm_scalars`, `PolishToken::evaluate`,
`Context::get_column`, `PolyComm::multi_scalar_mul`, `chunk_commitment` and `scale`. A
transcription is not a ground truth, so the reconstruction is then **pinned**: it is handed, inside
the full 47-entry `evaluations` list, to o1-labs' own `SRS::verify` — the real verifier's final IPA
opening check — which returns `true`; and re-run with `ft_comm` displaced by `+G`, which returns
`false`. Nothing is emitted unless both hold, so the gold cannot be a restatement of our own
arithmetic and the pin cannot be vacuous.

It also prints two measurements the plan in `docs/MINA-REAL-BLOCK-GATE.md` §6.1 rests on:
`linearization.index_terms = 0` (hence `f_comm` is a **one-term** MSM), and that the terminal
`msm == 0` runs over **82 non-SRS points + `|srs.g| = 32768`**.

#### Rungs 5e and 5f (2026-07-28) — four more ground truths, in the same "assert before emit" shape

`wrap_group_export` also produces what `MinaWrapPublicCommGate` (5e) and `MinaWrapOpeningGate`
(5f) consume, and asserts each object before emitting it:

* **GT5 — `public_comm`.** The 40 SRS Lagrange points, the block's 40-element public input and
  `srs.h` are dumped, and the reconstruction is an **explicit sequential fold** rather than
  `PolyComm::multi_scalar_mul`, so it is a different computation from the one it is checked
  against; it must equal o1-labs' `commit_public`. Then `public_comm` is displaced by `+G` inside
  the 47-entry evaluations list and **o1-labs' own `SRS::verify` must reject**.
* **GT6/GT7 — the opening relation.** `SRS::verify` folds two statements into one randomised MSM
  and exposes neither, so this binary re-derives the whole IPA transcript from `o.fq_sponge`
  (`absorb_fr(shift_scalar(cip))` → `challenge_fq` → the group map → 15 rounds → `absorb_g(delta)`
  → `c`) and asserts the deterministic (`rand_base = 1`) relation
  `c·Q + delta − z1·sg − z1·b0·U − z2·H == O` **directly, with arkworks group arithmetic**. It
  must hold, and must FAIL at `z1 + 1` and at `combined + G`.
* **GT8 — the leg the Lean side defers.** `<b_poly_coefficients(chal), srs.g> == opening.sg`, the
  2^15-term SRS MSM of rung 5h. Cheap here. It used to be quoted at ~18 h and ~7 TB in-kernel and
  it is neither: **re-measured 2026-07-28 it is ~2.9 h and ~28 GB**, and 5h is now DISCHARGED in
  the Lean kernel (`MinaWrapSgCore` + `MinaWrapSgChunk0..3`, the chunks since retired 2026-11-06, see metatheory/docs/MINA-PICKLES-RESCUE.md). This assertion is the reference value
  those theorems are checked against, not a substitute for them.

* **GT9 — the generator FOLD recipe.** GT8's object is a 2^15-term MSM, which is not a shape a
  Lean kernel can run. GT9 pins the shape that is: 15 rounds of `g <- g_lo + c_j·g_hi`, **first
  challenge first**, written out as plain group arithmetic (`combine_one_endo` is deliberately
  *not* called), landing on the *same* point as `<s, srs.g>` and as `opening.sg`. It carries three
  **orientation controls**, each of which must be FALSE, because a fold identity that survives the
  wrong convention pins nothing about that convention: challenges consumed in **reversed** order,
  the **halves swapped** (`g_hi + c·g_lo`), and **`chal_inv`** used in place of `chal`. All three
  measure false. GT9 also emits, into an untracked `out/`, `MinaWrapSrsG.lean` — the 32768 SRS
  generators as 64 Lean `List Pt` blocks of 512, decimal `(x, y, 1)`, none at infinity — and
  `srs_fold_gold.json` (`srs_g_len`, `chals`, `chal_invs`, `sg`, `fold_gold`).
* **GT10 — the chunk partials.** The kernel cannot discharge a 2^15-term MSM in one `decide`
  (elaborator memory tracks the largest single one), so the discharge is split into **32
  contiguous chunks of 1024**, each its own theorem over a pinned arkworks-produced partial. What
  makes the split sound is that the 32 partials **re-sum to `sg`** — asserted — and that the
  re-sum **fails** when one partial (index 7) is displaced by `+G`. **None of the 32 partials is
  the point at infinity**, so the Lean side never has to represent `O`. Emitted as
  `out/MinaWrapSgParts.lean` (`PARTS`, `SG`) and as `chunk_partials_1024` / `chunk_size` /
  `n_chunks` in `out/srs_fold_gold.json`.

The 15 IPA *pre*challenges are replayed on a second sponge clone (via `OpeningProof::prechallenges`)
and each is asserted to endo-lift to the challenge the verify path computed, so the Lean sponge
derivation has 128-bit values to land on.

The extra `rand = "0.8"` dependency exists only because `SRS::verify`'s `RngCore + CryptoRng`
bounds come from rand 0.8 and nothing in the graph re-exports it.

`Cargo.lock` is committed and is **seeded from mina-rust's own lock on purpose**: resolving fresh
fails, because `multihash 0.18.1` requires `core2 = "^0.4.0"` and `core2 0.4.0` is **yanked**. A
lockfile that already pins it is the only way this resolves.

## A measured openmina defect: the mainnet verifier index does not load

`cargo run --release -- mainnet` reproduces it. At openmina `82480cd468`,
`crates/ledger/src/proofs/data/mainnet_{blockchain,transaction}_verifier_index.json` are in a
**stale serde format**:

* `PolyComm` is `{"unshifted": [...], "shifted": null}` — the pre-`chunks` kimchi shape;
* `zk_rows` is absent entirely;
* `domain` is a 172-byte arkworks-0.3 `Radix2EvaluationDomain` encoding written as a JSON **int
  array** (172 = `u64 + u32 + 5·32`; the pinned ark-poly 0.5 layout is a different length),

while the pinned proof-systems `0.3.0` `o1_utils::serialization::SerdeAs` deserialises a **hex
string** from any human-readable format. So
`serde_json::from_str::<VerifierIndex<Fq>>(mainnet json)` fails with
`invalid type: sequence, expected a hex encoded string` and `BlockVerifier::make()` **panics**.
This is not feature-dependent — `serde_json` is always human-readable — so openmina cannot verify a
mainnet block at this revision. The **devnet** files were regenerated (`chunks`, `zk_rows: 3`, hex)
and work, which is why the gate is a devnet block.

`mina_mainnet_block_header.json` is kept alongside: it is a real **mainnet** block header (height
**359606**, genesis `3NK4BpDSekaqsG6tx8Nse2zJchRft2JpnbvMiog55WCr5xJZaKeP` — confirmed against
`api.minascan.io/node/mainnet` `genesisBlock.stateHash`), lifted from openmina's tracked p2p RPC
fixture `crates/p2p/tests/files/rpc/best_tip_with_proof_response.json`. It deserialises fine; only
the VK blocks it. When openmina regenerates the mainnet index, `-- mainnet` becomes a second gate
that calls `verify_block` literally.

## The lesson this directory encodes

The Kimchi extractors lived only as untracked files inside `~/dev/proof-systems` — one `git clean`
from gone. This one is tracked, its input fixture is tracked, and the rev it builds against is
written down in `Cargo.toml` and in this file.

---

## Second binary: `samasika_vectors` — chain-selection differential vectors

`cargo run --release --bin samasika_vectors` (added 2026-07-29). Where `wrap_group_export` is about
one block's Wrap proof, this one is about **which chain wins**: it drives openmina's own
`mina_core::consensus` — `is_short_range_fork`, `relative_min_window_density`,
`short_range_fork_take`, `long_range_fork_take`, `consensus_take` — over real Mina protocol states,
and in the SAME run over the SAME state also computes the **OCaml daemon's** semantics
(`~/dev/mina/src/lib/consensus/proof_of_stake.ml:2951` `is_short_range`, `:1221`
`update_min_window_density`, `:2971` `select`). It emits both columns side by side so the
disagreement between the two implementations is a datum, not an argument.

Inputs, both tracked here:

* `../samasika-forks/*.json` — the five real fork pairs copied from `mina-rust/tests/files/forks/`,
  the fixtures openmina's own `short_range_fork` / `long_range_fork` tests assert against. The
  binary re-asserts those verdicts before emitting anything.
* `../samasika-forks/minascan-devnet-bestchain.json` — four consecutive real devnet blocks
  (539767–539770) fetched read-only from `api.minascan.io/node/devnet` on 2026-07-29, pinned to
  record what the PUBLIC GraphQL surface does and does not serve.

Outputs:

* `out/MinaSelectionVectors.lean` → copied to `metatheory/Dregg2/Bridge/MinaSelectionVectors.lean`,
  consumed by `Dregg2.Bridge.MinaChainSelectionDifferential`.
* `../samasika-forks/samasika_vectors.tsv` — the same rows, human-readable.

### Three things it measured that are worth knowing before touching this code

1. **The fork fixtures no longer deserialize with openmina's own types.** They carry
   `consensus_state.curr_global_slot`; the generated type calls it
   `curr_global_slot_since_hard_fork` (`crates/p2p-messages/src/v2/generated.rs:204`), and the
   enclosing `MinaStateProtocolStateValueStableV2` has since gained
   `constants.grace_period_slots`. openmina's `short_range_fork` / `long_range_fork` tests read
   these files with `serde_json::from_str::<MinaStateProtocolStateValueStableV2>` — so **the only
   tests openmina has over its chain-selection code do not currently run.** This binary renames the
   key and deserializes the consensus state alone.
2. **openmina's chain-selection density is not the daemon's**, on 30 of 57 vectors, and its final
   VERDICT differs on 8. Its `relative_min_window_density` transcribes the spec document's §5.4.12
   pseudocode (which contradicts the same document's §5.4.9): the shift count is measured in SLOTS
   rather than SUB-WINDOWS, the loop is `0..=shift_count` (one zero more than the pseudocode), and
   `GRACE_PERIOD_END` is hardcoded to `1440` where the daemon computes
   `grace_period_slots + slots_per_window = 2160 + 77 = 2237`. Note openmina's BLOCK-PRODUCTION
   path (`crates/ledger/src/proofs/block.rs:1116`) is a faithful port of the daemon's
   `update_min_window_density` — the two live in the same repo and disagree.
3. **`subWindowDensities` is not a field of the public GraphQL `ConsensusState`.** So the
   long-range fork rule cannot be evaluated from GraphQL at all; it needs the binprot protocol
   state. `blockHeight`, `epoch`, `slot`, `minWindowDensity`, `lastVrfOutput` and both
   `lockCheckpoint`s are served, so the short-range rule can.

---

## `walk.py` / `deferred.py` / `phaseb.py` / `verify_guards.py` — the `expand_deferred` extractor

These four are the provenance of every fixture in
`metatheory/Dregg2/Bridge/MinaWrapDeferredWeld.lean`, and they are the falsifier for it. No cargo,
no network: they read `mina_devnet_block.json` and run in about a second.

* **`walk.py`** — a field-for-field re-walk of `bridge/src/mina_pickles.rs` `decode_proof_at` in
  Python, KEEPING what that walk discards: `prev_evals` (43 columns × 2 points, the
  `public_input` pair, `ft_eval1`), `old_bulletproof_challenges`, the four plonk challenges,
  `sponge_digest_before_evaluations`, `branch_data`. It consumes the base64url proof with **zero
  trailing bytes**, which is the structural check that the layout is right, and it reports each
  evaluation array's chunk count (all 1 on this block, so `evals_of_split_evals` is the identity).
* **`deferred.py`** — the endo lift, the `Fp` roots of unity (arkworks `GENERATOR = 5`), the
  `Shifted_value.Type1` shift, and the three words that need no sponge:
  `zeta_to_srs_length`, `zeta_to_domain_size`, `perm`.
* **`phaseb.py`** — Poseidon over `Fp` (constants read **out of
  `Dregg2/Circuit/Emit/PastaPoseidon.lean`**, not copied, so there is no second `fp_kimchi` in the
  tree to drift), the deferred-values `Fr`-sponge, `xi`, `r`, `b`, and the 47-entry
  `combined_inner_product` fold.
* **`verify_guards.py`** — evaluates **every** `#guard` of `MinaWrapDeferredWeld` and prints
  PASS/FAIL per line. Run it before believing the Lean, and after changing either.

⚠ `phaseb.py` SOLVES for the step-side `ft_eval0` from public-input slot 0 rather than deriving it;
the weld says so at the pin. Deriving it needs the seven Tick coset shifts and
`Plonk_checks.Scalars.Tick.constant_term`.

---

## ⚑⚑ `../mina-blocks/` — the MULTI-BLOCK fixture set, and why it exists

Until 2026-08-02 every real-data conformance claim in this tree was pinned to **one** devnet block,
539508. That means anything accidentally fitted to that block's particulars could never show: a
constant that happens to equal something there, a branch never taken because that block's shape
does not take it, a width that collapses because two of its exponents coincide.

`metatheory/fixtures/mina-blocks/` holds additional blocks in the SAME schema, so the same code
runs on all of them:

```
bridge/tools/mina-block-fetch.py --network devnet --best 40 --out <dir>     # pick from these
bridge/tools/mina-block-fetch.py --network devnet --genesis  --out metatheory/fixtures/mina-blocks
bridge/tools/mina-block-fetch.py --network mainnet --best 1   --out metatheory/fixtures/mina-blocks

./target/release/pickles-reality-gate-export devnet   <fixture>            # the FULL gate
./target/release/pickles-reality-gate-export deferred <fixture> <network>  # VK-FREE, mainnet works
./target/release/wrap_group_export <fixture>                               # the GROUP side
python3 gen_multiblock_conformance.py --fixtures ../mina-blocks \
    --fixture mina_devnet_block.json --out-dir <extractor json dir> \
    --lean ../../Dregg2/Bridge/MinaMultiBlockConformance.lean
scripts/check-mina-multiblock-conformance.py [--self-test]                 # the standing gate
```

### ⚑ What a fixture set of BLOCK PROOFS can and cannot vary — measured, 40 consecutive blocks

**Every devnet blockchain-SNARK Wrap proof has the same shape.** `branch_data = (proofs_verified =
N2, domain_log2 = 16)`, two accumulator commitments, 15 IPA rounds, one chunk per evaluation column,
identical binprot length. That is a property of the RULE, not of the instance — so **no additional
block proof can exercise a different `proofs_verified` or a different domain**, and a fixture set of
block proofs cannot refute a constant fitted to those. Say that out loud rather than implying the
sweep covers it. The axes that DO vary, and on which the fixtures were chosen:

  * **transaction content** — from an empty block (0 user commands, 0 zkApp commands, 0 snark jobs)
    to the busiest in the window (4 / 3 / 35). Different Step proof wrapped, hence every field
    value, the accumulator challenges and the accumulator commitments.
  * **the hardfork genesis block** (devnet 296372) — its proof is 32 binprot bytes shorter, a
    degenerate object whose small challenge limbs take short varints. ⚠ `kimchi::verifier::verify`
    REJECTS it (`Err(OpenProof)`) while `accumulator_check` accepts: Mina's genesis carries a dummy
    blockchain proof. Step-side fixture only, and the extractor refuses it loudly rather than
    emitting.
  * **mainnet** — a different network, verification key and genesis. ⚠ Step side only: openmina at
    `82480cd468` still cannot load its own embedded mainnet verifier index (the stale-serde defect
    reproduced above), so `BlockVerifier::make()` panics. `expand_deferred` needs no verifier index,
    which is why the `deferred` mode exists and why the Step side runs anyway.

Historical heights are **not** re-fetchable: a public node serves only its transition frontier
(~290 blocks), and `block(height: N)` answers "Could not find block in transition frontier".
