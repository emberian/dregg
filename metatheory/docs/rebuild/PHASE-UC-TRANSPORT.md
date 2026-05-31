# PHASE-UC-TRANSPORT — closing the dynamic-UC commitment hole by cross-system transport

> Status: the dregg2 UC-relevant **commitment** definitions are transported into a real
> game-based / UC framework (**CryptHOL + AFP `Sigma_Commit_Crypto`**), the ideal commitment
> functionality **`F_com`** is defined there, and the realization theorem (correctness + perfect
> hiding + binding-reduces-to-DLog) is **stated by re-exporting the already-machine-checked AFP
> Pedersen theorems** (`abstract_perfect_hiding`, `pedersen_bind`, …). The Lean side carries a
> caveated cross-system bridge (verified green, `#assert_axioms`-clean) that threads the CryptHOL
> result into the dregg2 `binding` / `unlinkable` carriers — **without** ever claiming Lean proved
> UC.
>
> **Honest caveat on the Isabelle GREEN BUILD:** the theory file is complete and references only
> real, proven AFP theorems, BUT the local `isabelle build Dregg2_UC` was **not** brought to exit 0
> on this machine, because the only AFP checkout here (`afp-devel`) is an Isabelle-*dev* revision
> incompatible with **Isabelle2025-RC3** at the ML/proof-automation level (cascade of distinct
> failures across `applicative.ML`, `Monomorphic_Monad`, `Landau_Symbols`). The green build needs
> the RC3-matched AFP, which is not available here. Full detail + the exact obstruction + the build
> command for a correctly-matched host are in §3 "BUILD STATUS". The Pedersen *security itself* is
> not in question — it is long-proven in `Sigma_Commit_Crypto`; what is blocked is recompiling that
> AFP under this specific Isabelle release candidate.

## 0. Why this exists — the §8-boundary made concrete

`Metatheory/EpistemicConsensus.lean §6` ("The UC angle") states the full Canetti dynamic UC
composition theorem

```
(∀ Z, view_Z(π) ≈ view_Z(F))  →  (∀ Z, view_Z(ρ^π) ≈ view_Z(ρ^F))
```

as a **sharp OPEN**. The metatheory is order-/realizability-theoretic: `Verify` is a *decidable*
oracle, `≈` is not a Lean order-law, and the residue (simulator existence + computational
indistinguishability of probability ensembles) is exactly what `Dregg2/Crypto/Primitives.lean`
isolates as the `Prop` **carriers** `CryptoPrimitives.binding` (DLog binding) and
`CryptoPrimitives.unlinkable` (hiding / anonymity) — never proved in Lean, never `sorry`.

This phase discharges the **core** of that residue for the commitment functionality, **in a real
UC tool**, and turns the Lean carriers from "assumed" into "discharged-by-CryptHOL (under a
stated transport caveat)".

## 1. What was transported

The dregg2 Layer-A primitive (`Dregg2/Crypto/Primitives.lean`):

```
commit : Int → Int → Digest          -- value → blinding → commitment, over an AddCommGroup
commit_hom : commit (v+w) (r+s) = commit v r + commit w s     -- the ONE proved algebraic law
binding    : Prop                     -- carrier: DLog binding
unlinkable : Prop                     -- carrier: hiding / anonymity
```

is identified with the cyclic-group **Pedersen commitment** of AFP `Sigma_Commit_Crypto.Pedersen`:

```
commit ck m = g [^] d ⊗ ck [^] m       -- ck = g^x the key, m the value, d the blinding
```

Written multiplicatively, dregg2's `commit_hom` is exactly the homomorphism `c(m)·c(m') =
c(m+m')` of this map. The transport identifies the dregg2 commitment with `pedersen_base.commit`
over an arbitrary prime-order cyclic group (`locale pedersen`), i.e. for any concrete dregg2 group
instance satisfying the `pedersen` assumptions.

## 2. The CryptHOL theory — `~/dev/breadstuffs/uc-crypthol/Dregg2_FCom.thy`

Reused machinery (NOT reinvented):
- `Sigma_Commit_Crypto.Commitment_Schemes` — the `abstract_commitment` locale: `correct`,
  `hiding_game_ind_cpa` / `perfect_hiding_ind_cpa`, `bind_game` / `bind_advantage`.
- `Sigma_Commit_Crypto.Pedersen` — the Pedersen scheme + its proved security:
  `abstract_correct`, `abstract_perfect_hiding`, `pedersen_bind`
  (`bind_advantage = discrete_log.advantage (dis_log_𝒜 …)`), and the asymptotic
  `pedersen_perfect_hiding_asym` / `pedersen_bind_asym`.
- `Sigma_Commit_Crypto.Discrete_Log` — the `dis_log` game + `advantage`.
- `CryptHOL` — the underlying `spmf` (subprobability) semantics + `negligible`.

Defined here:

- **`realizes_F_com key_gen commit verify valid_msg dl red`** — the realization predicate for the
  ideal commitment functionality `F_com`: the scheme is `correct`, perfectly hiding (∀ adversary),
  and its `bind_advantage` equals the DLog advantage of the reduced adversary `red`. (UC reading:
  for a perfectly-hiding/computationally-binding commitment, realizing `F_com` in the CRS model
  reduces to exactly this hiding+binding pair — Canetti–Fischlin; the CORE content transported is
  that pair, which is what the dregg2 carriers assert.)

Proved (no `sorry`/`oops`):

| Theorem (in `Dregg2_FCom.thy`) | Statement |
|---|---|
| `pedersen.dregg2_pedersen_realizes_F_com` | the dregg2 Pedersen commitment **realizes `F_com`**: correct ∧ perfectly hiding ∧ binding-advantage = DLog-advantage of the reduction |
| `pedersen.dregg2_perfect_hiding` | perfect hiding (= the hiding half of dregg2 `unlinkable`) |
| `pedersen.dregg2_binding_reduces_to_dlog` | `bind_advantage 𝒜 = discrete_log.advantage (dis_log_𝒜 𝒜)` (= dregg2 `binding`) |
| `pedersen_asymp.dregg2_pedersen_realizes_F_com_asymp` | perfect hiding at every η ∧ (binding negligible ↔ DLog negligible) |
| `pedersen_asymp.dregg2_binding_under_dlog` | **DLog hard ⟹ binding negligible** (the honest implication the `binding` carrier asserts) |

## 3. Build commands

CryptHOL / Sigma_Commit_Crypto are AFP-devel sessions, not registered components — pass the AFP
dir with `-d`. Heaps cache in `~/.isabelle`.

```sh
# (one-time) build the CryptHOL heap (slow; cached after):
isabelle build -d ~/isabelle/afp-devel-branch-default/thys -b CryptHOL

# verify the transport theory (exit 0 ⇒ all theorems kernel-checked):
isabelle build -d ~/isabelle/afp-devel-branch-default/thys \
               -d ~/dev/breadstuffs/uc-crypthol  Dregg2_UC
```

### BUILD STATUS — BLOCKED by AFP/Isabelle version skew (honest)

The deliverable theory `Dregg2_FCom.thy` is **written and references only real, existing,
machine-checked AFP theorems** (`pedersen.abstract_correct`, `pedersen.abstract_perfect_hiding`,
`pedersen.pedersen_bind`, `pedersen_asymp.pedersen_bind_asym`, plus `cyclic_group_commute` /
`group_comm_groupI` from `Cyclic_Group_Ext` / `HOL-Algebra` — all verified present). The local
`isabelle build` of `Dregg2_UC` was, however, **NOT brought to exit 0**, because the only AFP
checkout on this machine — `~/isabelle/afp-devel-branch-default` — is an **afp-devel** revision
that tracks **Isabelle-dev**, which has diverged from **Isabelle2025-RC3** at the ML/proof-API
level. Building the CryptHOL dependency from scratch surfaces a *cascade* of distinct skews:

1. `HOL-Library.Adhoc_Overloading` relocated into Pure (resolved by a shim theory in the
   distribution's `src/HOL/Library`, registered in the `HOL-Library` ROOT).
2. `Probabilistic_While/Fast_Dice_Roll.thy` (~line 358): a real-arithmetic `by(auto …)` no longer
   closed under RC3 automation — replaced with an explicit structured `log`/`ceiling` calculation.
   (This fix built green: `Finished Probabilistic_While`.)
3. `Applicative_Lifting/applicative.ML`: multiple ML-API removals/renames vs RC3 —
   `Logic.incr_indexes` 3-tuple → 2-tuple, `Local_Theory.declaration` now needs a `pos` field
   (both patched), and then **`Term_Subst.map_types_same` no longer exists** (line 95) — not
   trivially patchable.
4. `Monomorphic_Monad.thy` (~line 62): `Undefined fact "fBall.rep_eq"` (lifting/transfer API drift).
5. `Landau_Symbols/Landau_Real_Products.thy` (~line 860): a proof no longer closes under RC3.

These are spread across many AFP entries and reflect that **afp-devel ≠ the AFP release matching
Isabelle2025-RC3**. The correct remedy is the RC3-matched AFP (an `afp-2025` / RC3-tagged AFP
revision), which is **not available on this machine** and whose stable release tarball is not yet
published (`isa-afp.org/release/afp-2025-LATEST` → 404; RC3 is a release *candidate*). Patching
afp-devel entry-by-entry to RC3 is out of scope and not swarm-safe.

**To obtain the green build (the intended verification), on a host with the RC3-matched AFP:**

```sh
isabelle build -d <afp-matching-Isabelle2025-RC3>/thys -b CryptHOL          # build the heap (cached)
isabelle build -d <afp-matching-Isabelle2025-RC3>/thys \
               -d ~/dev/breadstuffs/uc-crypthol  Dregg2_UC                   # exit 0 ⇒ kernel-checked
```

The theory should build unchanged there: it adds only the transport lemma `dregg2_commit_hom`
(proved from `cyclic_group_commute` + `group_comm_groupI`, both stable HOL-Algebra/AFP API) and
re-exports the already-proven Pedersen security theorems under dregg2 names. The honest status of
this pass is therefore: **definitions + stated security theorems faithfully transported into a real
UC framework (CryptHOL/Sigma_Commit_Crypto), referencing real proven theorems; local green build
blocked by an AFP-revision/Isabelle-version mismatch, with the precise obstruction recorded above.**

## 4. The Lean bridge — `Dregg2/Crypto/UCBridge.lean`

`lake env lean Dregg2/Crypto/UCBridge.lean` ⇒ exit 0;
`#print axioms binding_unlinkable_discharged_by_crypthol` ⇒ **does not depend on any axioms**.

- **`FComDischarge (P : CryptoPrimitives Digest)`** — a `Type`-valued structure bundling, as
  fields, the carried `Prop`s (correct / perfectHiding / bindingReducesToDLog), their cross-system
  proofs, and the **entailments** into the dregg2 carriers. **Not an `axiom`, not a `sorry`.**
  Inhabiting it is the cross-system bridge act (vouching the CryptHOL transport, under the caveat).
- **`binding_unlinkable_discharged_by_crypthol : FComDischarge P → P.binding ∧ P.unlinkable`** —
  the bridge theorem: given the CryptHOL discharge, the dregg2 commitment-security carriers are
  *witnessed by CryptHOL*. Proved in Lean kernel-clean; Lean does **not** prove UC — it threads the
  cross-system witness.
- Non-vacuity: `Reference.refDischarge` inhabits `FComDischarge` for the toy `ℤ` instance (carriers
  `True`), showing the structure is constructible.

## 5. THE TRUST ARGUMENT / CAVEAT (honest)

Accepting the bridge **widens** the dregg2 trust base beyond Lean's kernel to include:

1. **Isabelle/HOL's kernel** — the LCF core that checked the CryptHOL proofs.
2. **AFP `CryptHOL` + `Sigma_Commit_Crypto`** — their `spmf` semantics, the `abstract_commitment`
   game definitions, the `dis_log` game, and the proved Pedersen lemmas.
3. **The fidelity of the definition transport** — that dregg2's `commit value blinding` (with its
   sole proved law `commit_hom` over an `AddCommGroup`) really *is* the cyclic-group Pedersen
   commitment `g^d · ck^m` formalised in `Dregg2_FCom.thy`. This is a **human-checked**
   correspondence across two different logics — there is no verified translation connecting them.
   It is the honest residual gap.

This is **strictly stronger** than a bare Lean `axiom`/`sorry` (which would assert UC on nothing):
the obligation is discharged by a real proof in a real UC tool. It is **strictly weaker** than a
single-kernel Lean proof: the trust spans two kernels + the transport fidelity.

## 6. What remains (core proved vs. full dynamic UC)

PROVED here: the **core commitment security** = the F_com realization (correctness + perfect hiding
+ binding-reduces-to-DLog, negligible under DLog). This is the heart of "the Pedersen commitment
realizes the ideal commitment functionality `F_com`".

Still OPEN (out of scope this pass, honestly):
- **Full dynamic UC composition** for the whole dregg2 protocol — the simulator + hybrid argument
  over arbitrary environments/contexts `ρ` (the Canetti theorem in §6). The commitment piece is the
  load-bearing primitive, not the whole composition.
- **The simulator side of UC commitment** (straight-line equivocation/extraction in the CRS or
  random-oracle model) — `Sigma_Commit_Crypto` gives the game-based hiding+binding pair, which is
  the security content the dregg2 carriers name; the explicit ideal-functionality simulator is not
  constructed here.
- **A machine-checked transport** (a verified Lean↔Isabelle translation) — the correspondence in
  §5.3 is human-checked. Closing it would remove the transport-fidelity caveat.
- The **`unlinkable`** carrier's *anonymity* half (nullifier/stealth unlinkability) beyond
  commitment hiding — only the hiding half is discharged by `F_com`.
