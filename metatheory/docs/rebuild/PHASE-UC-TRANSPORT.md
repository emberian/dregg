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
> **GREEN BUILD (resolved 2026-05-31):** the version skew is fixed. The machine now has the final
> stable **Isabelle2025-2** (January 2026) matched with **AFP release 2025-2** (`~/isabelle/afp-2026-05-29`,
> `etc/version` → `VERSION=2025-2`, registered via `isabelle components -u`). `isabelle build CryptHOL`
> and `isabelle build Dregg2_UC` both reach **real exit 0** (`Finished CryptHOL`, `Finished Dregg2_UC`;
> the full dependency chain HOL-Analysis → HOL-Probability → Probabilistic_While → CryptHOL →
> Sigma_Commit_Crypto → Dregg2_UC compiles clean, with **no** manual AFP patches — the entire
> afp-devel/RC3 failure cascade evaporated once Isabelle and AFP versions matched). Bringing the
> build to exit 0 exposed **one real bug** in `Dregg2_FCom.thy`: the three realization-*bundle*
> theorems reused a single adversary `\<A>` for both the hiding conjunct and the binding conjunct,
> but `hid_adv` and `bind_adversary` are distinct types in `Commitment_Schemes` — fixed by
> quantifying a separate binding adversary `\<B>` (the standalone per-property theorems were always
> well-typed). The theory is sorry-/oops-free and references only the real proven AFP Pedersen
> lemmas. Detail in §3 "BUILD STATUS". The Pedersen *security itself* was never in question — it is
> long-proven in `Sigma_Commit_Crypto`.

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

The toolchain on this machine is now **version-matched**: **Isabelle2025-2** (the final stable
release, January 2026 — supersedes Isabelle2025-1, and is newer than the RC3 candidate previously
used) at `~/Applications/Isabelle2025-2.app`, with the matching **AFP release 2025-2** at
`~/isabelle/afp-2026-05-29` (`etc/version` → `VERSION=2025-2`). The AFP is registered as a
component (`isabelle components -u ~/isabelle/afp-2026-05-29/thys`), so `CryptHOL` /
`Sigma_Commit_Crypto` resolve; heaps cache in `~/.isabelle`. (The old `afp-devel-branch-default`
checkout — the source of the skew — is no longer used.)

```sh
ISA=~/Applications/Isabelle2025-2.app/bin/isabelle
AFP=~/isabelle/afp-2026-05-29/thys

# (one-time) build the CryptHOL heap (~14 min cold incl. HOL-Analysis; cached after):
$ISA build -d $AFP -b CryptHOL

# verify the transport theory (exit 0 ⇒ all theorems kernel-checked):
$ISA build -d $AFP -d ~/dev/breadstuffs/uc-crypthol Dregg2_UC
```

### BUILD STATUS — GREEN (resolved 2026-05-31)

Both sessions reach **real exit 0**:

- `Finished CryptHOL` (full chain HOL-Analysis → HOL-Probability → Probabilistic_While → CryptHOL,
  `EXIT=0`, zero `***` errors). Notably **no manual AFP patches were needed** — the entire
  afp-devel/RC3 failure cascade documented in earlier drafts of this section (`Adhoc_Overloading`
  relocation, `Fast_Dice_Roll` real-arithmetic, `applicative.ML` / `Term_Subst.map_types_same`,
  `Monomorphic_Monad` `fBall.rep_eq`, `Landau_Real_Products`) was purely an artifact of the
  afp-devel-vs-Isabelle-version mismatch and disappeared once Isabelle and the AFP versions were
  matched.
- `Finished Dregg2_UC` (`EXIT=0`). `Dregg2_FCom.thy` is sorry-/oops-free and references only the
  real proven AFP theorems (`pedersen.abstract_correct`, `abstract_perfect_hiding`, `pedersen_bind`,
  `pedersen_asymp.pedersen_bind_asym`, `cyclic_group_commute`, `group_comm_groupI`).

**One real bug fixed** to reach green (it had been masked because afp-devel never built far enough
to typecheck our theory): the three realization-*bundle* theorems
(`dregg2_pedersen_realizes_F_com`, `dregg2_F_com_realizes`, `dregg2_pedersen_realizes_F_com_asymp`)
reused a single adversary `𝒜` for both the hiding conjunct and the binding conjunct. But in
`Commitment_Schemes`, `hid_adv` (a state-passing pair) and `bind_adversary` (a single
opening-producing function) are **distinct types** — so `perfect_hiding_ind_cpa 𝒜` and
`bind_advantage 𝒜` cannot share one `𝒜` (Isabelle: *"Clash of types `_ × _` and `_ ⇒ _`"*). Fixed
by quantifying a separate binding adversary `ℬ` in each bundle. The standalone per-property
theorems (`dregg2_F_com_hiding`, `dregg2_F_com_binding`, `dregg2_binding_under_dlog`, …) were always
well-typed and unchanged.

The honest status of this pass is therefore: **definitions + stated security theorems faithfully
transported into a real UC framework (CryptHOL/Sigma_Commit_Crypto) and kernel-checked GREEN
(`Dregg2_UC` exit 0) on a version-matched Isabelle2025-2 + AFP 2025-2.** The cross-system transport
*fidelity* caveat (§5.3 — the human-checked Lean↔Isabelle correspondence) is unchanged; what is now
removed is the build-blocker.

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
