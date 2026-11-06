# THE INJECTIVITY-FLOOR CLASS — one class, two halves, and a replacement ladder whose second rung is also refuted

**2026-07-27.** Two lanes hit the same root cause independently on the same day:
`docs/OPENING-SOUNDNESS-DECONFLATED.md` found the STARK apex resting on `Poseidon2SpongeCR`,
proven false at deployed parameters; and the dregg-in-dregg lane
(`docs/DREGG-IN-DREGG-BUILD.md` §3b) had a conservation leg refused by the tree's floor
ratchet for carrying `compressInjective` / `compressNInjective` / `cellLeafInjective`.

This file does **not** re-census. The census exists, it is a Lean metaprogram over elaborated
terms, and it has run: `docs/artifacts/floor-census-v2-2026-07-26/`. The campaign's state is
written up in `docs/PARKED-vacuity-campaign.md`, which is the file to read first for the
draining plan. **What is written here is what those files do not contain:**

1. the **replacement ladder** — four rungs, of which **two are themselves refuted**, one of
   them being the rung most readers (and the incoming work order) assume is the answer;
2. the **unification** of the hash-injectivity class with the felt-width class — they are one
   wound, and the reason is that *injectivity is width-blind*;
3. an assessment of `Dregg2/Bignum.lean`'s actual role, which is **not** the hash floors;
4. the ordered plan in those terms, and the first slice, landed.

---

## §1 — The true size, measured (not re-derived here)

Every number below has an instrument named beside it. Nothing in this section is a grep.

| quantity | value | instrument |
|---|---:|---|
| candidate floors discovered | 35 | `#floor_census`, TSV `FLOOR` records |
| of those, **REFUTED in-tree** | **27** | same |
| **UNREFUTED** | **8** | same — §1.2 below |
| carriers (declarations whose proof term binds a refuted floor) | **1925** | `#floor_census` SUMMARY |
| ↳ endpoint / threader / dead / other | 127 / 1266 / 100 / 432 | same |
| ↳ **`dead-thm-clean`** (the genuine day-one deletion wave) | **8** | same |
| gate baseline, grandfathered names | **2382** (2100 named + 282 inline) | `FloorRatchetBaseline{,Inline}.lean` |
| `Function.Injective`-spelled sites over an **uncountable** domain | ~600 | `Verify/InjSpelledFloors.lean` |

⚑ **The census and the gate disagree (1925 vs 2382) and should.** The census classifies against
the *proof term*; the gate asks *"is this name in the baseline"* and counts classes the census
reports separately. Neither is the other's correction. This has already confused two handoffs.

⚑ **A measured correction to the project record.** The memory note
`reference-grounding-efficient-adversaries` records a "1172-carrier surface … ~90 dead-binder
deletions … free, day one." The census measured the dead class at **100**, of which only **8**
are `dead-thm-clean`. The free wave is 8 declarations, not 90. Plan on the measurement.

### 1.1 Where the carriers concentrate — and the one rule that governs the work

**A declaration stays a carrier while ANY floor remains.** That single fact explains the
campaign's measured 0.5 endpoint→threader unlock ratio, and it makes sole-floor share, not
carrier count, the thing to sort on:

| floor | carriers | sole-floor | reading |
|---|---:|---:|---|
| `Poseidon2Binding.Poseidon2SpongeCR` | 732 | **707 (97%)** | a port here **ends** the carrier |
| `StateCommit.compressNInjective` | 753 | 233 | |
| `StateCommit.cellLeafInjective` | 470 | **13 (3%)** | the wave that freed nothing, explained |
| `StateCommit.compressInjective` | 366 | 12 | |
| `StateCommit.logHashInjective` | 291 | 137 | |
| `HermineHintMLWE.HashCR` | 57 | 57 | |
| **`HashFloorHonesty.CollisionResistant`** | **57** | **47** | ⚑ **see §2 — this is a *refuted floor*** |
| `DeployedCapTree.Compress8CR` | 31 | 31 | |

### 1.2 ⚑ The 8 UNREFUTED candidates — the frontier, and it is not all frontier

Read individually. Four are false and merely undetected; four are legitimately unrefuted.

| candidate | verdict | why |
|---|---|---|
| `Emit.AttestedFactsRootModel.Hash4Injective` | **FALSE, no tooth** | 4-to-1 compression stated as 4-way injectivity — the exact shape of the *deleted* `compress4Injective`. Docstring calls it "the honest collision-resistance floor". 2 carriers, 1 file. |
| `Emit.AutomataflRevealRefine.Hash4NoCollision` | **FALSE — now REFUTED, §5** | its own docstring said "globally it cannot hold … generic birthday ≈ `2^15.5`". Prose, not a theorem, so the gate was blind. |
| `Market.Fxc4ConsequenceBinding.Node8CROnFxc4` | **FALSE, no tooth** | infinite preimage record → 8 BabyBear lanes; same shape as the refuted `Compress8CR`. 1 consumer. |
| `Market.WideCarrierSameOpening.SpongeCROnCarrier` | **FALSE, no tooth** | its own docstring puts it "in the same register as `Poseidon2SpongeCR`" and defers grounding. |
| `Emit.ShieldedWideValueLinkDescriptor.WideBindingCR` | **legitimately unrefuted** | ⚑ **the model member — see §3.** |
| `Crypto.XmVrfRefinement.Injective3` | legitimately unrefuted | a length-framed *serialization* into a preimage type, not a digest. Genuinely injective. |
| `Crypto.HomomorphicDigest.SumInjective` | legitimately unrefuted | codomain is a lattice module, not a bounded field; and it is *constructively discharged* at `HomomorphicDigestPositioned:85`. |
| `Distributed.StrandIntegrity.StrandForkFree`, `Blocklace.Lace.Canonical`, `Crypto.Segmentation.SplitUniqueAt`, `ShieldedWideJoinPin.CrossSchemeSameOpening` | structural, not hash floors | not cardinality-shaped. |

Additional never-censused members with **no tooth and no regrounding module**:
~~`Emit.MinaStateQuery.PoseidonPairCR:174`, `.AccountLeafCR:236`, `.ZkappStateCR:281`~~ — ⚑ **all
three CLOSED 2026-07-27**: refuted in-file (`poseidonPair_shift_collides`, `leafHash_shift_collides`,
`zkappStateCR_refuted` — `absorbAt` reduces every input mod `pN`, so injectivity over `Nat` dies to
a one-line shift, and `ZkappStateCR` dies inside its own length-8 restriction), the three floor
`def`s **deleted**, and every consumer ported to a per-instance non-equivocation side condition
(`NoFoldColl`, `¬ LeafColl`, `¬ StateColl`) carrying all three legs — satisfiable with an exhibited
model, strength-preserving, and load-bearing. Refutation and port landed in the SAME commit, so no
consumer was ever left vacuous-and-known. The replacements are **not** `¬ Function.Injective`
spellings, deliberately: that would arm `#floor_ratchet` Source B on the shared signatures
`List Nat → Nat` and `Account → Nat`, where injections genuinely exist — gating them would be
noise, not a finding.
`Crypto.MlKemIndCca.QROMInjective:286` (superseded by `FoQromRegrounded`'s proved O2H bound,
3 residual live uses), `Circuit.ListCommit.listLeafInjective:36` (185 occ / 42 files —
`ListCommitRegrounded` re-grounded the `compressNInjective` half and **retained** this one).

**So: `docs/deos/VACUITY-SWEEP.md`'s "~20 carriers" understates the class.** 27 refuted + 4
false-but-undetected + ~8 never-censused + the ~600-site uncountable-domain class.

### 1.3 Three stale pointers found while assembling this

- `VacuitySweepTeeth.poseidon2WideCR_false_babyBear` **does not exist**. It is cited by name at
  `InjectiveFloorRegrounded.lean:48,677,827`, `Dregg2.lean:1148`, and in `VACUITY-SWEEP.md`.
  The live theorem is `VacuitySweepTeeth.widePerm_not_injective_babyBear:137`.
- `VACUITY-SWEEP.md` demands the `Compress8CR` field deletion as its priority; that field fell
  **2026-07-20**. The doc predates the repair it asks for.
- `Dregg2.lean:222`'s import comment still says `legS_swap_refused` is "conditional on the
  explicitly-named `Hash4NoCollision` floor". As of §5 it is not. **Not corrected here** —
  editing that root file was out of scope for this pass; it is a one-line fix.

---

## §2 — ⚑ THE REPLACEMENT LADDER, and its second rung is also refuted

This is the correction that most needs writing down. The obvious repair — *"swap the refuted
injectivity floor for `HashFloorHonesty.CollisionResistant`, the honest computational one"* —
**reproduces the disease.** It is also, per §1.1, a floor with 57 carriers and 47 sole-floor
carriers of its own, sitting in the ratchet's refuted set.

| rung | object | status | refutation / authority |
|---|---|---|---|
| **0** | `Poseidon2SpongeCR`, `compressNInjective`, `Compress8CR`, … — **injectivity** | **FALSE at deployed BabyBear params** | `HashFloorHonesty` §1 pigeonhole core; 27 instances |
| **0′** | `Function.Injective D` for `D : (CellId → AssetId → ℤ) → ℤ` and kin | **FALSE at ANY params, for ANY hash, in ANY field** | `Verify/InjSpelledFloors.lean` — uncountable domain. *Worse than rung 0: no width fixes it.* |
| **1** | `HashFloorHonesty.CollisionResistant F` — keyed family, negligible collision advantage | ⚑ **ALSO FALSE for any compressing family — and DELETED 2026-07-28 (§2.1)** | `FloorGames.hashCRHardQuant_top_false_of_compressing`. It WAS `HashCRHardQuant F ⊤` under a name that hid the `⊤`, and `hard_top_iff_solvableFrac_negl:241` proves **every** unrestricted-adversary floor IS the existence floor. The `Classical.choice` adversary that outputs a collision at every key is a perfectly good one. **There is no rung 1 any more**: the ladder starts at 2, and the `⊤` pole is now written out at every site that used to hide it. |
| **2** | `FloorGames.HashCRHardQuant F Eff` — a real collision **Game** at an **explicit adversary class** | **honest; `Eff` undischarged** | both poles proved: `⊤` false, `⊥` vacuous (`hard_bot_vacuous`). The residual is named: *the tree has no cost model* (`FloorGames` §8; `computable_does_not_restrict`). |
| **3** | `RomQueryFloor.birthday_bound:364` — `winProb (collWin M) ≤ (Q²+1)/‖R‖` for a `Q`-query adversary | ⚑ **PROVED. No hypothesis, no named carrier, no assumption** | information-theoretic, by induction over the query tree. `Eff := RomEff F Q` (adversaries that factor through a `Q`-query `OracleComp`) is a genuine class, and `romEff_not_iff_solvableFrac_negl` proves the rung-1 collapse **fails** for it. |
| **3′** | `Poseidon2RomInstantiation.Poseidon2IsKeyedRandomOracle D w` | the ONE central idealisation, **per-experiment** | satisfiable and refuted-as-`∀w` on both faces. This is the honest name for "Poseidon2 behaves generically". |

### 2.1 ⚑ `def CollisionResistant` IS DELETED — and it cost a gate. ember authorized it; this is the record.

**Landed 2026-07-28.** Rung 1 no longer exists as an object. Read this section as the flag day.

#### What was paid

It was a **named sentinel** in `Verify/FloorCensus.sentinelFloors` with `needRefut = true`, and both
`#floor_census` and `#floor_ratchet` **fail closed — hard error —** when a sentinel name does not
resolve. So deleting the `def` forced deleting that sentinel entry, in the same commit; leaving it
would have reddened the root for every lane rather than gating anything. And its body
(`∀ A, Negl (collisionAdv F A)`) is **not** injectivity-shaped, so the census's DERIVED half cannot
rediscover it: **the sentinel was the only thing gating this floor.** `HashCRHardQuant` cannot take
its place on that list — at a restricted `Eff` it *is* the honest rung 2, and the list is keyed by
head constant, so a `needRefut` entry for it would record `¬ HashCRHardQuant F ⊤` as refuting the
floor at *every* `Eff` and report every honest rung-2 carrier as sitting on a refuted floor. A gate
that lies is worse than an absent one.

**THE WEAKENING, stated plainly: nothing now detects the reintroduction of a floor of this shape.**
An author can write `∀ A : <finder structure> F, Negl (<advantage> F A)` again, under any name, and
neither instrument will say a word. That is a real loss of coverage and it is the price.

- **Who authorized it:** ember, asked directly on 2026-07-27 as a check-weakening — which
  `CLAUDE.md` puts on the short list reserved for the operator — and answering that the `def` goes
  now. Not a drift, not an accident, not an agent's judgement call.
- **What restores it:** a **derived detector** for the shape "universally quantified over an
  unrestricted adversary structure, with a negligible advantage", the way Pass 0 already recognises
  injectivity. That is strictly stronger than the sentinel that was removed: a name-keyed entry only
  catches an author who reuses *this* name, while a shape detector catches the next floor written
  with a fresh structure and a fresh name. This is the follow-up worth doing.
- **Where a future reader meets it:** the removal site itself,
  `Verify/FloorCensus.lean`'s `sentinelFloors` docstring, carries the whole record — including the
  authorization and the restoration path — so it cannot be found without the reason attached.

#### And the tooth SURVIVED, contrary to the work order's expectation

`collisionResistant_false_of_compressing` — the refutation, the thing that made this floor a
*measured* wound rather than an opinion — was expected to die with its subject. It did not. Its
subject moved to the propositionally equal `HashCRHardQuant F (fun _ => True)`, and it is
`FloorGames.hashCRHardQuant_top_false_of_compressing`, same proof, same content. This is **more**
honest than the original: the `⊤` that makes the floor false is now written into the statement
instead of folded into a name. Ported with it: `injective_family_CR` →
`hashCRHardQuant_top_of_injective`, `idFamily_CR` → `idFamily_hashCRHardQuant_top`,
`brokenFamily_not_CR` → `brokenFamily_not_hashCRHardQuant_top`, `mod2Family_not_CR` →
`mod2Family_not_hashCRHardQuant_top`. What genuinely died is
`collisionResistant_iff_hashCRHardQuant_top`, whose only job was to see through the name — an `↔`
needs two sides.

#### How the 45 remaining carriers went

- **26 satisfiability / refutability teeth and family bridges** across the `*Regrounded*` modules —
  **PORTED**, names unchanged, conclusion restated at `HashCRHardQuant … (fun _ => True)` (measured:
  declarations present in both HEAD and the port whose type mentioned `CollisionResistant` before and
  `HashCRHardQuant` after). Every one of them was *about* the `⊤` pole; now it says so. Names are
  unchanged deliberately — `FloorRatchetBaseline` grandfathers carriers BY NAME, so a rename is a
  NEW carrier and hard-errors the gate.
- **9 old-floor ⟹ new-floor bridges** (`_of_keySetCR`, `_of_leafCR`, `_of_noCollision`,
  `_of_rosterCR`, `_of_compressInjective`, `_of_logHashInjective`, `_of_compressionCR`,
  `_of_floorDigestBinds`, `_of_commitTreeInjective`) — **DELETED.** Each implied a refuted floor
  from a refuted floor, and each carried the docstring *"the old floor was STRICTLY STRONGER … so
  nothing is lost re-grounding"*, which is **false**: the `⊤` floor they land on is refuted at a real
  digest too, by a tooth in the very same file. Capability lost: the tree no longer records that
  implication. It is one line to restate and it was never security content.
- **3 prop-body floors.** `Poseidon2KeyedBridge.DomainSeparatedCR` **kept, body rewritten** to
  `HashCRHardQuant (poseidon2KeyedFamily D) (fun _ => True)` — it cannot be defined as
  `DomainSeparatedCREff D ⊤` because that module imports this one, so `domainSeparatedCREff_top_iff_old`
  is now `Iff.rfl`. `WideNativePqCommitment.ComputationalBindingFloor` and
  `CommitFaithfulRegrounded.CollisionResistant` — **DELETED**, both were re-export aliases with zero
  Lean consumers whose whole function was to point a reader at rung 1.
- **The one genuine security consumer,
  `S5Closure.deployed_unfoolable_of_domainSepCR` — PORTED TO RUNG 2**, name kept, now taking
  `HashCRHardQuant (poseidon2KeyedFamily D) Eff` plus a named `hEff`: that the class contains the
  CONSTRUCTED fixed-pair equivocator `foolingRootEquivocator D xs xs'`. That obligation is the honest
  price of a categorical `¬ Foolable` from a hash floor and it is **undischarged**. §5's own teeth
  prove why it cannot be avoided: this floor *forces injectivity*, and injectivity is false at
  BabyBear, so at `⊤` the headline was true with a false antecedent. The concrete-security sibling
  that needs no `hEff`, `DomainSeparatedCREffRegrounded.deployed_lightclientUnfoolable_advantage_bound_eff`,
  bounds the forgery *advantage* instead and is the form a real hash supports.
- The `thread_advantage_bound` tactic's `‹CollisionResistant _›` leaf went with the floor. It cost
  nothing: the floor was a `∀`-statement, so the generic `apply_assumption; done` leaf already closed
  the same goals.

**Read rung 1 → rung 2 → rung 3 as the actual migration.** `InjectiveFloorRegrounded.lean`
§"⚑ Why this is NOT the `CollisionResistant` treatment" (`:23–45`) argues rung 1 is a trap and
is right. Measured state of the 28 `*Regrounded*` modules:

- **14** land on rung 2 (`HashCRHardQuant … Eff`) — correct;
- **7** landed on **rung 1** (`CollisionResistant`) — i.e. re-grounded onto a *second refuted
  floor*. Most priced themselves with a `_top_false` tooth beside it, so this was honest debt
  rather than laundering — but it was debt, and it was the reason `CollisionResistant` had 47
  sole-floor carriers. ⚑ **Drained 2026-07-28** (§2.1): the bridges deleted, the teeth restated at
  `HashCRHardQuant … ⊤`. All 7 now read at rung 2 or above;
- **5** land on rung 3 (`KeyedRomFloor.keyedRom_hard` / `binds_or_collides`) — strictly best;
- **2** are not hash floors.

⚑ And **every one of them is ADDITIVE.** `InjectiveFloorRegrounded`'s own §Non-fake: *"The OLD
injective-floor consumers are KEPT UNTOUCHED — this file only ADDS siblings."* Exactly three
carriers have been genuinely **deleted** (`Poseidon2WideCR`, `compress4Injective`, and the
`Compress8CR`/`Compress1CR` structure *fields*). **A sibling does not drain a ratchet.**

---

## §3 — ⚑ THE UNIFICATION: injectivity is WIDTH-BLIND, which is why the two campaigns are one

Here is the connection the record has never stated, and it is the reason two lanes hit the same
root on the same day.

`∀ xs ys, h xs = h ys → xs = ys` **mentions no width.** It is exactly as false at 8 felts as at
1. So for as long as the tower's binding floors were stated as injectivity, **the width of the
digest could not appear anywhere in the security argument** — there was no number for a wider
encoding to improve. That is why the felt-width campaign's own verdict reads *"width bounds the
IMAGE, it does not PRICE the attack"*: at rung 0 there is no price to move.

The instant you climb to rung 3 the width **becomes** the number, because the bound is
`(Q²+1)/‖R‖` and `‖R‖` is the digest cardinality:

| carrier | `‖R‖` | birthday bar |
|---|---|---|
| 1 felt (`babyBearP ≈ 2^30.9`) | `2^30.9` | **≈ 2^15.5** — a break, not a bound. **Never instantiate here.** |
| 8 felts (`babyBearP^8 ≈ 2^247`) | `2^247` | **≈ 2^123.5** — the real ~124-bit security. **This is the target.** |

`RomQueryFloor.birthday_bound` is already width-agnostic (no width hypothesis), so this is an
**instantiation choice, not new mathematics**.

### The worked template already exists, in one file, at one deployed lane

`metatheory/Dregg2/Circuit/Emit/ShieldedWideValueLinkDescriptor.lean` is the only place in the
tree where both halves are correctly closed together, and it should be read as the pattern:

- `narrow_binding_collision_exists` — **unconditional, no crypto**: *every* BabyBear-bounded
  1-felt binding admits two distinct canonical openings with equal tags. Pigeonhole over 2^32
  openings vs `p < 2^31` tags; birthday finds one in ~2^15.5. **The narrow floor is not weak, it
  is UNSATISFIABLE.**
- `WideBindingCR permOut:317` — the same binding at **8 lanes**, quantified over **canonical
  openings only** (limbs < 2^16, randomness < p). Canonical domain ≈ 2^159 against a range
  ≈ 2^248, so **counting does not refute it** — and `wideBindingCR_satisfiable:732` exhibits an
  inhabitant. This is why it sits in §1.2 as *legitimately* unrefuted.
- `birthday_collision_no_longer_forges:786` — the composition: every 1-felt binding admits a
  canonical collision pair, and on **any** such pair the 8-felt binding still separates.

**The repair therefore has two moves and needs both:**

> **(a) RESTRICT THE DOMAIN to the canonical encoding** — a `Ranged`/`CanonicalOpening`
> predicate, so the domain stops being infinite; and
> **(b) WIDEN THE CODOMAIN to 8 felts** — so the cardinality count stops applying and the
> birthday bar reads 2^123.5 instead of 2^15.5.

Do (b) alone and you get `Poseidon2WideCR` — widened, still `∀ xs ys` over infinite `List ℤ`,
still pigeonhole-refuted, **deleted**. Do (a) alone and a 1-felt codomain still collides.
`Verify/InjSpelledFloors.lean` names the same two-move answer for the uncountable half:
*"commit the FINITE support actually touched, never the whole function"* — that is move (a) at
its most extreme, and it is the **only** repair for rung 0′, where widening does nothing.

⚑ **`CircuitSoundness.CommitSurface`'s `restFrame : RestHashIffFrame RH` is the pure rung-0′
case** and is the largest single object in the way (227 binder positions, 80 modules, 409
declarations reached). `RestFrameCardinalityFloor.restHashIffFrame_false_by_cardinality` refutes
it for **every** `RH`, at any width, and both campaign instruments are structurally blind to it.
See `PARKED-vacuity-campaign.md` §2 — that is a multi-session port, not a swarmcycle.

---

## §4 — `Dregg2/Bignum.lean`, assessed by reading it

**It is not the fix for the hash floors, and it was never claimed to be.** Bignum is schoolbook
integer arithmetic — `compare` / `sub` / `add` / `mul` / `mod` / `range` — with soundness +
completeness `_iff` keystones and four anti-exploit theorems (no-overflow, no-underflow-wrap,
field-vs-integer, canonicality). It contains no hash.

**Its actual role in this class is move (a) of §3.** `Ranged B` is the canonicality predicate
that makes a domain finite; `Dregg2/Bignum/DigitInjective.lean:42 bignumVal_injective` is the
theorem that a range-checked limb list **is** an injective encoding — with `:166` as the
negative pole (drop `Ranged` and it is *false*, not merely weak). That is exactly the
`CanonicalOpening` discipline `WideBindingCR` rides.

### The "~3% adopted" figure has been measured and retired

`docs/CENSUS-bignum-adoption-2026-07-25.md` measured it: **~11 genuine adopt-sites, 2 of them
security-load-bearing.** Most files saying "limb" mean a *digest lane* (which needs no bignum)
or an ML-KEM/ML-DSA polynomial coefficient (where adopting it *would be wrong*). Live counts:
**7** files import `Dregg2.Bignum`; the arithmetic layer (Add/Sub/Mul/Mod) has exactly **one**
consumer outside its own module tree (`Bignum/LedgerBalance`); the `bignumVal`/`Ranged`
denotation has **6**; the one export with real fan-out is `legs_noWrap_conservation` (3 real
uses). So "3%" is right *as a feeling about the arithmetic layer* and wrong as a work estimate.

### What actually blocks wider adoption — ranked, each read

1. **Wire-format / VK-epoch flag day.** The only place adoption is explicitly sequenced —
   `docs/FINDING-balance-encoding-divergence-2026-07-26.md:52-67` — says it *"rides the
   re-genesis flag day that is already in flight, or it waits"*. `MapOpWideKey.lean`'s header
   says the same for the MapOp lane: the widened chip row is a **VK epoch**.
2. **⚑ The `Expr` → `EmittedExpr` seam, and this is the most fixable item.** Bignum's four
   "emittable" ties (`addLimbEqn_is_gate`, `mul2LimbEqn_is_gate`, `modEqn_is_gate`,
   `subLimbEqn_is_gate`) are all stated over `Circuit.Constraint`/`Expr`. Every registered
   descriptor authors `EmittedExpr` directly. The bridge `emitExpr`/`emitConstraint`
   (`Exec/CircuitEmit.lean:90`, with a round-trip proof at `:149`) **has zero call sites outside
   its own file.** So "Bignum is EMITTABLE, not a mirror" is true at the `Constraint` level and
   has **no wired path into any registered descriptor**. Nobody has touched this.
3. **The `[0, p)` range-table wall — genuinely hard.** A power-of-two range table cannot express
   `[0, p)` at all (`2^27 < p < 2^31`), and `MapOpWideKeyCanonDischarge`'s
   `lexBlock_invariant_under_p_shift` proves this is **not fixable by adding teeth** —
   canonicity of a raw full-felt cell is a model artifact. This is why the MapOp lane uses a
   bespoke lex-compare gadget (`Emit/LexCompare8Emit.lean`) rather than Bignum's `borrowSub_iff`:
   they are different algorithms, so "adopt Bignum in MapOp" is a rewrite, not a substitution.
4. **AIR width — real, priced, bounded.** `circuit/src/lean_descriptor_air.rs:188,229-232,263`:
   a range gate appends `Σ ranges.bits` boolean aux columns and bumps constraint degree to 2. At
   MapOp the widening is a proved cost: **+7 felts per map-op row, +14 per leaf absorb**
   (`MapOpWideKey.lean:269-270`).
5. **Rewrite-every-encoder — the *smallest* of these**, bounded at ~11 files by the census.
6. **A missing multi-limb hash — NOT a blocker.** `imtLeafHash8` (arity 17) and
   `wireCommitR8`/`Poseidon2Width8` exist and are the designated reuse.

`Dregg2/Bignum/LedgerBalance.lean` `biasedLimbs_valid` (completeness) and its soundness twin
`biasedLimbs_unique` are both proved and pinned with `#assert_axioms`.

**And the four deployed byte→felt encoders are non-injective by construction — all four, not
three** (`docs/WOUND-felt-width-boundaries-2026-07-19.md:1630-1633`): one is a linear form, two
reduce each 4-byte chunk mod `p`, one discards 16 bits.

---

## §5 — What the apex actually needs, measured

`FriLdtExtractDeployed.algoStarkSound_transferV3_cons:641` has exactly **two** real premises:
`hCR : Poseidon2SpongeCR sponge` and the extraction bundle. The `hCR` chain is **four links and
one leaf**, and *nothing in links 1–3 inspects the hypothesis — they thread it*:

| # | lemma | use of `hCR` |
|---|---|---|
| 1 | `algoStarkSound_transferV3_cons:641` | forwards to #2 |
| 2 | `mainAirAcceptF_of_floor_cons:538` | forwards to #3 |
| 3 | `hood_of_reductions_cons:497` | **one line** (`:523`) → `commitmentOpening_binds_of_poseidon2CR` |
| 4 | `OodCommitmentBinding.commitmentOpening_binds_of_poseidon2CR:207` | forwards to #5 |
| 5 | `OodCommitmentBinding.merkleRecomputeZ_binds:189` | **THE LEAF** |

⚑ **The leaf does NOT need injectivity.** It applies the hypothesis to exactly one argument:
`(merkleFind_spec …).2`, the second component of a spec about a **total constructive extractor**
`merkleFind` whose output pair is already known distinct with equal images. Injectivity is used
*only to contradict an already-extracted collision pair* — precisely the shape a collision-game
advantage bound discharges. `merkleRecomputeZ_binds` is already doc-marked **"⚑ DEMOTED"**, and
the floor-free replacement **already exists**: `OodCommitmentBinding.merkleOpening_binds_rom:280`,
carrying **no floor hypothesis at all**, backed by `KeyedRomFloor.keyedRom_hard` (rung 3).

**So the answer to "does the apex genuinely need injectivity?" is NO — it needs a per-instance
non-collision at one extracted pair.** The blocker is **shape, not content**:
`merkleOpening_binds_rom` concludes `Negl (gameAdv …)` while `hood_of_reductions_cons` needs the
*equality* to rewrite `hlayout` at `:526-528`. The fitting shape is the `_or_collides` / `¬…Coll`
idiom the rest of the tree already adopted. **Cost: 4 lemma restatements (one trivial) plus 8
identical call sites of `commitmentOpening_binds_of_poseidon2CR` tree-wide.**

⚠ **Independent, and not touched by any of this:** the apex's *other* vacuity. Every corrected
bundle still carries `topen ∈ tableOpenings`, which acceptance does not supply —
`deployed_accepting_pole_has_no_tableOpenings:902` is a `decide`-backed accepting run with
`tableOpenings = []`. Routing off `hCR` removes one of the apex's two vacuities, not both.

### ✅ 2026-07-28 — LANDED. The apex rests on no refuted floor.

`algoStarkSound_transferV3_cons`, `starkSound_of_friLdtExtractFaithful_transferV3` and
`StarkSoundFriLdt.starkSound_of_friLdtExtract_transferV3` now take **no floor hypothesis at all**.
The estimate above was right about the content and wrong about one thing worth writing down:

⚑ **The residual cannot be a BINDER at the apex — it has to enter through the BUNDLE.** At
`hood_of_reductions_cons` the opening data (`idx`, `siblings`, `topen`, `vCommitted`) are explicit
binders, so a per-instance `¬ OpeningColl sponge idx topen.constraintEval vCommitted siblings`
swaps straight in for `hCR`. At the apex those four are **existentially bound inside
`FriLdtExtractV3Cons`**, so there is nothing to state the residual *about*. Quantifying it
universally would have re-created a global Merkle-binding floor — the forbidden move. So the
conjunct went into the corrected bundles (`FriLdtExtractV3Cons`, `FriLdtExtractV3Faithful`,
`FriLdtExtractV3FaithfulNoOodShape`, `ApexOodLaneRepair.FriLdtExtractV3ConsNoOodShape`), where it
sits beside the two Merkle recomputes those bundles already deliver.

What that cost, exactly: the LANDED `FriLdtExtractV3` never carried the conjunct, so
`friLdtExtractV3_imp_cons` is **deleted**, and with it four migration receipts
(`StarkSoundReduce.retiredPremise_imp_reducePremise`,
`StarkSoundFriLdt.retiredPremise_imp_apexPremise`,
`StarkSoundFriLdtCorrected.landedPremise_imp_correctedPremise` and
`.starkSound_of_friLdtExtract_transferV3_via_corrected`). All five were transports **out of a
premise proved to make `verifyBatch` reject every input**, so nothing that ever transported was
lost. The landed bundle is deliberately not given the conjunct — it is the SUBJECT of the theorems
that prove it empty.

Landed in `OodCommitmentBinding`, with `merkleRecomputeZ_binds` and
`commitmentOpening_binds_of_poseidon2CR` **deleted**:

- `OpeningColl sponge idx l1 l2 siblings` — the pair `merkleFind` extracts really is a collision;
- `openingColl_self_false` / `honest_run_needs_no_residual` — **dischargeable, and totally**: a
  non-equivocating opening kills the side condition for every sponge, index and path, with no
  hypothesis. The honest path pays nothing for the port;
- `openingColl_of_constant_sponge` — refutable, so `¬ OpeningColl` is not free;
- `openingColl_refutes_poseidon2CR` — the deleted floor implied it, so the port is a visible
  WEAKENING (stated in the ¬-direction so it is anti-floor content and assumes no floor);
- `merkleRecomputeZ_binds_of_noColl` / `commitmentOpening_binds_of_noColl` — the binding;
- `opening_equivocation_exhibits_coll` — the converse, so the residual is *equivalent* to the
  binding at that opening rather than merely sufficient for it.

Priced by rung 3, unchanged: `merkleOpening_binds_rom` bounds a query-bounded prover's advantage in
producing exactly this event on `KeyedRomFloor.keyedRom_hard`.

**Measured delta:** 22 declarations shed their `Poseidon2SpongeCR` binder, 7 declarations deleted,
2 inline-spelled baseline entries removed (282 → 280), **zero baseline entries added.**

**NOT ported, named at each site in source:** five consumers whose opening data arrives from a
*different* bundle — `OodExtChallengeLayout.DecodedLdtLinkExt`,
`OodSingletonRepair.DecodedLdtLinkExtCons`, `ApexOodLaneRepair.FriLdtExtractCons`. They keep their
already-grandfathered `Poseidon2SpongeCR` binder and DERIVE the residual through
`openingColl_refutes_poseidon2CR`. One conjunct on each of those three bundles finishes it.

---

## §6 — The ordered plan, with effort bands

**The governing rule, from the measurement: a declaration stays a carrier while ANY floor
remains. Multi-floor sites must shed EVERY floor in one pass, or the metric does not move.**

| band | work | size | why here |
|---|---|---:|---|
| **A — hours** | Refute the 4 false-but-undetected floors of §1.2 (`Hash4Injective`, `Hash4NoCollision` ✅, `Node8CROnFxc4`, `SpongeCROnCarrier`) **and port their consumers in the same commit**. Each is 1 file, 1–2 carriers. | 4 commits | Refuting **arms the gate automatically** (`refutedFloors` is derived, not listed). Porting in the same commit keeps the net carrier delta at zero, so no co-tenant's root goes red. **Never refute without porting.** |
| **A — one edit** | `CLAIMS-LEDGER-vacuity.md` rows 42/43: labelled CITABLE, refuted 7 lines below themselves. | 1 doc edit | A CITABLE label is what gets quoted externally. |
| **A — one edit** | The 3 stale pointers of §1.3. | 1 commit | `poseidon2WideCR_false_babyBear` does not exist and is cited 5×. |
| **B — a swarmcycle** | **`Poseidon2SpongeCR`'s 707 sole-floor carriers.** | 707 sites | The only place unit-of-work and unit-of-progress coincide (97% sole). Repair = the standard per-instance residual; the extractor idiom and `Tools/ConePort` exist. |
| ~~**B — a swarmcycle**~~ ✅ | ~~The **apex chain** (§5)~~ — **LANDED 2026-07-28.** Cost was 22 restatements + 7 deletions across 12 files, not 12 decls: the residual had to enter through the corrected BUNDLES, because the apex cannot name the extraction data. | done | One of the apex's two vacuities is gone. `topen ∈ tableOpenings` remains. |
| **C — a swarmcycle** | The four-combo batch table: 473 of 547 multi-floor sites in **4** combos. | 473 sites | Sequence **after** their floors' endpoints; shed all floors per site. |
| **C — a real build** | Move the 7 rung-1 `*Regrounded* → CollisionResistant` modules up to rung 2/3, and **delete the old carriers rather than adding siblings**. | 7 modules | 28 regroundings are additive; a sibling does not drain a ratchet. **Started 2026-07-28**: the two ENDPOINT carriers (`HashFloorHonesty.equivocation_advantage_negligible` / `.friFold_advantage_negligible` — the only two declarations in the tree that CONSUMED the floor rather than talking about it) are deleted and restated at rung 2 as `FloorGames.*_eff`. 45 sole-floor carriers remain; see §2.1. |
| **D — multi-session** | **`CommitSurface`**, shedding `restFrame` **in the same pass** as the four CR fields, via the finite-support redesign. | 409 decls reached | Rung 0′: widening does nothing; the domain must become finite. `PARKED` §2 is the brief. |
| **D — a real build** | Instantiate `RomQueryFloor.birthday_bound` at the **8-felt** carrier (`‖R‖ = p^8`) and wire it under the ported endpoints. | repackaging | §3. Width-agnostic already, so an instantiation, not research. ⚑ **Never instantiate at 1 felt** — that proves a theorem about a bug (2^15.5). |
| **E — open design** | Decide whether `#floor_ratchet`'s derivation grows to recognise ∀-iff-shaped floors like `RestHashIffFrame`. | decision | Right now it is undecided, which silently means "human-recognised only". |

---

## §7 — FIRST SLICE, LANDED

`metatheory/Dregg2/Circuit/Emit/AutomataflRevealRefine.lean` — the class's cleanest exhibit of
**"a documented wound is not a detected one"**, and of §3's width unification in miniature.

Its `Hash4NoCollision` floor's own docstring already read *"not a practical deployment
assumption for a one-BabyBear-felt codomain: globally it cannot hold, and generic birthday
search is about `2^15.5`"* — the finding, the width, and the number, all correct, and **all
prose**. Because it was never a theorem, `#floor_ratchet` could not derive it as a refuted
floor, so both of its consumers passed the gate while being vacuous at deployed parameters.

Landed, in one commit:

- **`hash4NoCollision_false_babyBear`** — the tooth. Pigeonhole via the diagonal
  `n ↦ [n,0,0,0]`, same counting core as `poseidon2SpongeCR_false_babyBear`. No collision
  exhibited, none needed.
- **`RevealColl hash a b`** — the honest per-instance residual: a collision at the exact
  preimage pair the extractor produces. With **both poles proved**:
  `revealColl_self_false` (dischargeable — a gate that refuses everything is not a repair) and
  `revealColl_of_constant_hash` (refutable — so `¬ RevealColl` is not free).
- **`not_revealColl_of_hash4NoCollision`** — the old floor implies the new residual, so the port
  is visibly a *weakening of the hypothesis*, not a change of subject.
- **`opening_unique_or_collides`** — bind, or EXHIBIT the collision. **Floor-free.**
- `opening_unique_of_noCollision` **DELETED**, replaced by `opening_unique_of_noResid`;
  `legS_swap_refused` restated on the residual.

**Net carriers of `Hash4NoCollision` after this commit: zero.** The floor becomes derivable as
refuted — arming the gate for anyone who reintroduces it — while adding **no** baseline entry,
so no co-tenant's root build goes red.

**Verification, at the resolution actually achieved:** elaborated green on hbox
(`lake env lean`, EXIT=0, no errors) with all **13** `#assert_axioms` in the file passing —
`#assert_axioms` hard-errors on anything outside `{propext, Classical.choice, Quot.sound}`, and
it caught a real `sorryAx` leak on the first attempt. `scripts/check-floor-baseline-preflight.sh`
passes: *"22 floor name(s), 2138 baseline entries; no unbaselined carrier."*
⚠ **The whole-root `lake build Dregg2` (≈10 362 jobs) was NOT run** — the one warm Lean lane on
hbox was held by a co-tenant. `#floor_ratchet` is the authority and it has not adjudicated this
commit. Expected green, not established.

---

## Appendix — where to go next

| for | read |
|---|---|
| the draining plan, operational laws, exact commands | `docs/PARKED-vacuity-campaign.md` |
| the measured surface (TSV + provenance) | `docs/artifacts/floor-census-v2-2026-07-26/` |
| the apex's *other* vacuity, and the (a)/(b)/(c) floor split | `docs/OPENING-SOUNDNESS-DECONFLATED.md` |
| the two-move repair, worked end to end | `metatheory/Dregg2/Circuit/Emit/ShieldedWideValueLinkDescriptor.lean` |
| why `CollisionResistant` was not the answer, and where it went | `metatheory/Dregg2/Crypto/FloorGames.lean` §2, §6, §8 |
| the gate its deletion cost, who authorized it, what restores it | `metatheory/Dregg2/Verify/FloorCensus.lean` — `sentinelFloors` docstring |
| the floor that is actually proved | `metatheory/Dregg2/Crypto/RomQueryFloor.lean` §5 |
| the canonical-encoding half | `metatheory/Dregg2/Bignum/DigitInjective.lean`, `docs/CENSUS-bignum-adoption-2026-07-25.md` |
