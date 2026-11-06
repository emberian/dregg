# THE DIGEST-WIDENING PLAN — widen the CODOMAIN, and the one-felt endpoints that still have not been

**2026-07-28.** `b44170f73` ported the wide-key map family off the refuted `Poseidon2SpongeCR`
floor onto per-instance non-collision residuals, and in doing so made the honest number visible for
the first time. The number is bad, and this file is the plan for moving it.

The finding, restated once: **`leafOfW`, `mapRootW` and `imtLeafHash8` all return ONE BabyBear felt
at every key width.** The kind-D epoch widened the *absorbed preimage* (map leaf arity 2 → 9, IMT
leaf 3 → 17) and **not the digest**, so on `Crypto.RomQueryFloor.birthday_bound`'s honest rung
(`(Q²+1)/‖R‖`) the bar reads `‖R‖ = babyBearP ≈ 2^30.9` at `wideEnc` exactly as at `narrowEnc`.
**Preimage width buys zero bits.** The number that moves is `‖R‖`.

`docs/INJECTIVITY-FLOOR-CLASS.md` §3 is the theory; this file is the inventory, the cost, and the
order.

---

## §0 — What LANDED with this file, and at what resolution

`metatheory/Dregg2/Circuit/MapOpWideDigest8.lean` (commit `eeffb70fb`). Import line, for a rooting
edit the operator makes:

```lean
import Dregg2.Circuit.MapOpWideDigest8
```

⚠ **It is deliberately NOT added to `metatheory/Dregg2.lean`.** So `lake build Dregg2` cannot see
it and **`#floor_ratchet` has not adjudicated it.** What *was* established: elaborated green on
hbox lane `mapop-wide` (`lake env lean`, EXIT=0, zero errors) with **all 31 `#assert_axioms`
passing** — those hard-error on anything outside `{propext, Classical.choice, Quot.sound}` — and
`scripts/check-floor-baseline-preflight.sh` reading *"24 floor name(s), 2062 baseline entries; no
unbaselined carrier."* No `sorry`, no `native_decide`, **zero new baseline entries.**

### The numbers are now theorems, not docstrings

This is the half that was missing. `birthday_bound` is width-agnostic — no width hypothesis — so
instantiating it is arithmetic, not research, and nobody had done it at the two widths the tree
deploys. Now:

| statement | content |
|---|---|
| `narrow_bar_vacuous_at_2pow16` | at `Q = 2^16` the one-felt bound is **`≥ 1`** — it states nothing a probability does not state for free |
| `narrow_break_exactly_at_44870` | the one-felt bar dies at **`Q = 44870 ≈ 2^15.45`**; the prose "≈ 2^15.5" IS that integer |
| `narrow_bar_says_nothing_at_2pow64` | at a real attacker budget the one-felt bound exceeds `1` by ≈ `2^97` |
| `wide8_bar_at_2pow64` | the eight-felt bound at the same budget is **`≤ 2^-119`** |
| `wide8_break_exactly_at_p4` | the eight-felt bar dies at **exactly `babyBearP^4 = 16428751811598850197311699254593454081 ≈ 2^123.63`** — `‖R‖ = babyBearP^8` is a perfect square, so the threshold is an integer |
| `wide8_bar_ratio` | at **every** budget the eight-felt bar is `babyBearP^7 ≈ 2^216` times smaller |
| `romBar_antitone_in_codomain` | the codomain is the **only** lever |

⚑ Every bar theorem is stated over an **arbitrary finite domain**, deliberately: that is the kind-D
error in its exact form. The arity-9 absorb and the arity-2 absorb are one instance of one theorem
with one conclusion. `romBar Q N` mentions `Q` and `N` and nothing else.

### The endpoint that moved

`MapOpWideKeyGate.mapRootW_injective` → `MapOpWideDigest8.mapRootW8_injective`, through:

- `leafOfW8` — the **byte-identical** preimage `leafPreW E e` (`leafPreW_arity_unchanged` proves the
  arity did not move) absorbed into `Heap8Scheme.chipAbsorb8` instead of a scalar sponge;
- `mapRootW8` — folded by `MapMerkleRoot` §5b's `perfectRoot8` (arity-16 `node8`), so the image is
  `Digest8` **all the way to the root** instead of being crushed back to one felt at the first node.
  `mapRootW` folded with `perfectRoot hash`, whose node is `mapNode hash l r = hash [l,r] : ℤ` — so
  even an 8-felt *leaf* would have died at level 1. This is why the leaf alone is not the fix;
- the openings — `opensToMerkleW8`, `writesToMerkleW8`, the anti-ghosts over explicit witness
  heaps, and the nullifier tooth `opensToMerkleW8_some_excludes_none_or_collides`.

**Before / after, at the same statement:** a some/none equivocation behind one committed root costs
**≈ 2^15.45 queries** to exhibit at `mapRootW`, and **≈ 2^123.63** at `mapRootW8`.

Three poles, and the third is the one that matters: `mapRootCollW8_dischargeable` (the honest prover
pays nothing, every chip, no assumption); `mapRootCollW8_refutes_compress8CR` (exhibiting the
residual **refutes** the floor, so the port is a visible weakening and assumes no floor content);
and `mapRootCollW8_fires_on_constant_chip` — **satisfiable**, a constant chip really does equivocate
and the extractor hands back `([0,0], [1,0])`. Without that third pole `mapRootW8_injective` could
have been secretly unconditional, which is an over-claim of exactly the kind this campaign exists to
catch.

**The cost, in the file:** node absorb arity `2 → 16` (`pack8_arity`); committed digest felts
`2^(d+1)−1 → 8·(2^(d+1)−1)`. At the deployed `HEAP_TREE_DEPTH = 16` that is **917 497 extra
committed felts per full tree**, against a bar that improves by ≈ `2^216`. A wider digest is not
free and the file says so in Lean, not in prose.

---

## §1 — ⚑ THE SEAM FINDING, and it reverses the usual direction

Found while assessing the emit blocker, and it is the single most useful thing in this file.

**The DEPLOYED IR-v2 map-op descriptor already commits EIGHT lanes. The Lean denotation of it reads
LANE 0.**

- `metatheory/Dregg2/Circuit/DescriptorIR2.lean:301` — `structure MapOp` carries
  `root : Fin 8 → EmittedExpr` and `newRoot : Fin 8 → EmittedExpr`.
- `circuit/src/descriptor_ir2.rs:587-596` — `pub root: Vec<LeanExpr>` / `pub new_root`, and
  `:1069`/`:1084` **hard-error** if `root.len() != CHIP_OUT_LANES` (= 8). The Rust side validates
  eight lanes on every parse.
- `metatheory/Dregg2/Circuit/DescriptorIR2.lean:577` — `MapOp.holdsAt (hash : List ℤ → ℤ) …` reads
  `(m.root 0)` and `(m.newRoot 0)` in **all five** kinds (`read`/`absent`/`write`/`insert`/
  `aafiInsert`), through the scalar `opensTo`/`writesTo`.
- Its own docstring at `:303-307` says so: *"The per-row denotation (`holdsAt`) reads lane 0 only
  (the scalar `writesTo`/`opensTo`); the full 8-felt faithfulness is trace-forced by the heap
  after-spine keystone (`HeapOpenEmit`)."*

So the shipping circuit commits ~2^247 of digest and the Lean semantics of that circuit describes
~2^30.9 of it. That is the 2^15.45-vs-2^123.63 gap, sitting **at the Lean/Rust seam**, not in some
unshipped model.

### The named rescue, checked

The docstring's rescue is real machinery but it is **a different object**, and I could not find the
weld. `Emit/HeapOpenEmit.lean:244 heapOpen_writesTo8` genuinely forces an 8-felt write — but its
conclusion is `Emit.EffectVmEmitRotationV3.heapWritesTo8`, and its consumers are
`Emit/AccumulatorOpenEmit.lean` and `metatheory/Dregg2/Circuit/RotatedKernelRefinementCapFamily.lean` (the **rotated**
kernel-refinement cone). **No declaration relates it to `MapOp.holdsAt`.** Measured by grep, not by
reading a proof, so state it as: *the 8-felt heap-open keystone exists and is welded into the
rotated cone; whether it discharges `MapOp.holdsAt`'s lane-0 denotation is an open, unstated
obligation.* Closing or refuting that weld is **step 1** below and is the highest-value item in
this file.

---

## §2 — THE EMIT BLOCKER, assessed with evidence — and the record points at the wrong seam

`docs/INJECTIVITY-FLOOR-CLASS.md` §4.2 names it: *"The bridge `emitExpr`/`emitConstraint`
(`metatheory/Dregg2/Exec/CircuitEmit.lean:90`, with a round-trip proof at `:149`) has zero call sites outside its own
file."*

**That is TRUE and I confirm it** (`grep -rn "emitExpr\|emitConstraint"` over
`metatheory/**/*.lean`, excluding `metatheory/Dregg2/Exec/CircuitEmit.lean`: **0 hits**; 27 in-file). But it is not
the blocker, and the real one is worse:

### 2a. `emitConstraint`'s TARGET is a retired rail

`emitConstraint : Constraint → EmittedConstraint` lands in `EmittedDescriptor` — IR-**v1**. And
`circuit/src/lean_descriptor_air.rs:3-9`, the file's own header:

> ⚠ **RETIRED / IR-v1 — NOT the live law-#1 rail (marked 2026-07-16).** `LeanDescriptorAir` here is
> referenced ONLY inside this file: no deployed path instantiates it. … Lean's `metatheory/Dregg2/Exec/CircuitEmit.lean`
> (`emit_faithful`) emits to THIS v1 `EmittedDescriptor` target, so those faithfulness theorems are
> real but land on a path nothing runs.

Confirmed: `grep -rn "LeanDescriptorAir" --include="*.rs"` outside that file → **0**; inside → 15.
`EmittedDescriptor` appears in **no other Rust file**. So **wiring `emitConstraint` would wire
Bignum into a dead rail.** The record's "most fixable item" is, as stated, not fixable — it is the
wrong end.

### 2b. `emitExpr`, by contrast, is exactly right and free

IR-v2 **reuses `EmittedExpr` as its leaf type** — `DescriptorIR2.lean:50` opens it, and `MapOp`,
`MemOp`, `Lookup`, `ProofBind` are all built from it. So `emitExpr : Circuit.Expr → EmittedExpr` is
the correct bridge and comes with `emitExpr_eval` and `decodeExpr_emitExpr` already proved. Nothing
is missing on the expression half except a caller.

### 2c. What is genuinely missing — two small bridges, both absent

| bridge | from (Bignum) | to (IR-v2) | status |
|---|---|---|---|
| expression | `Circuit.Expr` | `EmittedExpr` | **EXISTS** (`emitExpr`, proved), 0 callers |
| gate | `Circuit.Constraint` (`lhs = rhs`) | `Emit.EffectVmEmit.VmConstraint.gate (body : EmittedExpr)` (`body = 0`) | **ABSENT** |
| range | `Circuit.Lookup.rangeCheck` / `rangeTable k` | `DescriptorIR2.Lookup { table := .range, tuple }` | **ABSENT** |

The gate bridge is one definition and one agreement lemma:
`⟨lhs, rhs⟩ ↦ .gate (.add (emitExpr lhs) (.mul (.const (-1)) (emitExpr rhs)))`, plus
`holdsAt ↔ Constraint.holds`, proved exactly as `emitConstraint_holds` is. **`EmittedExpr` has no
`sub` constructor**, which is why the `(-1)·` idiom — the one Bignum's own gate statements already
use — is the right shape.

The range bridge is the real work but it is bounded: `DescriptorIR2.lean:115` describes the limb
table as *"rows are exactly `[v]` for `v ∈ [0, 2^bits)`"*, which is the same shape as
`Circuit.Lookup.rangeTable k`, so the agreement is a short proof rather than a redesign.

### Verdict, plainly

**Bignum's emit path IS wireable, and cheaply — but not the way the record says.** Do not call
`emitConstraint`. Write the two IR-v2 bridges (≈ 2 defs + 2 agreement lemmas), reuse `emitExpr`,
and land it under **one** registered descriptor. What that does **not** fix is the
`[0, p)` range-table wall (`docs/INJECTIVITY-FLOOR-CLASS.md` §4.3), which is genuinely hard and is
why MapOp uses a bespoke lex-compare gadget rather than Bignum's `borrowSub_iff`.

⚠ And note what Bignum is **not**: `docs/INJECTIVITY-FLOOR-CLASS.md` §4 already established that it
contains no hash and is **not** the fix for the digest floors. Its role in this campaign is move
(a) — canonical-encoding domain restriction (`Ranged`, `bignumVal_injective`). **This file's
migration is move (b), and it needed none of Bignum.** Wiring Bignum's emit path is worth doing on
its own merits; it is not on the critical path for digest widening.

---

## §3 — THE INVENTORY: one-felt digest endpoints

**Method:** `grep -rn` / `-rho` over every `.lean` in `metatheory/`. "refs" counts the `def`, every
theorem mention **and docstring prose**, so read it as a **blast-radius proxy**, not a consumer
count. **All of these carry the same ROM number** — the bar is a function of the codomain and
nothing else, so every row below reads `romBar Q babyBearP`: **vacuous at 2^16 queries, dead at
Q = 44870 ≈ 2^15.45.** Quoting one number for the whole table is the point.

### 3a. Map tree, IMT and heap — the family whose 8-felt tower is already BUILT

| endpoint | file:line | codomain | refs | 8-felt sibling |
|---|---|---|---:|---|
| `leafOfW` | `metatheory/Dregg2/Circuit/MapOpWideKeyGate.lean:243` | `ℤ` | 104 | ✅ **`leafOfW8`** — `metatheory/Dregg2/Circuit/MapOpWideDigest8.lean:234` (this commit) |
| `mapRootW` | `metatheory/Dregg2/Circuit/MapOpWideKeyGate.lean:393` | `ℤ` | 76 | ✅ **`mapRootW8`** — `:306` (this commit) |
| `mapNode` | `metatheory/Dregg2/Circuit/MapMerkleRoot.lean:84` | `ℤ` | 68 | ✅ `DeployedHeapTree.heapNodeOf8:70` |
| `foldLevel` | `metatheory/Dregg2/Circuit/MapMerkleRoot.lean:98` | `List ℤ` | 56 | ✅ `foldLevel8:503` |
| `perfectRoot` | `metatheory/Dregg2/Circuit/MapMerkleRoot.lean:105` | `ℤ` | 236 | ✅ `perfectRoot8:510` |
| `mapRoot` | `metatheory/Dregg2/Circuit/MapMerkleRoot.lean:407` | `ℤ` | 201 | ✅ `mapRoot8:712` + `mapRoot8Find`, `MapRootColl`, `opensToMerkle8` |
| `pathRecompute` | `metatheory/Dregg2/Circuit/MapOpsColumnLayout.lean:180` | `ℤ` | 154 | ~ no `pathRecompute8`; `DeployedCapTree.recomposeUp8:859` is the shape |
| `aafiLeafHash` | `metatheory/Dregg2/Circuit/MapOpsColumnLayout.lean:1307` | `ℤ` | 49 | ~ `MapOpWideKeyGate.aafiLeafHashW:1161` — **still 1 felt** |
| `Heap.leafOf` | `Substrate/Heap.lean:387` | `ℤ` | **356** | ✅ `heapLeafDigest8:65` |
| `Heap.root` | `Substrate/Heap.lean:392` | `ℤ` | 123 | ~ partial, via `Heap8Scheme` |
| `imtLeafHash` | `metatheory/Dregg2/Circuit/IndexedMerkleTree.lean:133` | `ℤ` | **253** | ~ `heapLeafDigest8` is the arity-3 twin |
| `imtLeafHash8` | `metatheory/Dregg2/Circuit/MapOpWideKey.lean:281` | **`ℤ`** | 21 | ❌ — **wide INPUT, narrow OUTPUT: the kind-D error, named** |
| `imtLeafHash8Of` | `metatheory/Dregg2/Circuit/MapOpWideKeyGate.lean:1038` | **`ℤ`** | 63 | ❌ |
| `aafiLeafHashW` | `metatheory/Dregg2/Circuit/MapOpWideKeyGate.lean:1161` | **`ℤ`** | 27 | ❌ |
| `imtLeafHashE` | `metatheory/Dregg2/Circuit/MapWideImtPadOpen.lean:150` | `ℤ` | 43 | ❌ |
| `padImtRootE` | `metatheory/Dregg2/Circuit/MapWideImtPadOpen.lean:325` | `ℤ` | 17 | ~ `padImtRoot8:669` exists and is **also `ℤ`** |
| `padImtRoot` | `metatheory/Dregg2/Circuit/MapPaddedDenotation.lean:486` | `ℤ` | 64 | ❌ — docstring: **"⚑ THE DEPLOYED MAP COMMITMENT"** |
| `padMapRoot` | `metatheory/Dregg2/Circuit/MapPaddedDenotation.lean:365` | `ℤ` | 12 | ❌ |
| `appendOrderRoot` | `metatheory/Dregg2/Circuit/MapKindImtGates.lean:882` | `ℤ` | 9 | ❌ — docstring: *"`fold_append_order_8`'s 1-felt face"* |
| `opensTo` / `writesTo` | `metatheory/Dregg2/Circuit/DescriptorIR2.lean:534,539` | `ℤ` | — | ✅ `opensToMerkle8` / `writesToMerkle8` (§5b) |
| `MapOp.holdsAt` | `metatheory/Dregg2/Circuit/DescriptorIR2.lean:577` | reads **`root 0` only** | — | ⚠ **the seam — §1** |
| ⚑ `MapLeafSchema.commit` | `metatheory/Dregg2/Circuit/MapDenotationSchema.lean:134` | **structure FIELD**, `… → ℤ` | 3 field / `padImtSchema` 129 | ❌ — **the chokepoint, §3e** |

`narrowLeafHash` (`MapOpWideKey.lean:335`, 4 refs) and `halfWideLeafHash`
(`MapOpWideKeyGate.lean:1071`, 5 refs) are **deliberate anti-launder counterexamples** and must STAY
one felt. A widening sweep must not "fix" them.

### 3b. Cap tree — every primitive already has a `…8` sibling in the same file

`DeployedCapTree.lean`: `CapHashScheme.chipAbsorb:158` (71) → `Cap8Scheme.chipAbsorb8`;
`capLeafDigest:170` (34) → `capLeafDigest8:810`; `nodeOf:176` (47) → `nodeOf8:815`;
`recomposeUp:254` (33) → `recomposeUp8:859`; `deployedShapedChip1:1200` (10) →
`deployedShapedChip8:1146`. ⚑ **The file's own docstring at `:1190` already calls the 1-felt path
"DEBT REPORTED, NOT PROVEN AROUND".** No sibling: `EffectVmEmitCapRoot.{edgeLeafOf:222,
capAdvanceOf:226}` (35/25), `EffectVmEmitCapReshape.{capLeaf:126, capRoot:133}` (11/**621**),
`UMemCodec.{capLeafOf:172, uaddrEnc:107, rootWith:237}` (38/26/18), `CapRootBridge.capEdgeKey:84` (14).

### 3c. Light client / MMR / receipt index — and this cone already says the number out loud

`metatheory/Dregg2/Lightclient/MMR.lean`: `PTree.hashOf:109`, `bag:391` (44), `mroot:402` (**170**). ⚑ **That module's
own header self-declares "THE HONEST NUMBER: ~2^15.5 QUERIES … nothing here is `Digest8`-valued."**
`metatheory/Dregg2/Lightclient/HistoryIndex.lean`: `rleaf:179` (7), `iroot:184` (**305** — the second-widest name in
this inventory). `Circuit/RotationLayout.rotatedCommit:127` (88),
`RotatedCommitDifferential.rotatedCommit:170`, `NonOmissionAttack.rotatedCommitIdx:156` (5),
`Distributed/HistoryAggregation.{stateRoot:77 (101), turnReceipt:100, logRoot:112, chainedCommit:122,
foldedFinalRoot:243}`. **None has an 8-felt sibling.** So the whole light-client non-omission chain
is stated at 2^15.45, by its own admission — and `rotatedCommit_binds_mmr` holds **by `rfl`**
precisely because the commit absorbs `mroot` as one felt limb.

### 3d. Kernel / record / shielded / emit — no sibling, various blockers

**Kernel and record:** `StateCommit.{frameDigest:177 (138), movedDigest:184 (90), cellDigest:192 (85),
recStateCommit:200 (305)}`, `ListCommit.listDigest:31` (168), `KeyedCommit.keyedDigest:26` (19),
`Exec/FieldsMap.{tailLeaf:82 (30), fieldsRoot:98 (65)}` (**siblings exist** —
`DeployedFieldsTree.fieldsLeafDigest8:66` / `fieldsNodeOf8:71`), `Exec/RecordCommit.cellCommit:80`
(158), `CommitDifferential.effectVmCommit:98` (37), `FinBindsKernel.{CH_fin:70, p2Commit:95}`,
`FinFrameHash.RH_fin:233`, `Poseidon2Surface.{recListDigest:493 (21), turnLogDigest:498 (52)}`,
`CircuitSoundness.CommitSurface.commit:140`, `CouncilCommit.councilCommitOf:99`,
`SetFieldCommit.recSetFieldCommit:172`.

**Shielded / AIR folds:** `ShieldedOnRampPin.{noteLeaf:127 (41), rootAfterAppend:256 (9)}` — ✅
sibling `CommitmentTreeWide.{noteLeaf16:113, root:136} : Digest8`;
`CommitmentTreeAccumulator.root:91` — ✅ **a whole-module `Digest8` twin exists
(`CommitmentTreeWide.lean`, KAT-locked to the same Rust `poseidon2_tree.rs`, header claiming "no
one-felt intermediate exists")**; `StateTransitionAirSound.{stExtend:83 (15), initHash:88}`,
`AggregationAirSound.aggExtend:118` (16), `ShieldedSpendPortDischarge.Hair:111`,
`ShieldedSpendFoldReachRealized.{leafCommitOf:198, chainRoot:208}`, `TurnWitness.stepWitnessDigest:63`.

**Emit wire commits** (all **column-valued** — see §3e.2): `EffectVmFullStateRunnable.wideCommitOf:198`
(33), `…RunnableComplete.wireCommitOfRow:149` (46), `EffectVmFullStateTagsA.kernelWireCommit:249` (17),
`TagsB.cellWideCommit:78` (12), `EffectVmEmitTransferComplete.cellWireCommit:79` (24),
`EffectVmEmitRecordRoot.recordCommitOf:121` (4), `EffectVmEmitRotation{,R}.wireCommit{,R}`,
`EffectVmEmitRotationCaveat.{chainCommit:221 (88), caveatCommit:240 (147)}`,
`AttestedAutomatonEmit.autoRoot:215` (25 — its own docstring says *"ONE FELT"*),
`CommitmentTreeAppendEmit.hash4to1Real:68` (19), the six `*CapDigestNew` sites, the three
`*MembershipRefine` folds, `NoteSpendingLeafRung2.{nodeHashN:120, foldUpN:125}` (⚑ its `permOut` is
**already 8-lane** and the output is squeezed back to one), `MultiStepChainRefine.chainFold:80` (11),
`EffectVmEmitIvcStateTransitionRefine.extendAccumulatedHash:80` (11),
`EffectVmEmitEscrowRoot.leafOf:144`, `EffectVmWideCommitReduction.{wideAbsorbEnc:218, wideFullEnc:384}`
(⚠ "wide" there means wide **preimage** — the kind-D naming trap, in the wild).

**Storage / misc:** `Storage/BucketCommitment.{objectLeaf:47 (11), contentRoot:56 (12)}`,
`Storage/Deployed.{poseidon2Hash:102 (54), contentRootDeployed:121 (19)}` (**`@[extern]` FFI**),
`Verify/KeystoneAuditSystemRoots.commitDigest:82` (3), `Crypto/HashSigMerkle.{pkLeaf:49, masterKey:81}`,
`EffectCommit{,2,3,4,5,2Dual}.{touchedDigest, cellDigest, effectStateCommit*}`,
`NormalizeToShapeSound.publish:130`, `TurnCircuitCompose.authChainFold:91`.

**The 1-felt PRIMITIVES everything above rides on:**
`Poseidon2KeyedBridge.DomainSeparatedSponge.{hashAt:109, deployedHash:114}`,
`SpongeCarrierReduction.SpongeKeyed.hashAt:134`, `CommitmentBinding.deployedShapedCompress1:189` (6),
`Shielded/RealCrypto.deployedShapedSponge:490` (5),
`TurnDecodeChainLogBundleCutoverCheck.deployedTurnLogHash:202`. These are the scalar sponge itself
and are **not migrable in the same sense** — "widening" one means choosing an 8-lane squeeze, which
`Heap8Scheme.chipAbsorb8` already is.

### 3e. ⚑ Four structural blockers, four different KINDS of stuck

1. **`MapDenotationSchema.MapLeafSchema.commit` is a structure FIELD** (`:134`, codomain `ℤ`). Its
   instances are `padImtSchema` (129 refs — `Heap.lean:387` names it *"the deployed schema"*) and
   `narrowSchema` (17). **Widening a field widens every instance at once**, and drags `HeapOk`, the
   occupancy discipline and every `opensTo`/`writesTo` obligation with it. Everything in §3a routes
   through it. **The single hardest node in the inventory.**
2. **The `Emit/` wire commits are COLUMN values.** Each has a `*_forced` / `*_eq` theorem saying the
   published `state_commit` **column** equals the function. One felt is what a column *is*. Widening
   is an AIR column-layout change, not a Lean edit — the same class as `MapOp`'s
   `root : Fin 8 → EmittedExpr`, which is exactly how the map op already solved it.
3. **Byte-identity pins to Rust.** `padImtRoot` / `padImtRootE` (*"⚑ THE DEPLOYED MAP COMMITMENT"*,
   naming `relink_next_addrs`, `HeapLeaf::digest`, `CanonicalHeapTree::new`), `imtLeafHash`
   (*"arity 2 → 3"*), `CommitDifferential.effectVmCommit` (*"byte-for-byte the Rust nesting"* of
   `CellState::compute_commitment`), `Storage/Deployed.poseidon2Hash` (`@[extern]`). Several are
   `rfl`-equal to siblings (`padImtRoot` ≡ `appendOrderRoot`, `effectVmCommit` ≡ `effectVmFoldLimbs`),
   so widening one **splits a theorem that currently holds definitionally**.
4. ⚑ **The INVERSE wound.** `Emit/CarrierOctetGates.{keyCommitSpec:391, pubkeyCompress1Spec:583}`
   **take a `Digest8` and squeeze it back to one felt** for a gate column;
   `NoteSpendingLeafRung2.nodeHashN` does the same to an 8-lane `permOut`. Widening these is
   meaningless — the repair is to **delete the squeeze at the gate**, a descriptor change. Any sweep
   that mechanically "widens endpoints" will mis-handle these three.

### The structural reading

**The eight-felt tower is largely BUILT, and the deployed denotation still points at the narrow
one.** §3a's map/heap family, §3b's whole cap tree, `CommitmentTreeWide` vs
`CommitmentTreeAccumulator`, `DeployedFieldsTree` vs `Exec/FieldsMap` — four parallel towers, each
`#assert_axioms`-clean, each with the narrow twin still load-bearing. So the dominant remaining work
is **re-pointing and deleting**, not construction. That is exactly why §0's migration was one file:
`perfectRoot8` and `heapNodeOf8` were already there and already proved.

⚑ And per `docs/INJECTIVITY-FLOOR-CLASS.md` §2's measurement — *"a sibling does not drain a
ratchet"* — **every one of these parallel towers is currently additive, including the one this
commit added.** Building the wide one is the easy half; deleting the narrow one is the half that
moves a number.

---

## §4 — THE ORDERED PATH, with cost and blocker per step

Ordered on **what moves a number**, not on what is easiest. §3's structural reading is the governing
fact: the wide towers are mostly built, so almost every step below is *re-pointing and deleting*.

| step | work | size | blocked by |
|---|---|---|---|
| **1** ⚑ | **Close or refute the `MapOp.holdsAt` lane-0 seam (§1).** Either prove that `HeapOpenEmit.heapOpen_writesTo8` (or its `RotatedKernelRefinementCapFamily` consumers) discharges the 8-felt faithfulness `MapOp.holdsAt` leaves open, or state plainly that the deployed map-op denotation is 1-felt and carries a 2^15.45 bar. | one focused build | nothing — all objects exist. **The highest-value item in this file:** everything downstream is priced by whether the seam holds, and right now the answer is *unstated* |
| **2** | Root `MapOpWideDigest8` into `metatheory/Dregg2.lean`; let `#floor_ratchet` adjudicate. | one line + a root build | the root is red on other lanes' mid-edit files; needs a quiet tree |
| **3** | **`imtLeafHash8` / `imtLeafHash8Of` / `aafiLeafHashW`** — the three endpoints whose NAME says 8 and whose CODOMAIN says 1. Same family, same fix. | one file, ~111 refs combined | **no 8-felt sibling exists** at arity 17. Needs `chipAbsorb8` at that arity (it is `List ℤ → Digest8`, so this is a call, not a new chip) — the `MapOpWideDigest8` pattern transfers verbatim |
| **4** | **`CommitmentTreeAccumulator` → `CommitmentTreeWide`.** A whole-module `Digest8` twin already exists and is KAT-locked to the same Rust `poseidon2_tree.rs`. | re-point + delete | nothing structural. **The cheapest genuine win left**, because the wide module already claims *"no one-felt intermediate exists"* |
| **5** | **`DeployedCapTree`'s five 1-felt primitives** (§3b) → their in-file `…8` siblings. | 5 re-points in one file | `recomposeUp` (33) still has narrow callers. The file's own docstring already calls this debt |
| **6** | **`Exec/FieldsMap.{tailLeaf, fieldsRoot}` → `DeployedFieldsTree.{fieldsLeafDigest8, fieldsNodeOf8}`.** | one file, ~95 refs | nothing structural; sibling exists |
| **7** | Re-point `DescriptorIR2.opensTo` / `writesTo` at `opensToMerkle8` / `writesToMerkle8`. | wide | **VK epoch.** Moves `MapOp.holdsAt`, the descriptor denotation and the Rust `map_root` together. Greenfield says do it — and **say what re-emits** |
| **8** | Delete `MapOpWideKeyGate`'s ℤ family (and each narrow twin as its wide one lands). | deletion | (7). ⚑ **Do not skip.** `docs/INJECTIVITY-FLOOR-CLASS.md` §2 measured that 28 regroundings were **additive** and *"a sibling does not drain a ratchet"*. `MapOpWideDigest8` is a sibling today and stays debt until `mapRootW` dies |
| **9** | **`MapLeafSchema.commit`, the structure field (§3e.1).** | multi-session | widening a field widens `padImtSchema` and `narrowSchema` at once and drags `HeapOk` with it. Sequence **after** 3–8 so the wide leaf/root it needs already exist |
| **10** | **The light-client cone** — `mroot`, `iroot`, `rotatedCommit`, `HistoryAggregation` (§3c). | a real build, ~600 refs | no sibling anywhere; `rotatedCommit_binds_mmr` holds **by `rfl`** on the one-felt absorb, so widening splits it. ⚑ This cone's own header already concedes 2^15.5 — it is honest and unrepaired |
| **11** | The `Emit/` wire commits (§3d) — a **column-layout** change, following `MapOp`'s `root : Fin 8 → EmittedExpr` as the template. | per-descriptor | AIR width + PI count; each is a VK epoch of its own |
| **12** | ⚑ **The INVERSE wound (§3e.4)** — `CarrierOctetGates.{keyCommitSpec, pubkeyCompress1Spec}`, `NoteSpendingLeafRung2.nodeHashN`. **Delete the squeeze**, do not widen. | 3 sites | a descriptor change, not a Lean edit |
| **13** | Wire Bignum into IR-v2 (§2c) under one registered descriptor. | ≈ 2 defs + 2 lemmas + 1 descriptor | **not on the digest-widening critical path.** Sequence independently |
| — | ~~Widen the absorbed preimage further~~ | — | ⚑ **NEVER.** Zero bits, and it is proved: `romBar` does not mention the domain, and every §0 bar theorem is stated over an arbitrary finite one |

⚠ **Do not treat this as a sweep.** Four rows in §3 must NOT be widened —
`narrowLeafHash` / `halfWideLeafHash` are deliberate anti-launder counterexamples, and the three
§3e.4 sites need the opposite repair. A mechanical "widen every ℤ-valued digest" pass breaks all
seven.

### Two standing prohibitions, both paid for

1. **Never instantiate `birthday_bound` at one felt and call it a floor.**
   `narrow_bar_vacuous_at_2pow16` proves the bound is `≥ 1` there — it would be a theorem about a
   bug, dressed as a security result.
2. **Never reintroduce an injectivity floor, or a global `∀ p q, ¬ Coll` side condition, to make a
   widened proof go through.** 27 of 35 floors are refuted and the global-`¬Coll` shape is
   pigeonhole-refuted in exactly the same way. The honest shape is the per-instance residual at
   named preimages with all three poles proved — **dischargeable, satisfiable, and
   refutes-the-floor contrapositively**. `MapOpWideDigest8` §3a/§3b is the worked template, and the
   satisfiable pole is the one a hurried port drops.

---

## Appendix — where to go next

| for | read |
|---|---|
| why injectivity is width-blind, and the (a)/(b) two-move repair | `docs/INJECTIVITY-FLOOR-CLASS.md` §3 |
| the floor that is actually proved | `metatheory/Dregg2/Crypto/RomQueryFloor.lean` §5 |
| the two-move repair worked end to end at one lane | `metatheory/Dregg2/Circuit/Emit/ShieldedWideValueLinkDescriptor.lean` |
| the eight-felt towers that already exist | `metatheory/Dregg2/Circuit/MapMerkleRoot.lean` §5b · `metatheory/Dregg2/Circuit/DeployedHeapTree.lean` · `metatheory/Dregg2/Circuit/DeployedCapTree.lean` §5b · `metatheory/Dregg2/Circuit/CommitmentTreeWide.lean` · `metatheory/Dregg2/Circuit/DeployedFieldsTree.lean` |
| the migration landed here | `metatheory/Dregg2/Circuit/MapOpWideDigest8.lean` |
| the seam (deployed 8 lanes vs lane-0 denotation) | `metatheory/Dregg2/Circuit/DescriptorIR2.lean:301,577` · `circuit/src/descriptor_ir2.rs:587,1069` · `metatheory/Dregg2/Circuit/Emit/HeapOpenEmit.lean:244` |
| a cone that already concedes its own 2^15.5 | `metatheory/Dregg2/Lightclient/MMR.lean` (module header) |
| Bignum's actual role (move (a), not the hash floors) | `docs/INJECTIVITY-FLOOR-CLASS.md` §4, `docs/CENSUS-bignum-adoption-2026-07-25.md` |
