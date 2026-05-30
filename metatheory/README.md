# Metatheory — *this is dregg2*

This directory is not "the spec of dregg2." **It is dregg2**, built in Lean 4. The plan
is to build ~all of the system here — semantics, the executable kernel, the security
proofs — and keep in Rust only the *rustful things*: raw cryptographic primitives,
transport/IO, the IDE/agent extension, bots, web. The architecture mirrors **l4v**
(seL4's proof): an Abstract Spec of laws, an executable Design Spec, and a refinement
tying them — with a **portal** interface (`CryptoKernel`/`World`) where Rust plugs in.

Toolchain `leanprover/lean4:v4.30.0`; mathlib via a local `path` require to `~/src/mathlib4`
(rev `1c2b90b…`). **It builds:** `lake build` ⇒ ~28 modules, ~2900 jobs, 0 errors,
~21 `sorry` (all of which are *honest* — see "What the sorries mean" below). Style:
spec-first, grind up — but most of it is now proved, and the executable layer is
`sorry`-free and `#eval`-able.

## The layer cake (l4v mapping)

### Abstract Spec — the laws (`l4v spec/abstract` + `proof/access-control`/`infoflow`)
- **`Core`** — the symmetric-monoidal category of cells/turns; **conservation (Law 1)** as
  a monoid-valued measure over any `AddCommMonoid` (multi-asset/fractional/debt), one law
  `count B = count A + (minted − burned)`; the corollaries `conservation_ordinary`/
  `mint_delta`/`burn_delta` **proved** from the single balance obligation.
- **`Resource`** — the **resource-algebra (Iris camera) tier**: `ResourceAlgebra`
  (partial CM + `valid` + `core` with the three core laws), `Fpu` (frame-preserving
  update = the general conservation law). `ℕ` & `Excl` cameras + NFT non-duplication +
  the `Auth` (authoritative↔fragment) camera **proved**. At this tier conservation and
  authority are *one law*.
- **`StepCamera`** — the step-indexed (full Iris) camera for higher-order resources;
  `discrete_camera_of_RA` proved.
- **`Laws`** — `Predicate ⊣ Witness` Galois connection (a real polarity adjunction,
  proved) + the verify/find seam (`Verify` decidable oracle / `find` opaque plugin).
- **`Authority/Positional`** — the **l4v integrity lift**: caps, `pas_refined`
  (authority ⊆ caps), the `Integrity` intra/cross case-split, `boundary_law` /
  `confinement_preserved` / `lossy_attenuation_only` **proved** (faithful hypotheses).
- **`Confluence`** — **I-confluence (the 3rd judgement)**: tier-1 eligibility; non-triviality
  proved (`top_iconfluent` / `cardLeOne_not_iconfluent`).
- **`Boundary`** — coinductive soundness over the live-codata cell (`νF`). The real,
  PROVED keystone is **`stepComplete_preserves`**: step-completeness ⇒ a safety invariant
  holds along the whole execution (via `Execution.invariant_run`). (`Sound`/`IsBisim` are
  the *behavioural-equivalence* notion; the earlier bisimulation "keystones" were found
  false-as-stated and retired — `bisim_eq`/`sound_refl` are their honest residue.)
- **`Finality`** — judgement 2: the 4-tier finality lattice, `tau_unified`, cross-tier
  join, `no_downgrade` (run-monotonicity, proved).
- **`JointTurn`** — the **cross-cell ⊗** (the load-bearing multi-cell layer): the CG-2
  turn-id pullback ⊗ CG-5 conservation aggregate as the `JointBinding` *hypothesis*;
  `joint_sound` **proved** as joint-execution invariant-preservation; `binding_is_proper`
  (the corrected irreducibility — the binding is a proper equalizer subobject).
- **`Privacy`**, **`Coordination`** + **`Projection`** (MPST choreography / cand-D
  front-end), **`Await`** (effects + one-shot continuations), **`Liveness`** (GC laws +
  proved impossibilities), **`Upgrade`** (anti-brick `set_program`).

### The portals — the Lean⟷Rust contract
- **`CryptoKernel`** — crypto ops (`hash`/`verify`/`commit`/`nullifier`) + their laws, as
  an *uninterpreted interface*. PROVING uses an abstract `[CryptoKernel …]` (parametric);
  RUNNING uses a Rust instance via `@[extern]` FFI. Instantiates `Laws.Verifiable` (the
  portal *is* the verify oracle) and **closes the cross-vat integrity bridge**
  (`cross_vat_via_verify`). A lawful `Reference` kernel is included (Lean-as-host).
- **`World`** — the sibling portal for nondeterministic external inputs (network/clock/
  randomness) that consensus needs; quorum finality over it (`quorum_monotone`,
  `world_no_downgrade` proved; Byzantine quorum-intersection / post-GST liveness are the
  honest opens).
- **`PrivacyKernel`** — privacy realized over the portal: Pedersen `committed_conservation`
  + nullifier anti-double-spend, **proved relative to the interface laws** (`commit_hom`).

### Executable Design Spec — the machine (`l4v spec/design`), `sorry`-free + `#eval`-able
- **`Exec/Kernel`** — `exec : KernelState → Turn → Option KernelState`, fail-closed,
  checking authority + conservation; `exec_conserves` / `exec_authorized` /
  `kernel_run_conserves` proved.
- **`Exec/Caps`** — grant/attenuate/derive/revoke/invoke + attenuation/no-amplify proved;
  the integrity bridge.
- **`Exec/Generators`** — `execMint`/`execBurn` with the delta laws.
- **`Exec/Unified`** — ONE `KernelOp` + `step` with unified conservation (`step_delta`)
  and the ledger equation `total = initial + minted − burned`.
- **`Foundation`**: `Execution` (configurations/runs/`invariant_run` — the userspace-program
  layer) and `Tactics`.

### Refinement (`l4v proof/refine`) + protocols
- **`Proof/Refine`** — `Exec ⊑ Abstract`: conservation + integrity-intra refinement proved.
- **`Protocol/Transfer`** — two-cell atomic transfer + payment channel (`channel_run_conserves`).
- **`Protocol/Workflow`** — an authenticated, capability-gated, attested multi-party
  workflow ("DocuSign for authenticated workflows"): every guarantee a theorem, runs under
  `#eval`.

## What the `sorry`s mean (the key for real formal verification)

They sort into exactly two honest buckets — *no gaps masquerade as proofs*:
1. **Interface obligations** — the `CryptoKernel`/`World` laws and `conservation_step`:
   discharged by Rust + the ZK circuits, *by design* never in Lean (the §8 boundary).
2. **Genuine open theorems** — the deepest coinductive/joint ones, plus the Byzantine
   quorum-intersection and post-GST liveness (they need the adversary/GST model).

"Finish the metatheory" = drive bucket (2) to zero and pin bucket (1) as the audited
interface; then the executable kernel + refinement = an end-to-end verified system.

## §8 — crypto-soundness is the portal's job, never Lean's
The cryptographic soundness/extractability of `verify`/`commit`/`hash` is a circuit
obligation, stated as `CryptoKernel` *laws* (assumed in Lean, discharged by Rust+circuits).
Lean treats `verify` as a decidable oracle. This is a boundary, not a gap.

## Building
`lake build` (needs `~/src/mathlib4` @ the pinned rev). For one file during concurrent
work, `lake env lean Metatheory/<Module>.lean` (race-free; does not rebuild the world).
Do NOT rename this top-level directory — the working session is anchored to it; reorganize
*contents* (the `Spec/Abstract` reshuffle is planned) instead.
