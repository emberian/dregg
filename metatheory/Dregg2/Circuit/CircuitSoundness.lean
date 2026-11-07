/-
# Dregg2.Circuit.CircuitSoundness — the APEX light-client unfoolability theorem.

This module is the **architectural backbone** of dregg's circuit-soundness story: it states, as a
green Lean skeleton, the exact shape a verifying light client gets for free, and it carries the
genuine remaining obligations as EXPLICIT hypotheses / typeclasses — never as an open hole, `:= True`,
or a silent default.

## The target (what soundness means)

A light client verifies a rotated batch proof against the live VK and runs NOTHING else. Soundness:

  `verifyBatch vk pi π = accept  ⟹  ∃ a genuine kernel transition  s ⟶ s'  with
                                     pi.pre = stateCommit s  ∧  pi.post = stateCommit s'`.

The "genuine kernel transition" is the proved declarative kernel `ActionDispatch.fullActionStep`
(`⟺ execFullA` by `fullActionStep_exec_iff`), composed over a turn by `turnSpec`
(`⟺ execFullTurnA` by `execFullTurnA_iff_turnSpec`). The live circuit is `Satisfied2 hash d …` over
`EffectVmDescriptor2`, with descriptors drawn from the v3 registry
(`EffectVmEmitRotationV3.v3Registry`). The whole point of THIS module is to connect `Satisfied2` to
`turnSpec fullActionStep` faithfully.

## The three pieces (the prompt's mandate)

1. `StateDecode` — the FAITHFUL witness→kernel-state decode. It says the witness's PUBLISHED pre/post
   commitments equal `recStateCommit` of the kernel states they bind, over a fixed commitment surface
   (`CommitSurface`), and that those kernels are `AccountsWF`. Faithfulness is NOT assumed: it is a
   THEOREM (`stateDecode_pre_faithful` / `stateDecode_post_faithful`) — two states decoding the SAME
   published commitment have EQUAL kernels, by `recStateCommit_binds_kernel` (the named Poseidon CR
   set + the PROVED-preserved `AccountsWF`). It assumes NO kernel admissibility (no authority, no
   frame): the decode pins the kernel from the commitment alone.

   The cross-cell / cross-step FRAME is NOT a free field. A `StateDecodeChain` decodes a whole turn
   step-by-step, each step publishing its old/new commitment; `stateDecodeChain_frame_continuous`
   DERIVES that consecutive kernels coincide (`postᵢ = preᵢ₊₁`) from the published-commitment binding,
   so the frame is a CONSEQUENCE of the commitments, not an assumption.

2. `descriptorRefines d kstep` — the per-effect rung each effect discharges: any `Satisfied2` witness
   of descriptor `d` whose published commitments decode to `pre`/`post` forces `kstep pre post`. This
   is the genuine obligation per effect; this module CARRIES it (the registry-wide version is a
   hypothesis of the apex), it does not fake it.

3. `lightclient_unfoolable` — the apex. From a verifying batch (`verifyBatch vk pi π = accept`), the VK
   bound to the live registry (`vk = vkOfRegistry liveRegistry`), the named STARK-batch soundness
   carrier `[StarkSound]`, the named hash CR carrier `[Poseidon2SpongeCR]`, and the carried per-effect
   obligation, conclude a genuine kernel turn whose endpoints are the published commitments.

## Carried obligations ledger (every named-and-deferred premise; nothing laundered)

  * `[StarkSound vk pi π]` — the audited p3 batch-STARK soundness: `verifyBatch vk pi π = accept`
    yields, for the descriptor named in `pi`, a `Satisfied2` witness `t` whose published PI agree with
    `pi`. This is a REALIZABLE crypto/audit obligation (the FRI/p3 verify⟹∃witness extraction) that
    cannot be proved in Lean; it is introduced HERE as a clean named class, not assumed silently. The
    minimal honest interface (`StarkSound`, `verifyBatch`, `accept`, `vkOfRegistry`) is DEFINED in
    this module because none existed.

  * `[Poseidon2SpongeCR hash]` — Poseidon2-sponge collision-resistance (the existing carrier from
    `Poseidon2Binding`). The faithfulness of the decode rides on it (via `wireCommitR_binds` /
    `recStateCommit_binds_kernel`). REALIZABLE.

  * ⚰ the `CommitSurface` CR fields (`compressInjective cmb/compress`, `compressNInjective
    compressN`, `cellLeafInjective CH`) — GONE 2026-08-01. They were listed here as "REALIZABLE;
    bundled, not free"; they are not realizable, they are REFUTED at deployed BabyBear width by
    pigeonhole, and the bundle that carried them had no deployed inhabitant. The binding they
    justified is now `CommitSurface.commit_binds_of_noColl`, whose residual names the argument pairs
    instead of assuming there is none. The surviving field is `restFrame : RestHashIffFrameFin RH`,
    which IS satisfiable.

  * `hrefines : ∀ e, descriptorRefines (liveRegistry e) (fullActionStep-arm e)` — the per-effect
    refinement, CARRIED as an apex hypothesis. This is the rung the rest of the campaign discharges
    (one effect at a time) into `lightclient_unfoolable`. It is the genuine remaining work, named.

  * `WitnessDecodes hash R S pi` — the WITNESS→KERNEL-STATE EXISTENCE rung. A light client has only
    `(pi, π)`; it cannot supply `pre`/`post`. The hard fact is that the witness's published
    commitments are commitments of REAL well-formed kernel states — i.e. that SOME `pre`/`post` exist
    decoding `pi.toPublished`. This is the genuine surjectivity/realizability of the commitment surface
    on the published values a verifying witness pins; it CANNOT be proved by assuming the conclusion,
    so it is CARRIED explicitly (exactly like `StarkSound`), and the apex DERIVES the decode from it
    rather than hypothesizing a free `pre`/`post`/`hdecode`. REALIZABLE (every accepted trace's
    published roots ARE `recStateCommit` of the kernels the prover committed); named, not faked.

DERIVED (NOT carried — proved here from the above): the frame continuity over a chain
(`stateDecodeChain_frame_continuous`, in REDUCTION FORM since 2026-08-01) and the apex composition
shape. The decode's faithfulness moved out: `stateDecode_*_faithful` are DELETED (they rode the
vacuous `commit_binds`); their floor-free twins are
`StateCommitReduce.stateDecode_pre/post_faithful_orBreak`.
-/
import Dregg2.Circuit.StateCommit
import Dregg2.Circuit.RestFrameFin
import Dregg2.Circuit.StateCommitReduceRaw
import Dregg2.Circuit.LogCommitRegrounded
import Dregg2.Circuit.ActionDispatch
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.FriVerifier
import Dregg2.Circuit.FriTranscriptBind
import Dregg2.Circuit.ExtFieldChallenge

namespace Dregg2.Circuit.CircuitSoundness

open Dregg2.Circuit
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 VmTrace Satisfied2)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.StateCommit
  (recStateCommit recStateCommit_binds_kernel AccountsWF
   compressInjective compressNInjective cellLeafInjective RestHashIffFrame logHashInjective)
open Dregg2.Circuit.RestFrameFin (FiniteRepresentable RestHashIffFrameFin)
open Dregg2.Circuit.CollisionReduce (OrBreak)
open Dregg2.Circuit.ActionDispatch
  (fullActionStep turnSpec execFullTurnA_iff_turnSpec actionTag)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (FullActionA execFullTurnA)

/-- The kernel boundary turn the full-state commitment is taken at (`recStateCommit`'s `Turn`). -/
abbrev BoundaryTurn := Dregg2.Exec.Turn

/-! ## §1 — the commitment surface (the genuine Poseidon CR carrier, bundled).

`CommitSurface` packages the five abstract commitment primitives `recStateCommit` is parametric in
(`CH RH cmb compress compressN`) together with the STANDARD Poseidon collision-resistance facts the
full-state-root binding needs. These are SECTION PARAMETERS in `StateCommit`, never axioms; bundling
them lets the apex carry "the surface is collision-resistant" as ONE named hypothesis. Each field is
REALIZABLE by a real Poseidon. -/

/-- A commitment surface for the full kernel state: the five primitives `recStateCommit` runs over,
plus the finite-support rest-frame obligation.

⚰ **FOUR INJECTIVITY FIELDS DELETED 2026-08-01** — `cmbInj : compressInjective cmb`,
`compInj : compressInjective compress`, `compNInj : compressNInjective compressN`,
`leafInj : cellLeafInjective CH`. Each asserts that a COMPRESSING map into ONE BabyBear felt is
injective, which pigeonhole REFUTES at deployed parameters
(`Verify.ApexPremiseVacuity.apexCommitFloorSansRest_false_at_babyBear`) — so no deployed surface ever inhabited the bundle and
EVERYTHING quantified over `S : CommitSurface` and conditioned on them was VACUOUSLY TRUE.

The only consumers that read them AS INJECTIVITY were `CommitSurface.commit_binds` (deleted; use
`commit_binds_of_noColl`), `StateCommitReduce.surface_no_stateBreak` (deleted with its two dependents),
and `FinInjectivityCollapse.injectivity_collapses_to_poseidon2CR` (retired — its target
`Poseidon2SpongeCR` is refuted at the same width). Every other mention was a CONSTRUCTOR filling
them.

⛑ THE BINDER SURFACE FOLLOWED, 2026-08-02. Deleting these fields left `ClosureSurface.S_live` with
four `_`-prefixed parameters ITS BODY IGNORED, so ~150 declarations were inapplicable at deployed
parameters and every binder that only existed to feed them are DELETED. The "one place a proof
genuinely READ one" (the setProgram rung) was recorded that day and is FALSE — the rung passed the
hypothesis to a lemma whose body never used it, `RotatedKernelRefinementProgram` having shed it on
2026-07-30 — so the `ClosureReadouts.hNProgram` field it was parked in is deleted too (2026-08-03).
All four were inert at every site. See `Verify.ClosureSurfaceApplicable` for the closed surface that
buys, and `Dregg2/Circuit/ClosureSurface.lean`'s `S_live` for the measurement.

⚠ The surviving `restFrame` field is the finite-support successor `RestHashIffFrameFin`, which IS
satisfiable — at the UNBOUNDED reference sponge, and NOT at deployed BabyBear width, where the same
pigeonhole that killed the four kills it too
(`Verify.RestFrameFiniteSupportSuccessor.restHashIffFrameFin_false_babyBear`, 2026-08-02). So this
structure still has no deployed inhabitant, and — because its body is `Iff`-headed and
`#floor_ratchet`'s floor derivation requires an injectivity SHAPE — NO GATE SAYS SO. See its own doc
below. -/
structure CommitSurface where
  /-- the per-cell leaf hash. -/
  CH        : CellId → Value → ℤ
  /-- the rest hash over the non-`cell` components. -/
  RH        : RecordKernelState → ℤ
  /-- the root combiner (cell-digest ⊕ rest-hash). -/
  cmb       : ℤ → ℤ → ℤ
  /-- the Merkle 2-to-1 node hash. -/
  compress  : ℤ → ℤ → ℤ
  /-- the sponge over a leaf list. -/
  compressN : List ℤ → ℤ
  /-- the rest hash is injective on the framed non-`cell` components OF FINITELY-SUPPORTED STATES.

  ⚑ **This field was `RestHashIffFrame RH` until 2026-07-31, and that made the whole bundle
  UNINHABITED AT EVERY PARAMETER** (`RestFrameCardinalityFloor.restHashIffFrame_false_by_cardinality`
  refutes it for every `RH` by Cantor on `bal : CellId → AssetId → ℤ`), so every theorem quantifying
  over a `CommitSurface` was vacuous and could not even be given a refutability pole. The
  finite-support successor `RestFrameFin.RestHashIffFrameFin` restricts the biconditional to the
  `denote`-image of `FinKernelState` and IS satisfiable — see
  a closed inhabitant of this whole structure. ⚑ CORRECTED: this cited
  `Circuit.CommitSurfaceInhabited.refCommitSurface`, WHICH DOES NOT EXIST — no such module, no such
  declaration. The real inhabitant is the deliberately ANONYMOUS `noncomputable example :
  CommitSurface` at `Verify/RestFrameFiniteSupportSuccessor.lean:348`, left unnamed on purpose
  because naming it mints a `bundle-user` carrier in the floor ratchet (that file's §6). -/
  restFrame   : RestHashIffFrameFin RH

/-- The full-state commitment of a kernel under a surface, at a turn `t`. -/
def CommitSurface.commit (S : CommitSurface) (k : RecordKernelState) (t : Turn) : ℤ :=
  recStateCommit S.CH S.RH S.cmb S.compress S.compressN k t

/-! ### The faithfulness engine, in REDUCTION FORM.

⚰ **`CommitSurface.commit_binds` is DELETED (2026-08-01).** It said: two `AccountsWF`,
finitely-representable kernels whose surface commitments agree at the same turn are EQUAL. It proved
that by feeding `recStateCommit_binds_kernel` the four injectivity FIELDS
`S.cmbInj`/`S.compInj`/`S.compNInj`/`S.leafInj` — every one of which is FALSE at deployed
parameters, because injectivity of a compressing map into ONE BabyBear felt is refuted by pigeonhole
(`Verify.ApexPremiseVacuity.apexCommitFloorSansRest_false_at_babyBear`). So the theorem, and everything conditioned on it, was
VACUOUSLY TRUE; the four fields are deleted from the structure in the same commit.

⚰ **`CommitSurface.commit_binds_orBreak` IS ALSO DELETED (2026-08-01, same day, second pass).** It
was the first replacement: `OrBreak S.StateBreak (k = k')` — the kernels are equal, OR the adversary
exhibited a collision of one of `S`'s four hash carriers. It consumed no injectivity, so it was TRUE
at the deployed hash — and that is all it was. `S.StateBreak`'s first disjunct is
`SpongeCollision S.compressN`, a GLOBAL existential, and
`SpongeCollisionShirk.spongeCollision_of_fieldBounded` supplies it at ANY sponge landing in a BabyBear
felt. So the break branch held UNCONDITIONALLY at deployed parameters, the dichotomy was literally
`True` (`StateCommitReduce.orBreak_stateBreakP_iff_True`, stated over an ARBITRARY good branch), and
the good branch carried nothing. The same pigeonhole that REFUTES the injectivity floor ESTABLISHES
the break: the first pass traded vacuous-by-false-hypothesis for vacuous-by-free-disjunct.

`commit_binds_of_noColl` below is the replacement that discriminates. It carries the per-instance
residual `S.CommitColl k k' t` — the four-way collision event stated at the SPECIFIC argument pairs
the extraction visits, never as `∃ two colliding inputs` — which is SATISFIABLE at an honest hash,
REFUTABLE at a broken one, and NOT PROVABLE
(`StateCommitLeafRegrounded.noRecStateCommitColl_diag` / `recStateCommitColl_refutable` /
`noRecStateCommitColl_not_provable`). `StateCommitReduce.perInstance_sharper_than_stateBreakP` is the
separation: at ONE AND THE SAME deployed-shaped sponge the disjunctive form holds with good branch
`False` while the per-instance residual is genuinely refuted at the honest pair.

⚠ Do NOT reintroduce a `¬ S.StateBreak`-hypothesised twin either. `¬ StateBreak S` is false at
deployed width for exactly the pigeonhole reason the four fields are, so hypothesising it is the same
vacuity under a third name — which is why `StateCommitReduce.commit_binds_of_no_stateBreak` was
deleted alongside. The per-instance residual is NOT that: it names a pair. -/

/-- **The state-commit apex break at a surface's carriers**: a concrete collision of `S`'s sponge,
root combiner, node hash, or cell-leaf hash — the four commitment primitives `recStateCommit` runs
over. Definitionally the raw `StateCommitReduce.StateBreakP` at `S`'s carriers.

⚑ Defined HERE, not in `StateCommitReduce` where it lived until 2026-08-01. This module's OWN
bindings (`stateDecodeChain_frame_continuous`, the turn-chain seam teeth) have to state their break
disjunct, and `StateCommitReduce` sits ABOVE this module in the import order. The raw layers moved
DOWN to `StateCommitReduceRaw` for the same reason. -/
def CommitSurface.StateBreak (S : CommitSurface) : Prop :=
  StateCommitReduce.StateBreakP S.CH S.cmb S.compress S.compressN

/-- `StateBreak` is the raw break at the surface's carriers (definitional). -/
theorem CommitSurface.stateBreak_eq_raw (S : CommitSurface) :
    S.StateBreak = StateCommitReduce.StateBreakP S.CH S.cmb S.compress S.compressN := rfl

/-- **⚑⚑ THE SHIRK, AT THE SURFACE — why `commit_binds_orBreak` is gone.** At any deployed-shaped
(field-bounded) sponge, `OrBreak S.StateBreak P` holds for EVERY proposition `P`, by the break branch
alone. So the deleted `commit_binds_orBreak` was satisfied without its conclusion being satisfiable at
all. Cite this, not a doc-comment, when a lane offers an `OrBreak S.StateBreak` re-grounding.

`StateBreak` itself is KEPT: it is the raw break's surface view, out-of-scope threadings
(`HistoryAggregation`, `RecursiveAggregation`, `CommitFaithfulRegrounded`) still state their
conclusions over it, and a refuted def with a visible in-tree refutation is a tombstone with teeth. -/
theorem CommitSurface.orBreak_stateBreak_trivial (S : CommitSurface)
    (hb : SpongeCollisionShirk.FieldBounded S.compressN) (P : Prop) :
    OrBreak S.StateBreak P :=
  StateCommitReduce.orBreak_stateBreakP_trivial S.CH S.cmb S.compress S.compressN hb P

/-- The shirk as an equivalence: the dichotomy is literally `True` at every deployed-shaped surface. -/
theorem CommitSurface.orBreak_stateBreak_iff_True (S : CommitSurface)
    (hb : SpongeCollisionShirk.FieldBounded S.compressN) (P : Prop) :
    OrBreak S.StateBreak P ↔ True :=
  StateCommitReduce.orBreak_stateBreakP_iff_True S.CH S.cmb S.compress S.compressN hb P

/-- **`S.CommitColl k k' t` — THE PER-INSTANCE COMMITMENT RESIDUAL.** A collision of one of `S`'s four
commitment primitives AT THE SPECIFIC ARGUMENT PAIRS the whole-kernel extraction visits: the root
combiner at `((cellDigest k t, RH k), (cellDigest k' t, RH k'))`, the node hash at the frame/moved
children, the frame sponge at the two ordered leaf lists, the cell leaf at a named `(cell, v, w)`.

⚑ NOT an existential over all pairs. That distinction is the whole repair: `∃ two colliding inputs` is
supplied by pigeonhole at deployed width and discriminates nothing, while a claim about NAMED points
is refutable at a broken hash and satisfiable at an honest one. Definitionally
`StateCommitLeafRegrounded.RecStateCommitColl` at `S`'s carriers, whose three-check teeth
(`noRecStateCommitColl_diag`, `recStateCommitColl_refutable`, `noRecStateCommitColl_not_provable`)
apply verbatim. -/
def CommitSurface.CommitColl (S : CommitSurface) (k k' : RecordKernelState)
    (t : Dregg2.Exec.Turn) : Prop :=
  StateCommitLeafRegrounded.RecStateCommitColl S.CH S.RH S.cmb S.compress S.compressN k k' t

/-- `CommitColl` is the raw named-pair residual at the surface's carriers (definitional). -/
theorem CommitSurface.commitColl_eq_raw (S : CommitSurface) (k k' : RecordKernelState)
    (t : Dregg2.Exec.Turn) :
    S.CommitColl k k' t
      = StateCommitLeafRegrounded.RecStateCommitColl S.CH S.RH S.cmb S.compress S.compressN k k' t :=
  rfl

/-- **★ THE FAITHFULNESS ENGINE (floor-free, UNCONDITIONAL).** Two kernels whose surface commitments
AGREE (at the same turn), both `AccountsWF` and both FINITELY REPRESENTABLE, are EQUAL — OR the NAMED
residual `S.CommitColl` holds at the exact argument pairs the extraction visits. No hypothesis on
`S`'s hashes at all, so unlike both of its predecessors this holds at deployed parameters AND
discriminates: `StateCommitReduce.recStateCommit_binds_kernel_unconditional_false` shows the residual
is load-bearing. -/
theorem CommitSurface.commit_binds_or_collides (S : CommitSurface) (k k' : RecordKernelState)
    (t : Dregg2.Exec.Turn)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hfin : FiniteRepresentable k) (hfin' : FiniteRepresentable k')
    (h : S.commit k t = S.commit k' t) :
    k = k' ∨ S.CommitColl k k' t :=
  StateCommitReduce.recStateCommit_binds_kernel_or_collidesFin S.CH S.cmb S.compress S.compressN
    S.RH S.restFrame k k' t hwf hwf' hfin hfin' h

/-- **★ THE S3 FORM — the published commitment BINDS the kernel.** The SAME conclusion the deleted
`commit_binds` drew, from a per-instance, refutable side condition instead of four refuted
injectivity fields (pass 1) or a free disjunct (pass 2). NO authority gate, NO frame assumption, NO
injectivity carrier.

⚑ `hfin`/`hfin'` (2026-07-31) sit exactly where `hwf`/`hwf'` already sat — a per-call structural
obligation, never a field of the bundle (a bundle of FUNCTIONS has no business quantifying over
STATES). ⚠ `RestFrameFin.not_finiteRepresentable_of_lifecycle_ne_zero` exhibits an `AccountsWF`
kernel OUTSIDE the domain, so the restriction is real. Whether every EXECUTOR-REACHED kernel is
inside it is `FinKernelState.denote_surjective_on_reachable`, still gated on the per-effect commuting
square `hpres`, undischarged for every effect today. -/
theorem CommitSurface.commit_binds_of_noColl (S : CommitSurface) (k k' : RecordKernelState)
    (t : Dregg2.Exec.Turn)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hfin : FiniteRepresentable k) (hfin' : FiniteRepresentable k')
    (hno : ¬ S.CommitColl k k' t)
    (h : S.commit k t = S.commit k' t) :
    k = k' :=
  (S.commit_binds_or_collides k k' t hwf hwf' hfin hfin' h).resolve_right hno

/-- **⚑ THE RESIDUAL FIRES AT THE HONEST PAIR, FOR EVERY SURFACE.** On the diagonal every disjunct of
`CommitColl` demands an argument-pair DISEQUALITY that is `rfl`-refuted, so the side condition holds
with NO hypothesis on `S`'s hashes — the ported binding genuinely applies at deployed parameters. This
is the separation the global-existential form provably cannot express
(`orBreak_stateBreak_iff_True`). -/
theorem CommitSurface.noCommitColl_diag (S : CommitSurface) (k : RecordKernelState)
    (t : Dregg2.Exec.Turn) : ¬ S.CommitColl k k t :=
  StateCommitLeafRegrounded.noRecStateCommitColl_diag S.CH S.RH S.cmb S.compress S.compressN k t

/-- **⚑⚑ THE SEPARATION AT THE SURFACE — the port is not a relabeling.** At ONE AND THE SAME
deployed-shaped surface: the deleted form's dichotomy holds with the good branch `False` (it says
nothing), while the per-instance residual is genuinely refuted at the honest pair (it says
something). -/
theorem CommitSurface.perInstance_sharper_than_orBreak (S : CommitSurface)
    (hb : SpongeCollisionShirk.FieldBounded S.compressN) (k : RecordKernelState)
    (t : Dregg2.Exec.Turn) :
    OrBreak S.StateBreak False ∧ ¬ S.CommitColl k k t :=
  ⟨S.orBreak_stateBreak_trivial hb False, S.noCommitColl_diag k t⟩

/-! **THE UNIFORM BRIDGE — no strength lost, and NO new declaration for it.** The four deleted
injectivity fields, had they been inhabitable, would have killed every `CommitColl` disjunct at every
pair. So each theorem re-grounded on `¬ S.CommitColl` is IMPLIED BY its pre-deletion form: the port is
strictly STRONGER, conclusions unchanged.

⚑ Deliberately NO local `_of_carriers` twin at the surface. `S.CommitColl k k' t` is DEFINITIONALLY
`RecStateCommitColl S.CH S.RH S.cmb S.compress S.compressN k k' t`, so the tree's landed bridge
`StateCommitLeafRegrounded.noRecStateCommitColl_of_carriers hCmb hCompress hCompressN hLeaf` already
has exactly the type `¬ S.CommitColl k k' t` and a not-yet-ported consumer re-points through ONE
application of it. Minting a surface-level restatement would be a BRAND-NEW declaration taking four
refuted floors as hypotheses — a fresh `#floor_ratchet` carrier — for zero content. Reusing the
universal bridge lands this port at a net carrier DECREASE, which is the point of the exercise. -/

/-! ## §2 — `StateDecode`: the FAITHFUL witness→kernel-state decode.

`StateDecode S t pre post` says: the published OLD commitment (`pubPre`) equals the surface commitment
of `pre.kernel`, the published NEW commitment (`pubPost`) equals that of `post.kernel`, both kernels
are `AccountsWF`, and `pre`/`post` carry the turn the commitment is taken at. It DERIVES the kernel
from the commitment via `CommitSurface.commit` — it does NOT assume any kernel admissibility.

`pubPre`/`pubPost` are the witness's PUBLISHED public-input commitments (in the rotated layout, the PI
slots `d.piCount` / `d.piCount + 1` that `EffectVmEmitRotationV3.rotV3_publishes` pins to the row's
chained `wireCommitR` commit; `rotV3_binds_published` makes those PI BIND the decoded limbs under
`Poseidon2SpongeCR`). Here we keep the published commitment ABSTRACT (a single `ℤ` per boundary) — the
faithfulness we prove is exactly that the published commitment determines the kernel; the
limb-level decode (`wireCommitR`/`rotV3_binds_published`) is the per-descriptor bridge that supplies
`pubPre`/`pubPost`, carried by `descriptorRefines`. -/

/-- The published-commitment view of one circuit witness: the OLD and NEW state commitments the trace
publishes (the rotated PI slots), at the turn the commitment is parameterized by. -/
structure PublishedCommit where
  /-- the published OLD (pre) state commitment (rotated PI slot `d.piCount`). -/
  pubPre  : ℤ
  /-- the published NEW (post) state commitment (rotated PI slot `d.piCount + 1`). -/
  pubPost : ℤ
  /-- the turn the commitment is taken at (the boundary turn binding `recStateCommit`). -/
  turn    : BoundaryTurn

/-- A `PublishedCommit` is inhabited (a default boundary). Only used to let the abstract readout
`tracePublishedCommit` be `opaque` (which needs `Nonempty` of its codomain); carries no content. -/
instance : Inhabited PublishedCommit := ⟨⟨0, 0, ⟨0, 0, 0, 0⟩⟩⟩

/-- **`StateDecode`** — the faithful decode of a published commitment to its bound kernel states.

`pre`/`post` are the kernel states the published OLD/NEW commitments bind. Faithfulness is the THEOREM
`stateDecode_pre_faithful`/`stateDecode_post_faithful` below — it is NOT assumed here. No authority, no
frame: the decode pins the kernel from the commitment alone (via `CommitSurface.commit_binds`). -/
structure StateDecode (S : CommitSurface) (pc : PublishedCommit)
    (pre post : RecChainedState) : Prop where
  /-- the published OLD commitment IS the surface commitment of `pre.kernel`. -/
  preBinds  : pc.pubPre = S.commit pre.kernel pc.turn
  /-- the published NEW commitment IS the surface commitment of `post.kernel`. -/
  postBinds : pc.pubPost = S.commit post.kernel pc.turn
  /-- `pre`'s kernel is structurally well-formed (the binding's structural side-condition; PROVED
      preserved by the executor, `recKExec_preserves_AccountsWF` — not a crypto assumption). -/
  preWF     : AccountsWF pre.kernel
  /-- `post`'s kernel is structurally well-formed. -/
  postWF    : AccountsWF post.kernel

/-! ### ⚰ TOMBSTONE — `stateDecode_pre_faithful` / `stateDecode_post_faithful` (DELETED 2026-08-01).

They said: two pre-states (resp. post-states) decoding the SAME published commitment have EQUAL
kernels — the UNIQUENESS half of the decode. Both were one application of
`CommitSurface.commit_binds`, hence conditioned on the four refuted injectivity fields, hence
VACUOUSLY TRUE at deployed parameters (see the tombstone above `CommitSurface.StateBreak`).

CONSUME INSTEAD: `StateCommitReduce.stateDecode_pre_faithful_of_noColl` /
`stateDecode_post_faithful_of_noColl` — the same conclusion, from a per-instance residual at the two
named kernels. (Their `_orBreak` predecessors were themselves vacuous — the break disjunct is free at
deployed width — and are gone too.)

(EXISTENCE of a real transition behind an accepted proof is a separate and floor-free result —
`ApexFloorFree.lightclient_unfoolable_free`. Uniqueness is what these two were about.) -/

/-! ## §3 — `descriptorRefines`: the per-effect rung.

For a descriptor `d` and a candidate kernel step relation `kstep`, `descriptorRefines d kstep` says:
ANY `Satisfied2` witness of `d` whose published commitments (`pc`) decode (via a faithful
`StateDecode`) to `pre`/`post` FORCES `kstep pre post`. This is the obligation each effect discharges
(its `Satisfied2` denotation entails its `fullActionStep` arm); the apex carries the registry-wide
family of these. The hash, surface, and memory boundary (`minit`/`mfin`/`maddrs`) are quantified — a
witness under ANY boundary that publishes commitments decoding to `pre`/`post` must induce the step. -/

/-- **`descriptorRefines d kstep`** — the per-effect refinement obligation: every `Satisfied2` witness
of `d` whose published commitments decode to `pre`/`post` forces `kstep pre post`.

⚑⚑ **THE FLOOR IS IN THE BODY, AND IT IS DEAD. MEASURED 2026-08-01, NOT PORTED.**

The body opens `Poseidon2SpongeCR hash → …` — a floor `HashFloorHonesty.poseidon2SpongeCR_false_babyBear`
PROVES FALSE at deployed BabyBear (infinite `List ℤ` into ~2³¹ values, pigeonhole). Because it sits in the
VALUE and not the signature, **no floor binder appears anywhere in the type of any theorem that mentions
this def**, and every binder-keyed ruler reads those theorems as clean. `DescriptorRefinesShirkRefuted`
proves the consequence outright: `descriptorRefines S hash d (fun _ _ => False)` HOLDS at every
field-bounded sponge. A refinement obligation discharged at an unsatisfiable `kstep` constrains the
circuit in no way at all.

**What the previous version of this docblock claimed, and what is actually true.** It said the antecedent
is "GENUINE — exactly what each effect's discharge needs", citing
`EffectVmEmitRotationV3.rotV3_binds_published`. Measured over the whole tree: `rotV3_binds_published` is
APPLIED NOWHERE — its only non-comment occurrences are its own `theorem` line, its `#assert_axioms`, and a
`FloorRatchetBaseline` row. And not one in-tree discharge of `descriptorRefines` READS the antecedent:

  * `ClosureAll.effectDecodeBridge_of_closedLogExtract` — the funnel every closed-path producer goes
    through (`hrefinesAllClosed` → `ClosureForest.hrefines_forest_closed` → `descriptorRefines_complete`
    and its 31-tag census) — opens `intro _hCR …` and never mentions it again;
  * `WitnessRealizing.descriptorRefines_trivial` drops it;
  * `RotatedKernelRefinementFacetTurnBound.descriptorRefinesTB_to_descriptorRefines` only FORWARDED it
    into `descriptorRefinesTB`, whose body opened with the same dead antecedent — ⚰ BOTH DELETED
    2026-08-02 (tombstone at §6 of that file), which REMOVES this def's last in-tree consumer of the
    antecedent rather than weakening the measurement: the lowering is gone precisely because forwarding a
    live `hCR` into a dead antecedent is plumbing with no reader at either end;
  * the only genuine reads are inside the refuted twin (`DescriptorRefinesReduce.descriptorRefines_of_R`)
    and the refutations themselves.

So the honest replacement here is a **DELETION**, not a re-grounding — the identical finding that carried
the two landed 2026-07-25 prop-body ports (`ClosureAll.ClosedLogExtract`,
`CircuitCompleteness.descriptorComplete`; see `FloorCensus.portedPropBody`). Deleting the antecedent is
strictly STRENGTHENING and needs no bridge lemma.

⚠ **DO NOT re-ground this one on `¬ SpongeColl` at a named pair.** The per-instance residual
(`SpongeCollisionShirk.SpongeColl`, bridge `noSpongeColl_of_spongeCR`) is the right target for a site that
FEEDS the floor a specific pair of lists. This def feeds it nothing. Manufacturing a pair here would mint a
side condition no proof consumes — decoration, and a fresh carrier. Equally, do NOT port onto
`DescriptorRefinesReduce.descriptorRefinesR`: it is `↔`-equivalent to this def
(`descriptorRefinesR_iff_refines`) and provably just as vacuous
(`DescriptorRefinesShirkRefuted.descriptorRefinesR_vacuous_babyBear`).

**The target already exists and already passes the acceptance test:**
`ApexFloorFree.descriptorRefinesFree` — no antecedent, `CommitMap` in place of the (separately refuted)
`CommitSurface` bundle, publication link carried — and
`ApexFloorFree.descriptorRefinesFree_false_at_False_kstep` REFUTES it at `fun _ _ => False`, which is the
falsifier this def and its twin both fail.

**BLAST RADIUS, MEASURED (241 exact-word mentions, 39 files).** 156 are inside comments and carry nothing.
Of the 85 in code: 2 are the census/baseline pins, 4 are `open` lines, and 29 are `hrefines`-family
HYPOTHESIS binders — and every one of those 29 consumers ALSO binds `hCR : Poseidon2SpongeCR hash`
explicitly, so the consumer half of the surface is already visible to a binder-keyed census and is not
what this class hides. The silent carriers are the ~21 PRODUCERS (statements that CONCLUDE it with no
floor binder), plus two prop-body aliases that inherit the hiding — `CircuitSoundnessAssembled.EffectDecodeBridge`
(`:= descriptorRefines …`) and the `WitnessRealizing.LeafRefinement.refines` structure FIELD.

**WHY IT IS NOT PORTED HERE, and what the port costs.** The port is one edit to this body plus ~6 producer
proofs; it is NOT a 241-site change. What couples it into a single indivisible commit is the instrument:

  1. `FloorCensus.sentinelPropBody = [descriptorRefines]` and `FloorRatchet` gate (d) BOTH fail closed if
     this def stops being discovered as a prop-body carrier. The port must move the name into
     `FloorCensus.portedPropBody` in the SAME commit, or the whole tree goes red.
  2. `DescriptorRefinesShirkRefuted`'s four refutations become UNPROVABLE the moment the antecedent goes —
     that is the port succeeding, but a falsity theorem may not simply vanish; it has to be retired to a
     tombstone in the same commit, with the acceptance test re-pointed at `descriptorRefinesFree`.
  3. Each of the 29 consumers drops an argument at its `hrefines e hCR …` application sites, and sheds
     `hCR` where nothing else in the proof reads it.

None of the three is a reason to keep the antecedent; they are the work order.

⚑ **RE-MEASURED 2026-08-01 (second pass). The blast-radius numbers hold; two claims around them do
not.** Exact-word count over `metatheory/`, comments AND string literals stripped mechanically:
**245 mentions, 84 in CODE, 161 in comments, 38 files.** The 84 code sites account exactly:

  * **29** `hrefines`-family HYPOTHESIS binders — and checked one at a time, **29/29 also bind
    `hCR : Poseidon2SpongeCR hash` explicitly**. (The one that reads as an exception to a
    line-local grep, `Metatheory.Adversary.Schema.circuitDynamics`, is a `noncomputable def` and
    binds it four lines above its `hrefines`.) The consumer half is visible; it is not the hole.
  * **32** in `DescriptorRefinesComplete` — but that is TWO declarations: the alias `def`, and the
    single `descriptorRefines_census`, whose statement is one 31-way conjunction.
  * **4** `open` lines, **1** `FloorCensus.sentinelPropBody` row, **1** this def, **17** producers
    and equations — of which 4 are `DescriptorRefinesShirkRefuted`'s deliberate refutations and 1 is
    `DescriptorRefinesReduce.descriptorRefines_constHash_vacuous`.

**THE ALIAS CHAIN IS THREE DEEP, NOT TWO, AND THE THIRD CARRIES THE CAPSTONES.** Where a grep for
this def's name goes blind:

  * `CircuitSoundnessAssembled.EffectDecodeBridge` — 7 code sites, 4 files.
  * `DescriptorRefinesComplete.DescriptorRefinesComplete`
    (`def … : Prop := ∀ e, descriptorRefines …`) — 12 code sites, 4 files. Not named above until now.
  * `WitnessRealizing.LeafRefinement`, through its `refines` FIELD: reached as
    `Nonempty (LeafRefinement …)` at **18 code sites in 4 files**, including
    `AssuranceCaseGrounded.deployed_system_secure_grounded{,_v2}`,
    `grounded_capstone_engine_fires{,_v2}`, and six `GroundedApex` theorems.

At none of those 37 sites does the word `descriptorRefines` occur.

⚠ **"NO INSTRUMENT CAN SEE IT" IS FALSE, and stating it that way is how a real finding gets
over-read.** `#floor_ratchet`'s `Surface` carries `propBody` and `bundles` as a JOINT FIXPOINT
(`Verify/FloorRatchet.lean:669-670`), and every one of the 24 declarations across this chain that
was probed — this def, `EffectDecodeBridge`, `DescriptorRefinesComplete`, `LeafRefinement`,
`rejectLeaf`, `leafStep_of_refinement`, `leafSound_of_refinements`, `engineSound_of_refinements`,
three `GroundedApex` theorems, `AssuranceCaseGrounded.deployed_system_secure_grounded`, plus
`descriptorRefinesTB` and `Market.ProtocolAssurance.ShieldedRingDescriptorRefines` — is ALREADY a
grandfathered row in `FloorRatchetBaseline`. The ratchet SEES this class and PERMITS it. What the
prop-body placement hides is the declaration's TYPE: `#print`, `#check`, a human reader, and an
`#assert_axioms` audit all see a clean signature. Two different failures; only the second is this
def's, and the fix for the first is a shorter baseline, not a new instrument.

⚠ **"the (separately refuted) `CommitSurface` bundle" IS STALE — as of `1f53df6d2`, TODAY.**
`ApexPremiseVacuity.ApexCommitFloor` is the five-conjunct list `compressInjective cmb ∧
compressInjective compress ∧ compressNInjective compressN ∧ cellLeafInjective CH ∧
RestHashIffFrame RH`, and `apexCommitFloor_unsatisfiable` kills it through the FIFTH conjunct, by
Cantor. `CommitSurface` at HEAD has NONE of those five as fields — the four injectivity ones are
deleted (§1's tombstone) and the fifth is `RestHashIffFrameFin RH` — and it has a CLOSED inhabitant,
the anonymous `noncomputable example : CommitSurface` at
`Verify/RestFrameFiniteSupportSuccessor.lean:348`. So `(S : CommitSurface) → ¬ P S` is no longer
free and a refutability pole AT THE BUNDLE is stateable for the first time.

That does not make `ApexFloorFree.CommitMap` unnecessary; it changes the REASON, and the old reason
is about to be copied into two more files. `descriptorRefinesFree_false_at_False_kstep` needs a
commit map that HITS the opaque published value `tracePublishedCommit emptyTrace` — that is what
`ApexFloorFree.collapseMap` is for. `S.commit` is `recStateCommit` of `S`'s five primitives and
cannot be chosen to hit an opaque target. **The move to `CommitMap` is because the map must be
ARBITRARY, not because the bundle is empty.**

⚑ **AND THE TOOTH MAY NOT BE A NAMED THEOREM.** A declaration whose TYPE mentions `CommitSurface`
is a `#floor_ratchet` `bundle-user` carrier and the gate hard-errors on a new one; the established
discipline for a reference-pole object is an ANONYMOUS `example`
(`Verify/RestFrameFiniteSupportSuccessor.lean` §6, `TurnDecodeChainLogBundleCutoverCheck` §1/§5).
Whether `CommitSurface` is still computed into `Surface.bundles` after the drain is a question only
a root `#floor_ratchet` run answers, and the root cannot elaborate today — that run is step 0 of the
port, not an assumption of it.

**SMALLEST FIRST STEP, and it is not this def.** `FloorCensus.sentinelPropBody` is
`[descriptorRefines]` and nothing else, so porting THIS def requires editing `FloorCensus.lean` in
the same commit — which the vacuity-campaign lanes are forbidden to touch, so it needs the operator,
and it is the first work item rather than a reason to stop. The other two prop-body carriers were in
no sentinel list and could land alone: `RotatedKernelRefinementFacetTurnBound.descriptorRefinesTB`
(3 live code sites) and `Market.ProtocolAssurance.ShieldedRingDescriptorRefines` (5). Baseline rows
blocked neither — `FloorRatchetBaseline` is emitted as `baseline ∩ current` and its only healthy
direction is shorter, so a row left stale by a port is green.

⚑ **BOTH OF THOSE TWO ARE NOW DELETED (2026-08-02).** They were retired onto
`RotatedKernelRefinementFacetTurnBound.descriptorRefinesTBKernelFree` and
`Market.ProtocolAssurance.ShieldedRingDescriptorRefinesKernel` — floor-free, `CommitMap`-stated,
publication-link-carrying, conclusions weakened to their kernel-endpoint halves with the receipt-chain
clause named as a per-instance residual (`FacetLogResidual`, `ShieldedRingLogResidual`). Tombstones sit
at their former definition sites. Of the three prop-body carriers this docblock named, THIS def is the
one still standing, and it is the one whose port needs the `FloorCensus.lean` edit above. ⚠ The route was
DELETION and not `FloorCensus.portedPropBody`: that ratchet requires the ported name to STILL RESOLVE, so
a retired-and-deleted def must not be added to it. Whether any prop-body carrier this docblock did not
name survives is a question only a root `#floor_ratchet`/census run answers. -/
def descriptorRefines (S : CommitSurface) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor2) (kstep : RecChainedState → RecChainedState → Prop) : Prop :=
  Poseidon2SpongeCR hash →
  ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pc : PublishedCommit) (pre post : RecChainedState),
    Satisfied2 hash d minit mfin maddrs t →
    StateDecode S pc pre post →
    kstep pre post

/-! ## §4 — `StateDecodeChain`: decode a whole turn; the FRAME is DERIVED.

A turn is a list of actions; the circuit witnesses it as a list of per-step circuit witnesses, each
publishing its own OLD/NEW commitment. `StateDecodeChain` decodes the whole turn:

  * `pre₀` is the turn pre-state;
  * each step `i` has a witness with a faithful `StateDecode` to `(sᵢ, sᵢ₊₁)`;
  * the published NEW commitment of step `i` and the published OLD commitment of step `i+1` AGREE
    (the prover's chained-root column — `foldStepRoots` in `TurnCircuitCompose`).

The cross-step FRAME (that the post-state of one step IS the pre-state of the next) is then a
THEOREM, not an assumption: equal published commitments + faithfulness force `sᵢ₊₁.kernel = sᵢ₊₁.kernel`
across the seam. We state the per-seam continuity as `stateDecodeChain_frame_continuous`. -/

/-- A decoded turn step: the action, its descriptor, the published commitment, and the faithful
decode of that commitment to the step's `(pre, post)` kernels. -/
structure DecodedStep (S : CommitSurface) where
  /-- the kernel action this step runs. -/
  action  : FullActionA
  /-- the descriptor (from the live registry) the step's circuit witnesses. -/
  descr   : EffectVmDescriptor2
  /-- the published commitment view of the step's circuit witness. -/
  pc      : PublishedCommit
  /-- the step's pre/post chained states. -/
  pre     : RecChainedState
  /-- the step's post chained state. -/
  post    : RecChainedState
  /-- the faithful decode of `pc` to `(pre, post)`. -/
  decode  : StateDecode S pc pre post

/-- **`NoSeamCommitColl S steps` — the per-adjacency commitment residual, chained.** At EVERY seam of
a decoded chain, `S`'s commitment primitives do not collide at the NAMED argument pairs the seam's
extraction visits. The kernel-side twin of `NoLogSeamColl` (§8's 2026-07-25 log cutover), with the
same `List.IsChain` shape so the two fold together.

⚑ One named pair per seam, never `∃ two colliding inputs`: a global collision existential is supplied
by pigeonhole at deployed BabyBear width and would make the whole condition vacuous
(`StateCommitReduce.orBreak_stateBreakP_iff_True`). -/
def NoSeamCommitColl (S : CommitSurface) (steps : List (DecodedStep S)) : Prop :=
  List.IsChain (fun a b => ¬ S.CommitColl a.post.kernel b.pre.kernel b.pc.turn) steps

/-- **The uniform lift.** A non-equivocation claim holding at EVERY pair of kernels gives the
per-adjacency side condition on any decoded chain. This is the one step between the landed bridge
`CommitSurface.noCommitColl_of_carriers` (the four deleted injectivity fields kill every residual) and
`NoSeamCommitColl`, so the pre-deletion statements are recovered by a single composition WITHOUT
minting a new declaration on a refuted floor. -/
theorem noSeamCommitColl_of_forall {S : CommitSurface} {steps : List (DecodedStep S)}
    (h : ∀ (k k' : RecordKernelState) (t : Dregg2.Exec.Turn), ¬ S.CommitColl k k' t) :
    NoSeamCommitColl S steps := by
  rw [NoSeamCommitColl, List.isChain_iff_getElem]
  exact fun i _ => h _ _ _

/-- **Cross-step frame continuity is DERIVED, not assumed.** If two adjacent decoded steps publish the
SAME boundary commitment (`a.pc.pubPost = b.pc.pubPre`) at the same turn, and the post of `a` / the
pre of `b` are `AccountsWF`, then their kernels COINCIDE — the frame at the seam is forced by the
commitment binding, not a free hypothesis.

(The shared boundary commitment is the prover's chained-root column; equating it across the seam is
the `foldStepRoots` glue from `TurnCircuitCompose`. The `turn`-equality is the boundary-turn agreement
the layout pins.)

⚑ **NARROWED 2026-07-31**: the seam kernels must be FINITELY REPRESENTABLE (`hfin`/`hfin'`). The
frame is still DERIVED and not assumed; it is derived on a smaller class of states.

⚑ **EXTRACTOR FORM 2026-08-01 (second pass).** The conclusion is UNCONDITIONAL again, and the crypto
reliance is the explicit per-instance `hno`. The first pass wrapped the conclusion in
`OrBreak S.StateBreak`, which is `True` at every deployed-shaped surface
(`CommitSurface.orBreak_stateBreak_iff_True`) — so that form asserted nothing about the seam. `hno` is
a claim about the ONE pair of kernels at THIS seam, refutable at a broken hash and satisfiable at an
honest one. A prover who publishes a seam commitment disagreeing with the threaded kernel is rejected
unless the deployed hash collides at exactly those named points. -/
theorem stateDecodeChain_frame_continuous (S : CommitSurface) (a b : DecodedStep S)
    (hfin : FiniteRepresentable a.post.kernel) (hfin' : FiniteRepresentable b.pre.kernel)
    (hturn : a.pc.turn = b.pc.turn)
    (hseam : a.pc.pubPost = b.pc.pubPre)
    (hno : ¬ S.CommitColl a.post.kernel b.pre.kernel b.pc.turn) :
    a.post.kernel = b.pre.kernel := by
  have ha : a.pc.pubPost = S.commit a.post.kernel a.pc.turn := a.decode.postBinds
  have hb : b.pc.pubPre = S.commit b.pre.kernel b.pc.turn := b.decode.preBinds
  have : S.commit a.post.kernel a.pc.turn = S.commit b.pre.kernel b.pc.turn := by
    rw [← ha, ← hb, hseam]
  rw [hturn] at this
  exact S.commit_binds_of_noColl a.post.kernel b.pre.kernel b.pc.turn a.decode.postWF
    b.decode.preWF hfin hfin' hno this

/-! ## §5 — the minimal honest STARK-batch interface.

None of `VerifyKey`, `verifyBatch`, `vkOfRegistry`, or the STARK-batch soundness existed. We define
the minimal HONEST interface here and SAY SO:

  * `VerifyKey` — an opaque verifying key (the committed registry the verifier is pinned to).
  * `vkOfRegistry` — the VK↔registry binding: the live registry's commitment IS the VK.
  * `BatchPublicInputs` — the public inputs a batch proof exposes: the descriptor name/effect index it
    claims, the published OLD/NEW commitments (= `pi.pre`/`pi.post`), and the boundary turn.
  * `Accept` — the verdict; `verifyBatch vk pi π` is `accept` exactly when the proof checks.
  * `StarkSound` — the AUDITED p3 batch-STARK soundness, as a named class: a verifying batch yields a
    `Satisfied2` witness of the CLAIMED descriptor whose published PI AGREE with `pi`. This is the FRI
    extraction obligation; REALIZABLE, audited, NOT provable in Lean — carried as a class, not faked.

`liveRegistry` is the effect→descriptor map; we keep it abstract (a function `EffectIdx →
EffectVmDescriptor2`) so the apex is parametric in it — the concrete binding to
`EffectVmEmitRotationV3.v3Registry` is a registry-lookup wrapper a downstream instance supplies. -/

/-- An effect index (the dispatcher's `actionTag` lives here). -/
abbrev EffectIdx := Nat

/-- The live effect→descriptor registry (abstract; the concrete instance is the v3 registry lookup). -/
abbrev Registry := EffectIdx → EffectVmDescriptor2

/-- An opaque verifying key — the committed object the light client is pinned to. -/
structure VerifyKey where
  /-- the registry commitment the VK certifies (kept structural; equality is what the apex needs). -/
  registryDigest : ℤ
deriving DecidableEq

/-- A registry-commitment hash (abstract surface digest of the whole registry). -/
opaque registryCommit : Registry → ℤ

/-- **The VK↔registry binding.** The VK of a registry commits exactly to that registry. -/
def vkOfRegistry (R : Registry) : VerifyKey := ⟨registryCommit R⟩

/-- The public inputs a batch proof exposes to the light client. -/
structure BatchPublicInputs where
  /-- the effect index (which registry descriptor the batch claims). -/
  effect : EffectIdx
  /-- the published pre-state commitment. -/
  pre    : ℤ
  /-- the published post-state commitment. -/
  post   : ℤ
  /-- the boundary turn the commitments are taken at. -/
  turn   : BoundaryTurn

/-- The verifier verdict. -/
inductive Verdict where
  | accept
  | reject
deriving DecidableEq, Inhabited

open Verdict

/-- A batch proof object (interface stub; its bytes are irrelevant to the apex — only the verifier
verdict and the `StarkSound` extraction matter). -/
structure BatchProof where
  /-- the opaque proof bytes (unconstrained — the apex reasons only via the verdict). -/
  bytes : List ℤ := []

/-! ### The deployed verifier configuration (the honest KAT floor).

`verifyBatch` is no longer a fully-opaque function: it runs the specified batch-STARK verifier plus
the quartic-extension FRI fold at a fixed deployed configuration. Everything ABOVE this floor
(continued transcript derivation, query/beta binding, full-lane p3 fold, rejection teeth,
`wrap_sound`) is concrete Lean. The configuration constants below are the residue that is
NOT proved: the deployed p3 verifier's fixed knobs (Poseidon2 permutation `cfgPerm`, sponge `cfgRATE`,
index extraction `cfgToNat`, FRI parameters `cfgParams`, the baked recursion-VK shape `cfgVk`, the
base/extension arithmetic and hashing leaves, the challenger init state `cfgInitState`, the
log-domain size `cfgLogN`), and the byte-deserialization views `cfgView`/`cfgExtView` (proof/PI bytes → the structured
`BatchProofData`/`WrapPublics` the verifier walks), and the residual non-FRI checks `cfgExtra`. They
are left UNSPECIFIED (`opaque`) and are validated by the differential KAT corpus against the deployed
p3 verifier — the validation-tier floor, the same status as Poseidon2 bit-exactness. -/

instance : Inhabited FriVerifier.FriParams :=
  ⟨{ logBlowup := 0, numQueries := 0, powBits := 0, maxLogArity := 0,
     logFinalPolyLen := 0, extDeg := 0 }⟩

instance : Inhabited (FriVerifier.RecursionVk ℤ) :=
  ⟨{ shapeMatches := fun _ => false }⟩

instance : Inhabited (FriVerifier.FriChecks ℤ) :=
  ⟨{ foldConsistent := fun _ _ _ => false, merklePaths := fun _ _ => false,
     batchTables := fun _ _ => false, queryPow := fun _ => false }⟩

instance : Inhabited (FriVerifier.BatchProofData ℤ) :=
  ⟨{ traceCommit := [], friCommitments := [], finalPoly := [], queries := [],
     exposedSegment := [] }⟩

instance : Inhabited (FriVerifier.WrapPublics ℤ) :=
  ⟨{ segment := [] }⟩

instance : Inhabited (FriVerifier.FriCore ℤ) :=
  ⟨{ compress := fun _ _ => [], foldCombine := fun _ _ _ _ => 0 }⟩

instance : Inhabited (FriVerifier.FieldArith ℤ) :=
  ⟨{ add := fun _ _ => 0, mul := fun _ _ => 0, pow := fun _ _ => 0, zero := 0, one := 0 }⟩

instance : Inhabited (Dregg2.Circuit.ExtFieldChallenge.ExtFriArith ℤ) :=
  ⟨{ base := default, neg := fun _ => 0, half := 0 }⟩

instance : Inhabited (Dregg2.Circuit.ExtFieldChallenge.ExtFriCore ℤ) :=
  ⟨{ compress := fun _ _ => [], leafHash := fun _ _ => [],
     domainPoint := fun _ _ => ⟨[]⟩, domainPointInv := fun _ _ => ⟨[]⟩ }⟩

instance : Inhabited (Dregg2.Circuit.ExtFieldChallenge.ExtVerifierView ℤ) :=
  ⟨{ queries := [], singleAirOpenings := [] }⟩

/-- Deployed config: the Poseidon2 permutation the challenger sponges with. KAT-validated. -/
opaque cfgPerm : List ℤ → List ℤ
/-- Deployed config: the sponge rate. KAT-validated. -/
opaque cfgRATE : Nat
/-- Deployed config: field-element → query-index bit extraction. KAT-validated. -/
opaque cfgToNat : ℤ → Nat
/-- Deployed config: the FRI parameters (the deployed knobs are `ir2LeafWrapConfig`). KAT-validated. -/
opaque cfgParams : FriVerifier.FriParams
/-- Deployed config: the baked recursion-VK shape pin. KAT-validated. -/
opaque cfgVk : FriVerifier.RecursionVk ℤ
/-- Deployed config: the legacy scalar-restriction FRI ops. KAT-validated. -/
opaque cfgCore : FriVerifier.FriCore Int
/-- Deployed config: the field-arithmetic op bundle the batch-table check runs over. KAT-validated. -/
opaque cfgA : FriVerifier.FieldArith Int
/-- Deployed config: Poseidon2 leaf/node hashing and the two-adic domain-point tables used
by the extension-valued FRI walk.  The walk around these leaves is concrete in Lean. -/
opaque cfgExtCore : Dregg2.Circuit.ExtFieldChallenge.ExtFriCore Int
/-- Deployed config: BabyBear negation and `1/2`, used by the concrete p3 interpolation
formula.  Its `2 * half = 1` law is checked on every accepting extension fold. -/
opaque cfgExtA : Dregg2.Circuit.ExtFieldChallenge.ExtFriArith Int
/-- The deployed BabyBear quartic binomial residue.  The verifier checks its canonical
projection is `11` before accepting. -/
opaque cfgExtW : Int
/-- Deployed config: the arithmetic per-query check bundle — the SPECIFIED `fullChecks` at the
opaque deployed core/arith ops (no longer an opaque record itself). KAT-validated at the leaves. -/
@[reducible] def cfgChecks : FriVerifier.FriChecks Int :=
  FriVerifier.fullChecks cfgCore cfgA cfgToNat cfgParams.powBits
/-- Deployed config: the challenger's initial sponge state. KAT-validated. -/
opaque cfgInitState : List ℤ
/-- Deployed config: the proof's log-domain size (from the VK shape / degree bits). KAT-validated. -/
opaque cfgLogN : Nat
/-- Deployed config: byte-deserialization of `(pi, π)` into the structured proof data and carried
publics `verifyAlgo` walks. KAT-validated. -/
opaque cfgView : BatchPublicInputs → BatchProof → (FriVerifier.BatchProofData ℤ × FriVerifier.WrapPublics ℤ)
/-- Reconstruct only the serialized extension-valued rows/Merkle data and the AIR-evaluated
OOD values from the same deployed proof.  Query indices, betas, α, ζ, domain points,
vanishing, and inverses are NOT supplied by this KAT view: the concrete verifier derives
them from the continued transcript/domain arithmetic. -/
opaque cfgExtView : BatchPublicInputs → BatchProof →
  Dregg2.Circuit.ExtFieldChallenge.ExtVerifierView Int
/-- Deployed config: the residual non-FRI checks of the deployed verifier. KAT-validated. -/
opaque cfgExtra : FriVerifier.BatchProofData ℤ → FriVerifier.WrapPublics ℤ → Bool

/-- **The one key the deployed configuration was validated for.** The `cfg*` constants above are
ONE configuration — one AIR evaluation (`cfgExtView`), one recursion-VK shape pin (`cfgVk`) — KAT-
validated against the deployed p3 verifier for ONE registry. Nothing in them is a function of a
registry, so the only honest way for `verifyBatch` to consult its key is to check that the key IS
this one. Which registry `cfgKey` commits to is the same KAT-tier fact as the rest of the
configuration: not provable here, and not assumed by any theorem in this module. -/
opaque cfgKey : VerifyKey := ⟨0⟩

/-- The batch verifier: the continued-thread verifier strengthened with the faithful
single-AIR quotient identity AND the quartic-extension p3 fold, run at the deployed
configuration, and ONLY for the key that configuration was validated for (`cfgKey`). The apex
consumes the real RLC/chunk-recomposition/inverse teeth and full four-lane FRI arithmetic; the
scalar fold is retained only as a redundant soundness-refinement conjunct.

The key is consulted: under any key other than `cfgKey` the verdict is `reject`
(`verifyBatch_rejects_foreign_key`), so `verifyBatch (vkOfRegistry R) pi π = accept` genuinely
depends on `R` — it forces `vkOfRegistry R = cfgKey` (`verifyBatch_accept_iff`). An earlier
revision bound the key as `_vk` and never read it, so `StarkSound hash R`'s hypothesis was the
same proposition for every registry while its conclusion named `R pi.effect`. -/
def verifyBatch (vk : VerifyKey) (pi : BatchPublicInputs) (π : BatchProof) : Verdict :=
  if vk = cfgKey ∧
      (Dregg2.Circuit.ExtFieldChallenge.verifyAlgoUnifiedFaithfulExt
        cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA cfgExtCore cfgExtA cfgExtW
        cfgInitState cfgLogN (cfgView pi π).1 (cfgView pi π).2 (cfgExtView pi π)
      && cfgExtra (cfgView pi π).1 (cfgView pi π).2) = true then Verdict.accept else Verdict.reject

/-- **Acceptance, unfolded.** `verifyBatch vk pi π` accepts exactly when `vk` is the deployed key
AND the deployed configuration accepts. The single unfolding lemma every consumer uses. -/
theorem verifyBatch_accept_iff (vk : VerifyKey) (pi : BatchPublicInputs) (π : BatchProof) :
    verifyBatch vk pi π = Verdict.accept ↔
      vk = cfgKey ∧
        (Dregg2.Circuit.ExtFieldChallenge.verifyAlgoUnifiedFaithfulExt
          cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA cfgExtCore cfgExtA cfgExtW
          cfgInitState cfgLogN (cfgView pi π).1 (cfgView pi π).2 (cfgExtView pi π)
        && cfgExtra (cfgView pi π).1 (cfgView pi π).2) = true := by
  unfold verifyBatch
  split
  · exact iff_of_true rfl ‹_›
  · exact iff_of_false (by decide) ‹_›

/-- **The key is consulted (refuting pole of key-independence).** Under any key other than the
deployed one, `verifyBatch` rejects every batch. -/
theorem verifyBatch_rejects_foreign_key {vk : VerifyKey} (hvk : vk ≠ cfgKey)
    (pi : BatchPublicInputs) (π : BatchProof) : verifyBatch vk pi π = Verdict.reject := by
  unfold verifyBatch
  rw [if_neg (fun h => hvk h.1)]

/-- **At the deployed key the verdict is the configuration's (satisfiable pole).** `verifyBatch`
under `cfgKey` accepts exactly the batches the deployed configuration accepts, so the key check
removes nothing at the key the configuration belongs to. -/
theorem verifyBatch_cfgKey_accept_iff (pi : BatchPublicInputs) (π : BatchProof) :
    verifyBatch cfgKey pi π = Verdict.accept ↔
        (Dregg2.Circuit.ExtFieldChallenge.verifyAlgoUnifiedFaithfulExt
          cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA cfgExtCore cfgExtA cfgExtW
          cfgInitState cfgLogN (cfgView pi π).1 (cfgView pi π).2 (cfgExtView pi π)
        && cfgExtra (cfgView pi π).1 (cfgView pi π).2) = true := by
  rw [verifyBatch_accept_iff]
  exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

/-- **The verdict separates keys.** Whenever the deployed configuration accepts a batch, the
deployed key and any other key receive DIFFERENT verdicts on it: `verifyBatch` is not constant in
its key argument on any accepted input. -/
theorem verifyBatch_separates_keys {vk : VerifyKey} (hvk : vk ≠ cfgKey)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hcfg : verifyBatch cfgKey pi π = Verdict.accept) :
    verifyBatch vk pi π ≠ verifyBatch cfgKey pi π := by
  rw [verifyBatch_rejects_foreign_key hvk, hcfg]
  decide

/-- The published-commitment view induced by a `BatchPublicInputs`. -/
def BatchPublicInputs.toPublished (pi : BatchPublicInputs) : PublishedCommit :=
  ⟨pi.pre, pi.post, pi.turn⟩

/-- **The published-commitment readout of a circuit witness.** A `VmTrace` exposes its rotated PI
slots `d.piCount` / `d.piCount + 1` (the chained `wireCommitR` old/new state commitments) and the
boundary turn. We keep this readout ABSTRACT here (a single `PublishedCommit` per trace) — exactly as
`verifyBatch` is opaque — because the limb-level readout (`EffectVmEmitRotationV3.rotV3_publishes`) is
the per-descriptor bridge. The `StarkSound` extraction below pins this readout to `pi.toPublished`, so
the witness `t` it returns genuinely publishes the light client's public inputs (not merely SOME
commitments). -/
opaque tracePublishedCommit : VmTrace → PublishedCommit

@[simp] theorem BatchPublicInputs.toPublished_pubPre (pi : BatchPublicInputs) :
    pi.toPublished.pubPre = pi.pre := rfl
@[simp] theorem BatchPublicInputs.toPublished_pubPost (pi : BatchPublicInputs) :
    pi.toPublished.pubPost = pi.post := rfl
@[simp] theorem BatchPublicInputs.toPublished_turn (pi : BatchPublicInputs) :
    pi.toPublished.turn = pi.turn := rfl

/-- **`StarkSound` — the audited p3 batch-STARK soundness carrier (NAMED, not faked).**

A verifying batch against the live registry's VK yields, for the descriptor the PI names
(`R pi.effect`), a `Satisfied2` witness `t` (over SOME boundary) whose published OLD/NEW commitments
are EXACTLY `pi.pre`/`pi.post`, at the turn `pi.turn` (i.e. `pi.toPublished`). This is the FRI/p3
verify⟹∃witness extraction: REALIZABLE and audited, but NOT provable in Lean — introduced as a clean
class so the apex carries it explicitly instead of assuming it silently.

The hypothesis depends on `R` through its key: `verifyBatch (vkOfRegistry R)` accepts only when
`vkOfRegistry R = cfgKey`. So the class is contentless for a registry the deployed configuration
was not validated for (`starkSound_of_foreign_key`) and is exactly the extraction over the
configuration's accept set at the deployed key (`starkSound_iff_at_cfgKey`). -/
class StarkSound (hash : List ℤ → ℤ) (R : Registry) : Prop where
  extract : ∀ (pi : BatchPublicInputs) (π : BatchProof),
    verifyBatch (vkOfRegistry R) pi π = accept →
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash (R pi.effect) minit mfin maddrs t ∧
        tracePublishedCommit t = pi.toPublished

/-- **`StarkSound` has content only at the deployed key.** For a registry whose key is NOT the
deployed one, the verifier rejects everything under that key, so the extraction is owed for no
batch and the class holds with no content. This is the honest floor of a one-configuration
verifier: one deployed configuration, one VK. -/
theorem starkSound_of_foreign_key (hash : List ℤ → ℤ) (R : Registry)
    (hR : vkOfRegistry R ≠ cfgKey) : StarkSound hash R where
  extract := fun pi π hacc => by
    rw [verifyBatch_rejects_foreign_key hR] at hacc
    exact absurd hacc (by decide)

/-- **At the deployed key, `StarkSound` is exactly the extraction over the configuration's
accept set.** For a registry committed by `cfgKey`, `StarkSound hash R` holds iff every batch the
deployed configuration accepts has a `Satisfied2` witness of `R pi.effect` publishing `pi` — the
real obligation, now visibly indexed by `R` through its key. -/
theorem starkSound_iff_at_cfgKey (hash : List ℤ → ℤ) (R : Registry)
    (hR : vkOfRegistry R = cfgKey) :
    StarkSound hash R ↔
      ∀ (pi : BatchPublicInputs) (π : BatchProof),
        verifyBatch cfgKey pi π = accept →
        ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
          Satisfied2 hash (R pi.effect) minit mfin maddrs t ∧
            tracePublishedCommit t = pi.toPublished := by
  constructor
  · intro h pi π hacc
    exact h.extract pi π (by rw [hR]; exact hacc)
  · intro h
    exact ⟨fun pi π hacc => h pi π (by rw [hR] at hacc; exact hacc)⟩

/-! ## §6 — the apex: `lightclient_unfoolable`.

The apex's ONLY data inputs are what a light client actually has: the public inputs `pi` and the proof
`π`. It does NOT take `pre`/`post` or a `StateDecode` as hypotheses — those would HIDE the hardest rung
(that the published commitments are commits of REAL kernel states), turning the theorem into a
conditional refinement rather than unfoolability. Instead the apex DERIVES the decode, from named
floors only, and CONCLUDES the existence of a genuine kernel boundary.

The floors:
  * `[StarkSound hash R]` — a verifying batch yields a `Satisfied2` witness of the CLAIMED descriptor
    whose published commitments ARE `pi.toPublished` (the strengthened extraction).
  * `Poseidon2SpongeCR hash` + the `CommitSurface` CR fields — the decode's faithfulness floor.
  * `hrefines` — the per-effect refinement rung (`Satisfied2 + StateDecode ⟹ kstep`).
  * `WitnessDecodes hash R S pi` — the NEW carried obligation: a witness publishing `pi` decodes to
    SOME `(pre, post)`. This is the genuinely-hard witness→kernel-state EXISTENCE rung; carried, not
    proved-by-assuming-the-conclusion.

Derivation chain: STARK extracts a witness `t` with `tracePublishedCommit t = pi.toPublished` →
`WitnessDecodes` produces `pre`/`post` with `StateDecode S pi.toPublished pre post` → `hrefines` turns
the witness + decode into `kstep pi.effect pre post` → the decode's binding re-exports `pi.pre`/`pi.post`
as the genuine endpoint commitments. The result is the honest headline: `(pi, π)` + named floors ⟹
∃ a real kernel transition committing to `pi`. The light client RAN NOTHING.

### SCOPE — what this apex proves, and what it does NOT (the freshness boundary).

`lightclient_unfoolable` proves **SINGLE-TRANSITION soundness**: every accepted batch decodes to a
GENUINE kernel step `pre ⟶ post` committing to `pi.pre`/`pi.post`. It takes `pi.turn` as a GIVEN.
It establishes NOTHING about whether that transition is **FRESH** (not already applied), nor about
its ORDERING relative to other turns. A light client verifying `(pi, π)` learns "this is a REAL
transition", NOT "this is a fresh, unreplayed transition".

Cross-turn FRESHNESS / NO-REPLAY / ordering is **NOT part of THIS theorem**. Its LOGIC is now modeled
and proved in `Dregg2.Circuit.Freshness` — `no_replay`/`deployed_no_replay` PARAMETRIC over a
`CommitSurface`, with nonce-monotonicity DERIVED from the deployed executor (`nonce_strictly_increases`
= `CrossTurnFreshness.runTurn_forest_strictly_advances`, not assumed). HONEST RESIDUAL: grounding a
CONCRETE surface currently pulls in `RestHashIffFrame` (the infinite-domain-state binding — DEBT B in
docs/reference/CARRIER-CENSUS.md), unrealizable until the function-valued kernel fields are refined to
finite maps. So: the no-replay LOGIC is proved; its full crypto grounding on `Poseidon2SpongeCR` ALONE
awaits the finite-map data refinement. The DEPLOYED machinery this
single-transition apex does not itself model:
  * the **commitment-chain CAS** (`proof_verify.rs`): the live stored commitment must equal the
    proof's pre-anchor; applying the proof advances the live commitment to the post-anchor — modeled
    as `LiveCommitMatches` over a `Freshness.CommitChain`;
  * **cell-nonce monotonicity** (`cell_state.rs` "Monotonic"): the agent nonce is bound INTO
    `recStateCommit` (it lives in the agent cell's leaf, hashed through the leaf hash `CH`) and
    strictly increases each turn, so the commitment sequence never cycles — a consumed `pre` never
    recurs. This is a THEOREM, not an assumption: `Freshness.commit_binds_nonce` (equal commitment ⟹
    equal nonce — a nonce difference is a Poseidon collision) and `Freshness.nonce_strictly_increases`
    (every accepted `Admission.runTurn` over the live `execFullForestA` forest body strictly advances
    the agent nonce — the never-rolled-back committed prologue's `+1`, with the whole body proved
    nonce-nondecreasing per-arm and all three nonce-reset vectors closed at the executor).

A light client that wants freshness MUST additionally track the live stored commitment (the CAS) and
reject any proof whose pre-anchor ≠ the live commitment; the proof `(pi, π)` ALONE does not establish
freshness. The cross-turn close — `commit-chain + nonce-monotone ⟹ each proof applicable at most
once` — is `Freshness.no_replay` / `replay_rejected_after_apply`, lifted onto the LIVE forest executor
by `Freshness.deployed_no_replay` (the accepted-`runTurn` sequence IS a monotone `CommitChain`; the
advance is DERIVED, not assumed). Its crypto residual is EXACTLY `Poseidon2SpongeCR` (the four
sponge-shaped CR fields — root/node/frame/leaf — all reduce to that one hash floor via
the historical `Freshness.poseidon2CommitSurface`, now the floor-free `spongeCommitSurface`) plus the
PROVED nonce-monotone invariant;
the deployed replacement is `CommitFaithfulRegrounded.no_replay_faithful` — ⚠ WITH THE CAVEAT that
⚑ THIS CAVEAT IS NOW SPENT AND THE TEXT IS CORRECTED. It read "its `FaithfulBreak` opens with a
global-existential `SpongeCollision compressN` and so holds freely at deployed width" — TRUE when
written, FALSE since: `FaithfulBreak` was NARROWED and now opens with `CompressColl cmb` at a named
pair, and the free version was renamed `FaithfulBreakGlobal`. A correction can go stale faster than
the claim it corrected, which is why it names the object rather than describing it. The sole non-crypto
carrier is the structural `RestHashIffFrame` (not sponge-reducible — the state carries function-valued
components). Do NOT read "a light client that runs nothing cannot be fooled" as covering replay: it
covers AUTHENTICITY of a single transition; FRESHNESS is the CAS's job, discharged in `Freshness`. -/

/-- **`WitnessDecodes hash R S pi` — the witness→kernel-state EXISTENCE rung (NAMED, not faked).**

Any `Satisfied2` witness of the claimed descriptor `R pi.effect` that PUBLISHES `pi.toPublished` (its
rotated PI old/new commitments equal `pi`'s) decodes to SOME `(pre, post)` via a faithful
`StateDecode`. This is the existence of REAL well-formed kernel states behind the published roots — the
surjectivity of the commitment surface on the values a verifying witness pins. A light client cannot
supply `pre`/`post`; this rung SUPPLIES them. It must NOT be discharged by assuming the apex's
conclusion — it is carried EXPLICITLY (exactly as `StarkSound` is), and the apex consumes it to derive
the decode. REALIZABLE (the prover committed to the kernels whose roots the trace publishes). -/
def WitnessDecodes (hash : List ℤ → ℤ) (R : Registry) (S : CommitSurface)
    (pi : BatchPublicInputs) : Prop :=
  ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
    Satisfied2 hash (R pi.effect) minit mfin maddrs t →
    tracePublishedCommit t = pi.toPublished →
    ∃ pre post : RecChainedState, StateDecode S pi.toPublished pre post

theorem lightclient_unfoolable
    (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry)
    (hCR : Poseidon2SpongeCR hash) [StarkSound hash R]
    (kstep : EffectIdx → RecChainedState → RecChainedState → Prop)
    (hrefines : ∀ e, descriptorRefines S hash (R e) (kstep e))
    (pi : BatchPublicInputs) (π : BatchProof)
    (hwitdec : WitnessDecodes hash R S pi)
    (hacc : verifyBatch (vkOfRegistry R) pi π = accept) :
    ∃ pre post : RecChainedState,
      StateDecode S pi.toPublished pre post ∧
      kstep pi.effect pre post ∧
      pi.pre = S.commit pre.kernel pi.turn ∧
      pi.post = S.commit post.kernel pi.turn := by
  -- (1) strengthened STARK soundness extracts a Satisfied2 witness of the CLAIMED descriptor whose
  --     published commitments ARE `pi.toPublished`.
  obtain ⟨minit, mfin, maddrs, t, hsat, hpub⟩ :=
    (inferInstance : StarkSound hash R).extract pi π hacc
  -- (2) the carried witness→state EXISTENCE rung supplies the decoded kernel boundary `(pre, post)`.
  obtain ⟨pre, post, hdecode⟩ := hwitdec minit mfin maddrs t hsat hpub
  -- (3) the carried per-effect rung (fed the named hash CR carrier `hCR`) turns the circuit witness +
  --     the derived decode into the step.
  have hstep : kstep pi.effect pre post :=
    hrefines pi.effect hCR minit mfin maddrs t pi.toPublished pre post hsat hdecode
  -- (4) faithfulness re-exports the published commitments as the genuine endpoint commitments.
  refine ⟨pre, post, hdecode, hstep, ?_, ?_⟩
  · simpa using hdecode.preBinds
  · simpa using hdecode.postBinds

/-! ## §7 — the headline corollary: a genuine kernel TURN (forest-composition shape).

The natural downstream `kstep` is the dispatcher arm: a single committed `fullActionStep`. A turn is a
list of such steps composed by `turnSpec`, which `execFullTurnA_iff_turnSpec` identifies with the real
executor `execFullTurnA`. `lightclient_turn_unfoolable` packages the apex at this `kstep` over a
SINGLE-action turn, and re-exports it as a genuine `execFullTurnA` run — the "∃ genuine kernel
transition" headline. Multi-step composition chains these via `stateDecodeChain_frame_continuous`
(§4): the per-seam frame is DERIVED from the shared published commitments, so a chain of single-action
apexes folds into a whole-turn `turnSpec` exactly as `TurnCircuitCompose.turn_emitted_refines_exec_direct`
folds its per-step `hstep`. -/

/-- The single-action dispatcher arm: the published effect index names an action whose
`fullActionStep` holds between the decoded endpoints. -/
def dispatchArm (e : EffectIdx) (pre post : RecChainedState) : Prop :=
  ∃ fa : FullActionA, actionTag fa = e ∧ fullActionStep pre fa post

/-- **`lightclient_turn_unfoolable`** — the headline at the dispatcher arm. From a verifying batch and
the named floors (including the carried `WitnessDecodes` existence rung — the light client supplies NO
`pre`/`post`), there EXIST decoded endpoints and a genuine committed single-action kernel turn
(`execFullTurnA pre [fa] = some post`) whose endpoints are the published commitments. The per-effect
rung is carried as `hrefines` at `dispatchArm`. -/
theorem lightclient_turn_unfoolable
    (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry)
    (hCR : Poseidon2SpongeCR hash) [StarkSound hash R]
    (hrefines : ∀ e, descriptorRefines S hash (R e) (dispatchArm e))
    (pi : BatchPublicInputs) (π : BatchProof)
    (hwitdec : WitnessDecodes hash R S pi)
    (hacc : verifyBatch (vkOfRegistry R) pi π = accept) :
    ∃ pre post : RecChainedState,
      StateDecode S pi.toPublished pre post ∧
      (∃ fa : FullActionA, execFullTurnA pre [fa] = some post) ∧
      pi.pre = S.commit pre.kernel pi.turn ∧
      pi.post = S.commit post.kernel pi.turn := by
  obtain ⟨pre, post, hdecode, harm, hpre, hpost⟩ :=
    lightclient_unfoolable hash S R hCR dispatchArm hrefines pi π hwitdec hacc
  obtain ⟨fa, _htag, hstep⟩ := harm
  refine ⟨pre, post, hdecode, ⟨fa, ?_⟩, hpre, hpost⟩
  -- `fullActionStep pre fa post` ⟺ `turnSpec pre [fa] post` ⟺ `execFullTurnA pre [fa] = some post`.
  rw [execFullTurnA_iff_turnSpec]
  exact ⟨post, hstep, rfl⟩

/-! ## §8 — the WHOLE-TURN apex: composing the per-effect rung along a turn (FOREST shape).

§6/§7 land the apex on ONE effect. A turn is a LIST of effects, witnessed by a LIST of per-step circuit
witnesses, each publishing its own OLD/NEW commitment (the prover's chained-root column). This section
LIFTS the single-effect apex to a whole-turn statement: from the carried per-effect family `hrefines :
∀ e, descriptorRefines (R e) (dispatchArm e)` + the named floors, derive that a turn whose EVERY step's
circuit is satisfied yields a genuine `execFullTurnA s acts = some s'` over chained kernel states whose
ENDPOINTS commit to the published turn-level `(pre, post)`.

The composition is the §4 `DecodedStep` chain, folded:

  * `TurnDecodeChain` — a list of `DecodedStep`s threaded left-to-right so each step's post IS the next
    step's pre (`a.post = b.pre` as a FULL chained state — the executor's actual carried state), with
    the published seam commitments AGREEING across the boundary (`a.pc.pubPost = b.pc.pubPre`) at one
    boundary turn. The KERNEL half of the seam is then DERIVED — `stateDecodeChain_frame_continuous`
    proves the threaded kernels coincide from the published-commitment binding, so a prover who
    publishes a seam commitment disagreeing with the threaded kernel is REJECTED (the frame TOOTH). The
    chain is the §4 frame made whole-turn: not assumed, certified.

  * `turnDecodeChain_refines_turnSpec` — fold the per-step `descriptorRefines` (each step's circuit
    witness + faithful decode ⟹ its `dispatchArm`) along the chain into the declarative `turnSpec`,
    mirroring `TurnCircuitCompose.turn_emitted_refines_exec_direct`'s shape but landing on the ROTATED
    `dispatchArm` (not the universe-A `stepEmittedSat`).

  * `lightclient_turn_unfoolable_forest` — the whole-turn headline: a verified turn (every step's
    circuit satisfied, decoded, seam-published) + `hrefines` + floors ⟹ `∃ acts s s', execFullTurnA s
    acts = some s' ∧ turn-pre = commit s ∧ turn-post = commit s'`. Re-exported to `execFullForestG` by
    the existing `WholeTurnTriangle.execFullForestG_eq_execFullTurnG` lowering downstream.

### NEW carried obligation (named, added to the ledger — NOT laundered)

  * `seamFullState` (a field of `TurnDecodeChain`) — the FULL-state seam `a.post = b.pre`. The
    commitment surface commits ONLY the `RecChainedState.kernel` (`recStateCommit` takes a
    `RecordKernelState`), so the published seam binds the KERNEL half of `a.post = b.pre`
    (DERIVED, the tooth) but NOT the `log` (receipt-chain) half. The executor `execFullTurnA` threads
    the FULL state; thus the log-continuity of the seam is the genuine residue the commitments cannot
    certify. It is carried EXPLICITLY as a chain field (the prover threads the real executor state, so
    `a.post = b.pre` holds by construction of an honest run; a verifier obtains it from the same
    chained-root column that ties the kernels, EXTENDED to the uncommitted log column). REALIZABLE
    (the honest prover's post IS the next pre); named, not assumed silently. The kernel half is
    re-derived as the frame TOOTH (`turnDecodeChain_seam_kernel_derived`) so the commitment binding
    stays load-bearing on the part it covers. -/

/-- **`TurnDecodeChain S start steps fin`** — a whole-turn decode: a list of §4 `DecodedStep`s threaded
left-to-right from `start` to `fin`, each step's circuit satisfied, with the published seam
commitments agreeing across boundaries. The frame's KERNEL half is DERIVED
(`turnDecodeChain_seam_kernel_derived`); the full-state `seam`/`headPre`/`lastPost` fields carry the
uncommitted `log` residue (the NAMED obligation). -/
structure TurnDecodeChain (hash : List ℤ → ℤ) (S : CommitSurface)
    (start fin : RecChainedState) where
  /-- the decoded per-step records (action, descriptor, published commitment, decode). -/
  steps     : List (DecodedStep S)
  /-- every step publishes a circuit witness `Satisfied2` of its descriptor (the per-step accept). -/
  sat       : ∀ d ∈ steps, ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
                Satisfied2 hash d.descr minit mfin maddrs t ∧
                  tracePublishedCommit t = d.pc
  /-- the turn pre-state IS the first step's pre (or `start = fin` on an empty turn). -/
  headPre   : steps.head?.elim (start = fin) (fun d => start = d.pre)
  /-- the turn post-state IS the last step's post (full-state). -/
  lastPost  : steps.getLast?.elim (start = fin) (fun d => d.post = fin)
  /-- **the threaded seam (FULL-state):** each step's post IS the next step's pre. The KERNEL half is
      DERIVED from the published seam; the `log` half is the NAMED residue (see the ledger). -/
  seam      : List.IsChain (fun a b => a.post = b.pre) steps
  /-- the published seam commitments AGREE across each boundary (the prover's chained-root column). -/
  pubSeam   : List.IsChain (fun a b => a.pc.turn = b.pc.turn ∧ a.pc.pubPost = b.pc.pubPre) steps

/-- **The frame TOOTH (kernel half DERIVED, not assumed).** For every adjacent pair in a
`TurnDecodeChain`, the published seam commitments FORCE the threaded kernels to coincide
(`a.post.kernel = b.pre.kernel`) — `stateDecodeChain_frame_continuous` applied along the chain. So a
prover whose published seam commitment disagrees with the threaded kernel is REJECTED: the kernel half
of `seam` is certified by the commitment binding, not taken on faith.

⚑ **NARROWED 2026-07-31**: `hfin` says every threaded kernel is FINITELY REPRESENTABLE. Stated as a
per-step hypothesis rather than a field of `DecodedStep` so the restriction is VISIBLE in the
signature of every theorem that uses it, instead of hiding inside a carried structure.

⚑ **EXTRACTOR FORM 2026-08-01 (second pass).** The per-adjacency side condition is carried as a chain
(`NoSeamCommitColl`), exactly as the LOG half already carried `NoLogSeamColl` — same shape, same
`List.IsChain` fold, one named pair per seam. The first pass instead wrapped the whole conclusion in
ONE `OrBreak S.StateBreak`; that reads as economical ("a single collision anywhere is a single break")
but the disjunct is free at deployed parameters, so the economy was that the theorem said nothing. -/
theorem turnDecodeChain_seam_kernel_derived (hash : List ℤ → ℤ) (S : CommitSurface)
    {start fin : RecChainedState} (c : TurnDecodeChain hash S start fin)
    (hfin : ∀ d ∈ c.steps, FiniteRepresentable d.pre.kernel ∧ FiniteRepresentable d.post.kernel)
    (hno : NoSeamCommitColl S c.steps) :
    List.IsChain (fun a b => a.post.kernel = b.pre.kernel) c.steps := by
  rw [List.isChain_iff_getElem]
  intro i hi
  have hpub := List.isChain_iff_getElem.mp c.pubSeam i hi
  have hseam := List.isChain_iff_getElem.mp hno i hi
  exact stateDecodeChain_frame_continuous S _ _
    (hfin _ (List.getElem_mem _)).2 (hfin _ (List.getElem_mem _)).1 hpub.1 hpub.2 hseam

/-- **The per-step refinement obligation over a decoded turn.** Each decoded step's descriptor is the
registry entry for SOME effect index `e`, and its circuit witness + faithful decode force `dispatchArm
e d.pre d.post` (i.e. an action of effect `e` carries the step). This is the per-step accept the
carried `descriptorRefines` family discharges — quantified over the chain's steps. -/
def StepsRefine (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry)
    {start fin : RecChainedState} (c : TurnDecodeChain hash S start fin) : Prop :=
  ∀ d ∈ c.steps, ∃ e : EffectIdx, d.descr = R e ∧ dispatchArm e d.pre d.post

/-- **Each step's `descriptorRefines` discharges `StepsRefine`.** Given the carried per-effect family
`hrefines` and the named hash CR carrier, the per-step circuit accepts (`c.sat`) + faithful decodes
(`d.decode`) force `dispatchArm e d.pre d.post` at every step whose descriptor is `R e`. This is the
registry-wide rung consumed step-by-step — the rotated analog of `step_emitted_refines_fullActionStep`.
The effect-index identification (`d.descr = R e`) is supplied by the witness layout (`hidx`). -/
theorem stepsRefine_of_descriptorRefines
    (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry)
    (hCR : Poseidon2SpongeCR hash)
    (hrefines : ∀ e, descriptorRefines S hash (R e) (dispatchArm e))
    {start fin : RecChainedState} (c : TurnDecodeChain hash S start fin)
    (hidx : ∀ d ∈ c.steps, ∃ e : EffectIdx, d.descr = R e) :
    StepsRefine hash S R c := by
  intro d hd
  obtain ⟨e, hde⟩ := hidx d hd
  obtain ⟨minit, mfin, maddrs, t, hsat, hpub⟩ := c.sat d hd
  refine ⟨e, hde, ?_⟩
  -- the carried rung for descriptor `R e`, fed the named CR carrier, the witness, and the decode.
  have hsat' : Satisfied2 hash (R e) minit mfin maddrs t := hde ▸ hsat
  exact hrefines e hCR minit mfin maddrs t d.pc d.pre d.post hsat' d.decode

/-- **Fold `StepsRefine` along the threaded chain into `turnSpec`.** A `TurnDecodeChain` whose every
step refines (`StepsRefine`) induces the declarative `turnSpec` from `start` to `fin` over SOME action
list (each action the `fa` the step's `dispatchArm` names). Mirrors `turn_emitted_refines_exec_direct`'s
per-step→turn fold; the full-state `seam` threads the actual executor state (kernel half certified by
the frame tooth), so the fold composes left-to-right with no gap. -/
theorem turnDecodeChain_refines_turnSpec
    (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry)
    {start fin : RecChainedState} (c : TurnDecodeChain hash S start fin)
    (href : StepsRefine hash S R c) :
    ∃ acts : List FullActionA, turnSpec start acts fin := by
  -- A clean list induction with every threaded hypothesis as an explicit `∀`/`→` argument, so the
  -- IH shape is exactly the recursion (`start := d.post`). The endpoints (`headPre`/`lastPost`), the
  -- full-state `seam`, and the per-step refinement are all threaded uniformly.
  unfold StepsRefine at href
  obtain ⟨steps, _sat, headPre, lastPost, seam, _pubSeam⟩ := c
  simp only at href headPre lastPost
  suffices key : ∀ (steps : List (DecodedStep S)) (start : RecChainedState),
      List.IsChain (fun a b => a.post = b.pre) steps →
      steps.head?.elim (start = fin) (fun d => start = d.pre) →
      steps.getLast?.elim (start = fin) (fun d => d.post = fin) →
      (∀ d ∈ steps, ∃ e : EffectIdx, d.descr = R e ∧ dispatchArm e d.pre d.post) →
      ∃ acts : List FullActionA, turnSpec start acts fin by
    exact key steps start seam headPre lastPost href
  clear seam headPre lastPost href _sat _pubSeam steps start
  intro steps
  induction steps with
  | nil =>
      -- empty turn: `start = fin`, the empty `turnSpec`.
      intro start _seam headPre _lastPost _href
      simp only [List.head?_nil, Option.elim_none] at headPre
      exact ⟨[], by simpa [turnSpec] using headPre⟩
  | cons d rest ih =>
      intro start seam headPre lastPost href
      -- head: `start = d.pre`; the head step refines to `dispatchArm e d.pre d.post`.
      simp only [List.head?_cons, Option.elim_some] at headPre
      obtain ⟨e, _hde, fa, _htag, hstep⟩ := href d List.mem_cons_self
      -- the seam gives `d.post = (head of rest).pre`; recurse from `d.post`.
      have hseamRest : List.IsChain (fun a b => a.post = b.pre) rest := seam.tail
      have hheadRest : rest.head?.elim (d.post = fin) (fun d' => d.post = d'.pre) := by
        cases rest with
        | nil => simpa using (by simpa using lastPost)
        | cons d' _ =>
            have hrel := (List.isChain_cons.mp seam).1 d' (by simp)
            simpa using hrel
      have hlastRest : rest.getLast?.elim (d.post = fin) (fun d' => d'.post = fin) := by
        cases rest with
        | nil => simpa using lastPost
        | cons d' rest' =>
            have heq : (d :: d' :: rest').getLast? = (d' :: rest').getLast? := by
              simp [List.getLast?_cons_cons]
            rw [heq, List.getLast?_eq_getLast (List.cons_ne_nil d' rest')] at lastPost
            rw [List.getLast?_eq_getLast (List.cons_ne_nil d' rest')]
            exact lastPost
      have hrefRest : ∀ d'' ∈ rest, ∃ e' : EffectIdx, d''.descr = R e' ∧
          dispatchArm e' d''.pre d''.post := fun d'' hd'' => href d'' (List.mem_cons_of_mem _ hd'')
      obtain ⟨acts, htail⟩ := ih d.post hseamRest hheadRest hlastRest hrefRest
      -- prepend `fa`: `fullActionStep start fa d.post` (subst `start = d.pre`), then the tail.
      subst headPre
      exact ⟨fa :: acts, d.post, hstep, htail⟩

/-- **`turnDecodeChain_refines_turnSpec_gen` — the fold, GENERIC over an arm + step relation.** The
list-induction core of `turnDecodeChain_refines_turnSpec`, abstracted away from the toy `dispatchArm`/
`fullActionStep`: given any per-effect arm `arm : EffectIdx → RecChainedState → RecChainedState → Prop`
whose every step entails some `(fa, actionTag fa = e, stepRel pre fa post)` (the lowering hypothesis
`harm`), a `TurnDecodeChain` whose every step is `arm e d.pre d.post` (the `harm`-style per-step rung
`hsteps`) folds into `∃ acts, Spec.Turn.turnSpec stepRel start acts fin`. The toy fold
(`turnDecodeChain_refines_turnSpec`) is the instance at `arm := dispatchArm`, `stepRel :=
fullActionStep`; the FAITHFUL fold instantiates it at `arm := dispatchArmFacet …`, `stepRel :=
fullActionStepFacet …`. The proof reads `arm` ONLY through `harm`, so the same induction serves both
towers. -/
theorem turnDecodeChain_refines_turnSpec_gen
    (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry)
    (arm : EffectIdx → RecChainedState → RecChainedState → Prop)
    (stepRel : RecChainedState → FullActionA → RecChainedState → Prop)
    (harm : ∀ e pre post, arm e pre post →
      ∃ fa : FullActionA, actionTag fa = e ∧ stepRel pre fa post)
    {start fin : RecChainedState} (c : TurnDecodeChain hash S start fin)
    (hsteps : ∀ d ∈ c.steps, ∃ e : EffectIdx, d.descr = R e ∧ arm e d.pre d.post) :
    ∃ acts : List FullActionA, Spec.Turn.turnSpec stepRel start acts fin := by
  obtain ⟨steps, _sat, headPre, lastPost, seam, _pubSeam⟩ := c
  simp only at hsteps headPre lastPost
  suffices key : ∀ (steps : List (DecodedStep S)) (start : RecChainedState),
      List.IsChain (fun a b => a.post = b.pre) steps →
      steps.head?.elim (start = fin) (fun d => start = d.pre) →
      steps.getLast?.elim (start = fin) (fun d => d.post = fin) →
      (∀ d ∈ steps, ∃ e : EffectIdx, d.descr = R e ∧ arm e d.pre d.post) →
      ∃ acts : List FullActionA, Spec.Turn.turnSpec stepRel start acts fin by
    exact key steps start seam headPre lastPost hsteps
  clear seam headPre lastPost hsteps _sat _pubSeam steps start
  intro steps
  induction steps with
  | nil =>
      intro start _seam headPre _lastPost _href
      simp only [List.head?_nil, Option.elim_none] at headPre
      exact ⟨[], by simpa [Spec.Turn.turnSpec] using headPre⟩
  | cons d rest ih =>
      intro start seam headPre lastPost href
      simp only [List.head?_cons, Option.elim_some] at headPre
      obtain ⟨e, _hde, harmStep⟩ := href d List.mem_cons_self
      obtain ⟨fa, _htag, hstep⟩ := harm e d.pre d.post harmStep
      have hseamRest : List.IsChain (fun a b => a.post = b.pre) rest := seam.tail
      have hheadRest : rest.head?.elim (d.post = fin) (fun d' => d.post = d'.pre) := by
        cases rest with
        | nil => simpa using (by simpa using lastPost)
        | cons d' _ =>
            have hrel := (List.isChain_cons.mp seam).1 d' (by simp)
            simpa using hrel
      have hlastRest : rest.getLast?.elim (d.post = fin) (fun d' => d'.post = fin) := by
        cases rest with
        | nil => simpa using lastPost
        | cons d' rest' =>
            have heq : (d :: d' :: rest').getLast? = (d' :: rest').getLast? := by
              simp [List.getLast?_cons_cons]
            rw [heq, List.getLast?_eq_getLast (List.cons_ne_nil d' rest')] at lastPost
            rw [List.getLast?_eq_getLast (List.cons_ne_nil d' rest')]
            exact lastPost
      have hrefRest : ∀ d'' ∈ rest, ∃ e' : EffectIdx, d''.descr = R e' ∧
          arm e' d''.pre d''.post := fun d'' hd'' => href d'' (List.mem_cons_of_mem _ hd'')
      obtain ⟨acts, htail⟩ := ih d.post hseamRest hheadRest hlastRest hrefRest
      subst headPre
      exact ⟨fa :: acts, d.post, hstep, htail⟩

/-! ### §8.1 — the turn-level endpoint commitments (DERIVED from the chain's first/last step).

The whole-turn headline must export the PUBLISHED turn-level `(pre, post)` as genuine commitments of
the executor's endpoint kernels (`start`/`fin`). The turn's published pre/post commitments are exactly
the head step's `pubPre` and the last step's `pubPost` (the two open ends of the prover's chained-root
column). `TurnEndpoints` says the turn-level published commitments AND turn are pinned to those open
ends; `turnDecodeChain_endpoints_commit` then DERIVES, from the head/last step decodes alone, that the
published turn-level pre/post ARE `S.commit start.kernel` / `S.commit fin.kernel` — the endpoint
commitments are forced by the same per-step binding the seams use, not assumed. -/

/-- **`TurnEndpoints`** — the turn-level published commitment view pinned to the chain's open ends. The
published turn-pre/turn-post commitments equal the head step's `pubPre` / the last step's `pubPost`
(the two unmatched ends of the prover's chained-root column), at the boundary turn `tp.turn`, which
agrees with the head/last step's commitment turn. On an EMPTY turn there is no step root to read, so the
degenerate branch carries the endpoint binding DIRECTLY (`tp.pubPre`/`tp.pubPost = S.commit start.kernel
tp.turn`, with `start = fin` so both endpoints commit to the same kernel) — named, not laundered. -/
structure TurnEndpoints (hash : List ℤ → ℤ) (S : CommitSurface)
    {start fin : RecChainedState} (c : TurnDecodeChain hash S start fin) where
  /-- the published turn-level pre/post commitment view (the light client's `pi.toPublished`). -/
  tp        : PublishedCommit
  /-- the published turn-pre commitment IS the head step's `pubPre` (the open OLD end); on the empty
      turn it directly binds `start.kernel` (no step root exists to derive it from). -/
  headOpen  : c.steps.head?.elim (tp.pubPre = S.commit start.kernel tp.turn)
                (fun d => tp.pubPre = d.pc.pubPre ∧ tp.turn = d.pc.turn)
  /-- the published turn-post commitment IS the last step's `pubPost` (the open NEW end); on the empty
      turn it directly binds `fin.kernel`. -/
  lastOpen  : c.steps.getLast?.elim (tp.pubPost = S.commit fin.kernel tp.turn)
                (fun d => tp.pubPost = d.pc.pubPost ∧ tp.turn = d.pc.turn)

/-- **The turn-level endpoint commitments are DERIVED (not assumed) on a non-empty turn.** Given the
chain's `headPre`/`lastPost` (which thread `start`/`fin` to the head/last step's `pre`/`post`) and the
`TurnEndpoints` pinning of the published turn-pre/turn-post to the open ends, the published turn-level
commitments ARE the surface commitments of the executor endpoints: `tp.pubPre = S.commit start.kernel
tp.turn` and `tp.pubPost = S.commit fin.kernel tp.turn`. On a non-empty turn the head/last step decodes
(`preBinds`/`postBinds`) FORCE the binding (same per-step rung the seams use); on the empty turn the
`TurnEndpoints` degenerate branch carries it directly. -/
theorem turnDecodeChain_endpoints_commit (hash : List ℤ → ℤ) (S : CommitSurface)
    {start fin : RecChainedState} (c : TurnDecodeChain hash S start fin)
    (te : TurnEndpoints hash S c) :
    te.tp.pubPre = S.commit start.kernel te.tp.turn ∧
      te.tp.pubPost = S.commit fin.kernel te.tp.turn := by
  obtain ⟨tp, headOpen, lastOpen⟩ := te
  -- The head step pins `start`; the last step pins `fin`. Both via the step decode's binding.
  refine ⟨?_, ?_⟩
  · -- pubPre = S.commit start.kernel tp.turn
    cases hsteps : c.steps with
    | nil =>
        -- empty turn: the degenerate `TurnEndpoints` branch binds `start.kernel` directly.
        rw [hsteps] at headOpen; simpa using headOpen
    | cons d rest =>
        have hhead : tp.pubPre = d.pc.pubPre ∧ tp.turn = d.pc.turn := by
          rw [hsteps] at headOpen; simpa using headOpen
        have hstart : start = d.pre := by
          have := c.headPre; rw [hsteps] at this; simpa using this
        rw [hhead.1, hhead.2, hstart]; exact d.decode.preBinds
  · -- pubPost = S.commit fin.kernel tp.turn
    cases hsteps : c.steps.getLast? with
    | none =>
        -- `getLast? = none ⟺ steps = []`; the degenerate branch binds `fin.kernel` directly.
        have hnil : c.steps = [] := List.getLast?_eq_none_iff.mp hsteps
        rw [hnil] at lastOpen; simpa using lastOpen
    | some dl =>
        have hlastOpen : tp.pubPost = dl.pc.pubPost ∧ tp.turn = dl.pc.turn := by
          rw [hsteps] at lastOpen; simpa using lastOpen
        have hfin : dl.post = fin := by
          have := c.lastPost; rw [hsteps] at this; simpa using this
        rw [hlastOpen.1, hlastOpen.2, ← hfin]; exact dl.decode.postBinds

/-! ### §8.2 — `lightclient_turn_unfoolable_forest`: the WHOLE-TURN apex.

The headline. A verified turn — a `TurnDecodeChain` (every step's circuit `Satisfied2`, decoded, the
published seams agreeing) + the per-step effect-index identification (`hidx`) + the turn-level endpoint
pinning (`TurnEndpoints`) — together with the named floors (`hCR` + the carried per-effect family
`hrefines`) yields a GENUINE executor run `execFullTurnA start acts = some fin` whose ENDPOINTS commit
to the published turn-level `(pre, post)`. The light client RAN NOTHING; it verified per-step accepts
and read the two open ends of the chained-root column.

The derivation:
  1. `stepsRefine_of_descriptorRefines` discharges the per-step `dispatchArm` from the carried
     `hrefines` family + the per-step circuit accepts (`c.sat`) + faithful decodes (`d.decode`);
  2. `turnDecodeChain_refines_turnSpec` folds those along the threaded (kernel-half-certified) chain
     into `∃ acts, turnSpec start acts fin`;
  3. `execFullTurnA_iff_turnSpec` lowers `turnSpec` to the real executor `execFullTurnA`;
  4. `turnDecodeChain_endpoints_commit` re-exports the published turn-level pre/post as the genuine
     endpoint commitments (`S.commit start.kernel` / `S.commit fin.kernel`).

`execFullForestG`: the natural tree-shaped run lowers to this linear `execFullTurnA` by the existing
`Exec.FullForestAuth.execFullForestG_eq_execFullTurnG` / `Spec.WholeTurnTriangle` bridge — a forest is
the pre-order lowering of its turns, so this whole-turn statement is the linear core the forest run
factors through. -/
theorem lightclient_turn_unfoolable_forest
    (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry)
    (hCR : Poseidon2SpongeCR hash)
    (hrefines : ∀ e, descriptorRefines S hash (R e) (dispatchArm e))
    {start fin : RecChainedState} (c : TurnDecodeChain hash S start fin)
    (hidx : ∀ d ∈ c.steps, ∃ e : EffectIdx, d.descr = R e)
    (te : TurnEndpoints hash S c) :
    ∃ (acts : List FullActionA) (s s' : RecChainedState),
      execFullTurnA s acts = some s' ∧
      te.tp.pubPre = S.commit s.kernel te.tp.turn ∧
      te.tp.pubPost = S.commit s'.kernel te.tp.turn := by
  -- (1) the carried per-effect family discharges the per-step `dispatchArm` over the whole chain.
  have href : StepsRefine hash S R c :=
    stepsRefine_of_descriptorRefines hash S R hCR hrefines c hidx
  -- (2) fold the per-step refinement along the threaded chain into the declarative `turnSpec`.
  obtain ⟨acts, hturn⟩ := turnDecodeChain_refines_turnSpec hash S R c href
  -- (3) lower `turnSpec` to the genuine executor run.
  have hexec : execFullTurnA start acts = some fin :=
    (execFullTurnA_iff_turnSpec start fin acts).mpr hturn
  -- (4) the published turn-level commitments ARE the endpoint commitments (derived; §8.1).
  obtain ⟨hpre, hpost⟩ := turnDecodeChain_endpoints_commit hash S c te
  exact ⟨acts, start, fin, hexec, hpre, hpost⟩

/-! ## §9 — the INTRA-TURN RECEIPT-LOG seam: binding the LOG half of `a.post = b.pre`.

The kernel half of the turn-chain seam is DERIVED (`turnDecodeChain_seam_kernel_derived` /
`stateDecodeChain_frame_continuous`): the published seam commitments FORCE `a.post.kernel = b.pre.kernel`,
because `CommitSurface.commit` (= `recStateCommit`) BINDS the kernel. But `recStateCommit` is
KERNEL-ONLY (`RecordKernelState → Turn → ℤ`; the `RecChainedState.log` receipt chain is NOT one of its
inputs), so the published kernel seam says NOTHING about the `log`. The full-state `seam` field of
`TurnDecodeChain` (`a.post = b.pre` over the WHOLE `RecChainedState`, log included) therefore carried
its LOG half as a free residue: a prover could publish a turn-chain whose kernels chain genuinely while
the intermediate RECEIPT-LOG an observer reads is FORGED. The dregg through-line — "a turn leaves a
VERIFIABLE receipt" — was unforced at the composition seam.

This section CLOSES that, mirroring the kernel tooth EXACTLY. The per-step published LOG commitments
(the `EffectCommit.CommitSurface.LH` field's two published values — `effectStateCommit` already commits
`cmb (cellDigest) (cmb (RH) (LH log))`, so the deployed surface DOES publish + bind the log) are bound
to `pre.log`/`post.log` through the realizable `logHashInjective LH` carrier (the SAME class as the
Poseidon/Merkle CR set — a hypothesis, never an axiom; exactly what `EffectCommit.effectCircuit_rejects_log_forge`
realizes). A published LOG seam (`a.logPubPost = b.logPubPre`, the log column of the chained-root) then
FORCES `a.post.log = b.pre.log` by `LH`-injectivity — the receipt-log half of the seam is CERTIFIED by
the commitment binding, not taken on faith. Combined with the kernel tooth, the FULL `a.post = b.pre`
seam is DERIVED: a forged intermediate receipt-log can't satisfy both the published log seam and the
`logHashInjective` binding without a hash collision.

This is the apex analog of the per-step `ClosureLog.StateDecodeLog` (which forces ONE step's
`post.log = receipt :: pre.log`); here we force the CROSS-STEP log continuity the turn fold consumes. -/

/-- **`LogDecode LH pubLogPre pubLogPost pre post`** — the published LOG commitments of one step bind
its receipt chains through the realizable `logHashInjective LH` carrier: the published OLD/NEW log
commitments equal `LH pre.log` / `LH post.log`. The apex-seam analog of `ClosureLog.StateDecodeLog`'s
`logPreBinds`/`logPostBinds`. `LH` is the `EffectCommit.CommitSurface.LH` field; the two published
values are the log column of the prover's chained-root (mirroring how `pc.pubPre`/`pubPost` are the
kernel-root column). NO axiom: the binding is exactly the deployed `effectStateCommit`'s `LH log` leg. -/
structure LogDecode (LH : List Turn → ℤ) (pubLogPre pubLogPost : ℤ) (pre post : RecChainedState) :
    Prop where
  /-- the published OLD log commitment IS `LH` of `pre.log`. -/
  logPreBinds  : pubLogPre = LH pre.log
  /-- the published NEW log commitment IS `LH` of `post.log`. -/
  logPostBinds : pubLogPost = LH post.log

/-- **FAITHFULNESS (log).** Two log-decodes of the SAME published log commitment force EQUAL receipt
chains — pure `logHashInjective` binding, no admissibility. The log analog of
`StateCommitReduce.stateDecode_pre/post_faithful_orBreak` (the kernel twins; their injective
originals were deleted 2026-08-01 as vacuous). -/
theorem logDecode_faithful (LH : List Turn → ℤ)
    {p q : ℤ} {pre post pre' post' : RecChainedState}
    (hno : ¬ Dregg2.Circuit.LogCommitRegrounded.LogColl LH pre.log pre'.log)
    (h : LogDecode LH p q pre post) (h' : LogDecode LH p q pre' post') :
    pre.log = pre'.log :=
  Dregg2.Circuit.LogCommitRegrounded.logHash_binds_of_noLogColl LH pre.log pre'.log hno
    (by rw [← h.logPreBinds, ← h'.logPreBinds])

/-- **The LOG-SEAM tooth (log half DERIVED, not assumed).** If two adjacent steps' published LOG
commitments AGREE across the boundary (`a.logPubPost = b.logPubPre` — the log column of the prover's
chained-root, equated across the seam exactly as `pubSeam` equates the kernel-root column), and each
binds its receipt chain (`LogDecode`), then their receipt chains COINCIDE: `a.post.log = b.pre.log`.
The receipt-log half of the seam is FORCED by the `logHashInjective` binding — a prover whose published
log commitment disagrees with the threaded receipt chain is REJECTED. The faithful mirror of
`stateDecodeChain_frame_continuous` (kernel half) on the log. -/
theorem logDecodeChain_frame_continuous (LH : List Turn → ℤ)
    {a b : RecChainedState} {ap aq bp bq : ℤ} {a' b' : RecChainedState}
    (hno : ¬ Dregg2.Circuit.LogCommitRegrounded.LogColl LH a'.log b.log)
    (hda : LogDecode LH ap aq a a') (hdb : LogDecode LH bp bq b b')
    (hseam : aq = bp) :
    a'.log = b.log := by
  -- `LH a'.log = aq = bp = LH b.log`, then the per-instance side condition (S3).
  apply Dregg2.Circuit.LogCommitRegrounded.logHash_binds_of_noLogColl LH a'.log b.log hno
  rw [← hda.logPostBinds, hseam, hdb.logPreBinds]

/-- **`TurnDecodeChainLog`** — a `TurnDecodeChain` AUGMENTED with the per-step published LOG decode and
the published LOG seam, so the full-state `seam` (`a.post = b.pre`, log included) is DERIVED on BOTH
halves. `logDecode d` binds step `d`'s published log commitments to `d.pre.log`/`d.post.log`; `logPubPost`
/`logPubPre` are the log column of the chained-root (one published `ℤ` per step boundary); `logPubSeam`
equates them across each boundary (the log analog of `TurnDecodeChain.pubSeam`). The full-state seam is
then `turnDecodeChainLog_seam_full_derived`.

⚑ **DATA ONLY, AND IT IS INHABITED (2026-07-25 bundle cutover).** The `hLog : logHashInjective LH`
field is GONE. It asserted that the receipt-chain accumulator is injective from the UNBOUNDED `List
Turn` into ONE bounded BabyBear felt — which `StateCommitFloorRegrounded.logHashInjective_false_babyBear`
REFUTES for every real deployed accumulator, so no deployed `TurnDecodeChainLog` value could be
constructed and every theorem over the bundle below was VACUOUS. The three consumers now carry the
binding as a PER-INSTANCE `NoLogSeamColl` argument at exactly the adjacencies the deleted field was fed
(a theorem HAS argument positions; a field does not — the bundle-family design decision is recorded at
`Dregg2.Shielded.RealCrypto` §2.0). `Circuit/TurnDecodeChainLogBundleCutoverCheck` constructs
`honestTurnDecodeChainLog` — the honest prover's chained-root, publishing the true log digests — for an
ARBITRARY `LH`, and instantiates it at a deployed accumulator whose `logHashInjective` that module
REFUTES. -/
structure TurnDecodeChainLog (hash : List ℤ → ℤ) (S : CommitSurface) (LH : List Turn → ℤ)
    {start fin : RecChainedState} (c : TurnDecodeChain hash S start fin) where
  /-- per step, its published OLD log commitment (the log column of the chained-root). -/
  logPubPre  : DecodedStep S → ℤ
  /-- per step, its published NEW log commitment. -/
  logPubPost : DecodedStep S → ℤ
  /-- each step's published log commitments bind its receipt chains (`LogDecode`). -/
  logDecode  : ∀ d ∈ c.steps, LogDecode LH (logPubPre d) (logPubPost d) d.pre d.post
  /-- the published LOG commitments AGREE across each boundary (the log column of the chained-root). -/
  logPubSeam : List.IsChain (fun a b => logPubPost a = logPubPre b) c.steps

/-- **`NoLogSeamColl LH postLog preLog steps`** — the PER-INSTANCE side condition that replaced the
deleted `TurnDecodeChainLog.hLog` field. At EVERY adjacency of the decoded chain — precisely the pairs
the old proof fed the refuted floor at, and no others — the two receipt chains the published log seam
equates are NOT an equivocation of the deployed accumulator (`LogCommitRegrounded.LogColl`, which
carries its own distinctness, so the condition is never satisfied vacuously by an equal pair).

⚑ Stated over an ABSTRACT step type with the two log projections passed in, NOT over `List
(DecodedStep S)`. That is deliberate and load-bearing: `DecodedStep S` drags in `S : CommitSurface`,
which is itself a floor-carrying bundle, so the `List (DecodedStep S)`-shaped spelling would have made
the CURE a carrier of a floor it has nothing to do with. The condition is about receipt chains; it is
now typed that way.

Implied by the deleted field at every pair via the grandfathered bridge
`LogCommitRegrounded.noLogColl_of_inj` (one step through `noLogSeamColl_of_forall`), so every consumer
below is strictly STRONGER than its pre-cutover form; and REFUTABLE at a constant accumulator, so it is
not an empty ask (`TurnDecodeChainLogBundleCutoverCheck` §4). -/
def NoLogSeamColl {α : Type} (LH : List Turn → ℤ) (postLog preLog : α → List Turn)
    (steps : List α) : Prop :=
  List.IsChain
    (fun a b => ¬ Dregg2.Circuit.LogCommitRegrounded.LogColl LH (postLog a) (preLog b)) steps

/-- **The uniform lift, FLOOR-FREE.** A non-equivocation claim holding at EVERY pair of receipt chains
gives the per-adjacency side condition on any decoded chain. This is the one step between the
grandfathered bridge `LogCommitRegrounded.noLogColl_of_inj` (`logHashInjective LH → ∀ xs ys, ¬ LogColl
LH xs ys`) and `NoLogSeamColl`, so the pre-cutover statements are recovered by a single composition
WITHOUT minting a new declaration on the refuted floor. -/
theorem noLogSeamColl_of_forall {α : Type} {LH : List Turn → ℤ} {postLog preLog : α → List Turn}
    {steps : List α}
    (h : ∀ xs ys : List Turn, ¬ Dregg2.Circuit.LogCommitRegrounded.LogColl LH xs ys) :
    NoLogSeamColl LH postLog preLog steps := by
  rw [NoLogSeamColl, List.isChain_iff_getElem]
  exact fun i _ => h _ _

/-- **A membership-aware chain.** Every adjacency in `l` is between two elements OF `l` — the
`isChain_iff_getElem` readout, repackaged so per-adjacency reasoning can read both endpoints' carried
per-step data. (Used to feed `logDecode`/the per-step decodes a proof that the adjacent steps are
genuine list members.) -/
private theorem isChain_mem_self {α} (l : List α) :
    List.IsChain (fun a b => a ∈ l ∧ b ∈ l) l := by
  rw [List.isChain_iff_getElem]
  intro i hi
  exact ⟨List.getElem_mem _, List.getElem_mem _⟩

/-- **Combine two chains over the same list.** If `R` and `S` both chain `l`, then their conjunction
chains `l`. The faithful zip the full-state seam (kernel ∧ log) needs. -/
private theorem isChain_and {α} {R S : α → α → Prop} {l : List α}
    (hR : List.IsChain R l) (hS : List.IsChain S l) :
    List.IsChain (fun a b => R a b ∧ S a b) l := by
  rw [List.isChain_iff_getElem] at hR hS ⊢
  exact fun i hi => ⟨hR i hi, hS i hi⟩

/-- **The LOG half of the seam is DERIVED.** For every adjacent pair in a `TurnDecodeChain` augmented by
a `TurnDecodeChainLog`, the published LOG seam FORCES the threaded receipt chains to coincide
(`a.post.log = b.pre.log`) — `logDecodeChain_frame_continuous` along the chain. So a prover whose
published log commitment disagrees with the threaded receipt-log is REJECTED: the receipt-log half of
`seam` is certified by the `logHashInjective` binding, not taken on faith. -/
theorem turnDecodeChainLog_seam_log_derived (hash : List ℤ → ℤ) (S : CommitSurface) (LH : List Turn → ℤ)
    {start fin : RecChainedState} {c : TurnDecodeChain hash S start fin}
    (cl : TurnDecodeChainLog hash S LH c)
    (hno : NoLogSeamColl LH (fun d : DecodedStep S => d.post.log)
      (fun d : DecodedStep S => d.pre.log) c.steps) :
    List.IsChain (fun a b => a.post.log = b.pre.log) c.steps := by
  -- zip the published-log seam, the per-adjacency side condition, and the membership chain, then
  -- discharge each adjacency via the log tooth, reading both endpoints' `LogDecode` from the carried
  -- per-step binding.
  have hmem := isChain_and cl.logPubSeam (isChain_and hno (isChain_mem_self c.steps))
  refine List.IsChain.imp ?_ hmem
  intro a b hab
  obtain ⟨hseam, hnc, ha, hb⟩ := hab
  exact logDecodeChain_frame_continuous LH hnc (cl.logDecode a ha) (cl.logDecode b hb) hseam

/-- **The FULL-state seam is DERIVED (kernel ⊕ log).** Combining the kernel tooth
(`turnDecodeChain_seam_kernel_derived`, from the published kernel-root seam) with the log tooth
(`turnDecodeChainLog_seam_log_derived`, from the published log seam) recovers the WHOLE
`RecChainedState` continuity `a.post = b.pre` — the `seam` field of `TurnDecodeChain`, previously
carried with its log half as a free residue, is now CERTIFIED on both components. A forged intermediate
receipt-log cannot satisfy both the published log seam and the `logHashInjective` binding without a
hash collision; a forged intermediate kernel cannot satisfy the published kernel seam. So the published
turn-chain BINDS the full state — receipts included.

⚑ **NARROWED 2026-07-31**: the KERNEL half now requires `hfin` (every threaded kernel finitely
representable); the LOG half is unchanged.

⚑ **EXTRACTOR FORM 2026-08-01 (second pass)**: BOTH halves now carry a per-instance, per-adjacency
residual — `NoSeamCommitColl` on the kernel side, `NoLogSeamColl` on the log side — and the conclusion
is unconditional again. The first pass wrapped the kernel half in `OrBreak S.StateBreak`, whose
disjunct is free at deployed parameters; the two halves are now the SAME shape, which is what the log
cutover had right in the first place. -/
theorem turnDecodeChainLog_seam_full_derived (hash : List ℤ → ℤ) (S : CommitSurface) (LH : List Turn → ℤ)
    {start fin : RecChainedState} {c : TurnDecodeChain hash S start fin}
    (cl : TurnDecodeChainLog hash S LH c)
    (hfin : ∀ d ∈ c.steps, FiniteRepresentable d.pre.kernel ∧ FiniteRepresentable d.post.kernel)
    (hnoK : NoSeamCommitColl S c.steps)
    (hno : NoLogSeamColl LH (fun d : DecodedStep S => d.post.log)
      (fun d : DecodedStep S => d.pre.log) c.steps) :
    List.IsChain (fun a b => a.post = b.pre) c.steps := by
  have hkerChain := turnDecodeChain_seam_kernel_derived hash S c hfin hnoK
  have hlog := turnDecodeChainLog_seam_log_derived hash S LH cl hno
  -- zip the kernel-continuity and log-continuity chains, then `a.post.kernel = b.pre.kernel ∧
  -- a.post.log = b.pre.log ⟹ a.post = b.pre` (structure eta).
  refine List.IsChain.imp ?_ (isChain_and hkerChain hlog)
  intro a b hab
  obtain ⟨hk, hl⟩ := hab
  -- `a.post = b.pre` from equal kernels AND equal logs (the two `RecChainedState` fields, eta).
  calc a.post = ⟨a.post.kernel, a.post.log⟩ := rfl
    _ = ⟨b.pre.kernel, b.pre.log⟩ := by rw [hk, hl]
    _ = b.pre := rfl

/-- **MUTATION CONFIRM — a forged intermediate receipt-log is UNSAT.** Any `TurnDecodeChainLog` whose
published log commitments agree across the seam (`logPubSeam`) and bind each step's receipt chain
(`logDecode`) CANNOT carry a forged intermediate boundary: if the post-log of step `i` disagreed with
the pre-log of step `i+1` (`hforge`), `turnDecodeChainLog_seam_log_derived` forces them EQUAL — a direct
contradiction (`False`). So no satisfying turn-chain exhibits the forge. This is the receipt-log analog
of `effectCircuit_rejects_log_forge`, lifted to the CROSS-STEP seam: the published turn-chain binds the
intermediate receipt-log, not just the kernels. -/
theorem turnDecodeChainLog_rejects_forged_log (hash : List ℤ → ℤ) (S : CommitSurface) (LH : List Turn → ℤ)
    {start fin : RecChainedState} {c : TurnDecodeChain hash S start fin}
    (cl : TurnDecodeChainLog hash S LH c)
    (hno : NoLogSeamColl LH (fun d : DecodedStep S => d.post.log)
      (fun d : DecodedStep S => d.pre.log) c.steps)
    {i : Nat} (hi : i + 1 < c.steps.length)
    (hforge : (c.steps[i]'(by omega)).post.log ≠ (c.steps[i+1]'hi).pre.log) :
    False := by
  have hchain := turnDecodeChainLog_seam_log_derived hash S LH cl hno
  -- the forged boundary `(i, i+1)` is an adjacency in `c.steps`; the derived chain forces its log
  -- continuity, contradicting the forge.
  rw [List.isChain_iff_getElem] at hchain
  exact hforge (hchain i hi)

/-! ### §9.1 — NON-VACUITY of the log seam (the `logHashInjective` carrier is load-bearing).

The close is non-vacuous: the `hLog : logHashInjective LH` carrier is a GENUINE constraint, not free.
A collapsing log-hash (constant `LH`) is NOT injective once two distinct receipt chains exist — so a
prover CANNOT supply `hLog` for a degenerate `LH`, and the seam equation `logDecodeChain_frame_continuous`
produces is a REAL receipt-chain equality, not a trivial `True`. (Mirrors the Poseidon CR set's own
non-vacuity: a `+`-fold satisfies none of the injectivity carriers.) -/

/-- A collapsing log-hash CANNOT satisfy `logHashInjective` once two distinct receipt logs exist: the
carrier is a genuine non-trivial constraint (the don't-launder-vacuity tooth). Witnessed by the empty
log vs. any one-receipt log (`[tr]`) — distinct (different lengths), yet both hash to `0`. -/
example (tr : Turn) : ¬ logHashInjective (fun _ : List Turn => (0 : ℤ)) := by
  intro hinj
  have : ([] : List Turn) = [tr] := hinj [] [tr] rfl
  exact (by simp : ([] : List Turn) ≠ [tr]) this

/-- The log seam tooth is LOAD-BEARING: under a genuinely injective `LH`, a published log seam forces
two SEPARATELY-NAMED boundary receipt chains EQUAL. Here `a`'s post and `b`'s pre are arbitrary distinct
states; equal published log commitments at the seam (`LH a'.log = LH b.log`) pin `a'.log = b.log` — a
non-trivial cross-state equality the derivation produces (not a tautology). -/
example (LH : List Turn → ℤ) (hLog : logHashInjective LH)
    (a a' b b' : RecChainedState) (ap aq bp bq : ℤ)
    (hda : LogDecode LH ap aq a a') (hdb : LogDecode LH bp bq b b')
    (hseam : aq = bp) :
    a'.log = b.log :=
  logDecodeChain_frame_continuous LH (Dregg2.Circuit.LogCommitRegrounded.noLogColl_of_inj hLog) hda hdb hseam

#assert_axioms LogDecode
#assert_axioms logDecode_faithful
#assert_axioms logDecodeChain_frame_continuous
#assert_axioms turnDecodeChainLog_seam_log_derived
#assert_axioms turnDecodeChainLog_seam_full_derived
#assert_axioms turnDecodeChainLog_rejects_forged_log

#assert_axioms CommitSurface.commit_binds_or_collides
#assert_axioms CommitSurface.commit_binds_of_noColl
#assert_axioms CommitSurface.noCommitColl_diag
#assert_axioms CommitSurface.orBreak_stateBreak_iff_True
#assert_axioms CommitSurface.perInstance_sharper_than_orBreak
#assert_axioms noSeamCommitColl_of_forall
-- The ported engine must not route back through the four deleted injectivity floors.
#assert_not_depends_on Dregg2.Circuit.CircuitSoundness.CommitSurface.commit_binds_or_collides
  [Dregg2.Circuit.StateCommit.cellLeafInjective, Dregg2.Circuit.StateCommit.compressInjective,
   Dregg2.Circuit.StateCommit.compressNInjective,
   Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]
#assert_axioms stateDecodeChain_frame_continuous
#assert_axioms lightclient_unfoolable
#assert_axioms verifyBatch_accept_iff
#assert_axioms verifyBatch_rejects_foreign_key
#assert_axioms verifyBatch_cfgKey_accept_iff
#assert_axioms verifyBatch_separates_keys
#assert_axioms starkSound_of_foreign_key
#assert_axioms starkSound_iff_at_cfgKey
#assert_axioms lightclient_turn_unfoolable
#assert_axioms turnDecodeChain_seam_kernel_derived
#assert_axioms turnDecodeChain_refines_turnSpec
#assert_axioms turnDecodeChain_refines_turnSpec_gen
#assert_axioms turnDecodeChain_endpoints_commit
#assert_axioms lightclient_turn_unfoolable_forest

end Dregg2.Circuit.CircuitSoundness
