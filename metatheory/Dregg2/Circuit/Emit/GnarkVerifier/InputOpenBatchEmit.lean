/-
# Dregg2.Circuit.Emit.GnarkVerifier.InputOpenBatchEmit — the REAL multi-height MMCS batch
tree opening (`verifyOpenInputBatchNative`) as a LEAN-AUTHORED, EMITTED R1CS, with a
∀-refinement theorem.

SUBSTRATE, said out loud: **this is Lean-authored AIR/R1CS.** Every constraint below is
EMITTED from a Lean builder over the `R1csFr` foundation and the committed `Poseidon2Fr`
permutation model; nothing here is hand-written in Go/Rust. The deployed
`chain/gnark/stark_open_input.go` (`verifyOpenInputBatchNative`, lines 334-391) +
`chain/gnark/stark_open_input_ref.go` (`openInputBatchRootRef`, the host reference twin)
are the pinned REFERENCE the emission is checked against (same tallest-first height
classes, same `hashGroup` MultiField sponge over each class's concatenated rows, same
injected class-hash compressions, same arity-2 path), not the source of the constraints.

WHAT `InputOpenEmit` MISSED — the single-leaf template. `InputOpenEmit.inputOpenCircuit`
hashes ONE row group into ONE leaf and ladders a plain depth-`d` path to the root. The
DEPLOYED input-open opening is a MULTI-HEIGHT MMCS BATCH TREE (mmcs.rs:1052-1180): a query
opens matrices at several LDE heights (e.g. per-round log-heights {19,18,12,3}); the
matrices are sorted tallest-first into HEIGHT CLASSES; the leaf digest is the MultiField
sponge over the concatenation of ALL rows at the max height; the walk is one arity-2
`Poseidon2Bn254Compress` per level steered by the query bit; and — the structural piece the
single-leaf template lacks — when the walk descends to a height that carries MORE matrices,
their row hash is INJECTED via an extra compression `digest = C(digest, hashGroup(class))`
that consumes NO path node and NO index bit (mmcs.rs:1146-1167). The final digest is the
committed input root.

The multi-block sponge machinery (`multiFieldHashRef`/`multiFieldHashW`, ∀-width) already
exists in `InputOpenEmit`; what was absent is the RIGHT SERIALIZATION — a per-class leaf
hash + the injected-compression-interleaved batch walk. This module supplies it.

Deliverables (genuine ∀-theorems, not `#guard` samples):

  * **`leafHash_refines`** — the per-WIDTH (width-parametric) MMCS leaf-hash template
    (`hashGroup` of one height class): rows-in → leaf-out, a ReplayTemplate boundary with
    NO `select`. For every row list, the honest witness satisfies the emitted template IFF
    the claimed leaf is `multiFieldHashRef` of the rows.
  * **`inputOpenBatch_refines`** — for every `groupRows : List (List Fr)` (the concatenated
    rows per height class, tallest first), `root sibs bits` and `injMask` (the compile-time
    class-injection schedule): the emitted multi-height batch circuit, under the honest
    witness, is satisfied IFF the injection-interleaved batch walk over the per-class leaf
    hashes reproduces the claimed input root — the deployed `verifyOpenInputBatchNative`
    check. Both polarities (`_rejects`/`_accepts`): any tamper (a changed opened row limb —
    moving a class leaf hash — a wrong path node, a flipped bit, a corrupted root) that
    moves the recomputed root makes `gHolds` FALSE.
  * **`inputOpenBatch_refines_emitted`** — the same iff at the emitted wire form, via the
    proven `emit_faithful` round trip.
  * **`inputOpenBatch_sound`** — the adversarial face: ANY witness satisfying the circuit
    has its root variable equal to the batch-walk recomputation from its own row/path/bit
    variables (no honest-fill hypothesis).

`#guard` KAT: the batch walk reproduces the REAL apex-shrink fixture input root
(`chain/gnark/fixtures/apex_shrink_fri_real.json`, query 0, input round 1: height classes
{19,18,12,3}, root `0x0800ca…`, computed by `openInputBatchRootRef` in
`chain/gnark/stark_open_input_ref.go`) BIT-EXACTLY, plus tamper-rejects.
-/
import Dregg2.Circuit.Emit.GnarkVerifier.InputOpenEmit

namespace Dregg2.Circuit.Emit.GnarkVerifier.InputOpenBatch

open Dregg2.Circuit.R1csFr
open Dregg2.Circuit.Poseidon2Fr (permute compress St BuilderM)
open Dregg2.Circuit.Emit.GnarkVerifier.Merkle
open Dregg2.Circuit.Emit.GnarkVerifier.InputOpen

-- The heavy builders are spec-closed downstream; keep their monadic values OPAQUE so no
-- `whnf` ever reduces the Poseidon2 permutation while threading/comparing the sponge and
-- path builders (the `MerkleEmit`/`InputOpenEmit` discipline, which used `local
-- irreducible` — that attribute does not cross the module boundary, so re-assert it here).
attribute [local irreducible] compressW multiFieldHashW

/-! ## §1 A generic define-chain run helper for the sponge leaf hash. -/

/-- The leaf-hash builder run at any start counter: its emitted define-chain + forced
denotation is `multiFieldHashRef` over the row values. A thin repackaging of the committed
`multiFieldHashW_emits` at the concrete start state. -/
theorem hashRun_props (vals : List Wire) (start : ℕ)
    (hvals : ∀ w ∈ vals, wBelow w start) :
    ∃ n1, DefChain start (multiFieldHashW vals (start, [])).2.2 n1
      ∧ wBelow (multiFieldHashW vals (start, [])).1 n1
      ∧ (multiFieldHashW vals (start, [])).2.1 = n1
      ∧ ∀ a, (∀ p ∈ (multiFieldHashW vals (start, [])).2.2, p.1.eval a = p.2.eval a) →
          (multiFieldHashW vals (start, [])).1.eval a
            = multiFieldHashRef (vals.map (Wire.eval · a)) := by
  obtain ⟨Lw, n1, chain, hrun, hdc, hbleaf, hforce⟩ :=
    multiFieldHashW_emits vals hvals start [] le_rfl
  have heq : multiFieldHashW vals (start, []) = (Lw, (n1, chain)) := by
    rw [hrun, List.nil_append]
  rw [heq]
  exact ⟨n1, hdc, hbleaf, rfl, fun a ha => hforce a ha⟩

/-! ## §2 The per-WIDTH MMCS leaf-hash template (deliverable 1) — `hashGroup` of one class.

Layout: `var 0 … var (W-1)` = the `W` opened row limbs of the height class; `var W` = the
claimed leaf digest; sponge internals mint from `W+1`. The circuit is the leaf-hash
define-chain plus the `leaf = var W` pin. A ReplayTemplate boundary (bind the `W` rows,
SOLVE the leaf) — the sponge is pure pack + permute, so there is NO `select` in it. -/

/-- The leaf-hash builder run at the leaf-template layout (internals from `W+1`). -/
def leafHashRun (W : ℕ) : Wire × (ℕ × List (Wire × Wire)) :=
  multiFieldHashW (rowVars W) (W + 1, [])

/-- **The leaf-hash template circuit** — the sponge define-chain + the `leaf = var W` pin. -/
def leafHashCircuit (W : ℕ) : Circuit :=
  ⟨(leafHashRun W).2.2 ++ [((leafHashRun W).1, Wire.var W)]⟩

/-- **`leafHashData`** — the emission package the Go side replays (`ReplayTemplate`): the `W`
row boundary variables (bound prefix), the leaf output (solved suffix), and the gadget
record naming the deployed `hashGroup` MultiField sponge. -/
def leafHashData (W : ℕ) : GnarkCircuitData :=
  { name         := "mmcs_leaf_hash_multifield_v1"
    publicInputs := (List.range W).map (fun i => ("row" ++ toString i, i)) ++ [("leaf", W)]
    gadgets      := [⟨"MultiField32LeafHash", [W]⟩]
    circuit      := leafHashCircuit W }

/-- The interface fill: rows at `0…W-1`, claimed leaf at `W`. Internals solved. -/
def leafHashInAsg (W : ℕ) (rows : List Fr) (leaf : Fr) : Assignment := fun v =>
  if v < W then rows.getD v 0 else if v = W then leaf else 0

/-- **The honest witness** — interface plus solved sponge internals. -/
def leafHashAsg (W : ℕ) (rows : List Fr) (leaf : Fr) : Assignment :=
  solveChain (leafHashInAsg W rows leaf) (leafHashRun W).2.2

theorem leafHashInAsg_row (W : ℕ) (rows : List Fr) (leaf : Fr) (v : ℕ) (hv : v < W) :
    leafHashInAsg W rows leaf v = rows.getD v 0 := by
  simp only [leafHashInAsg, if_pos hv]

theorem leafHashInAsg_leaf (W : ℕ) (rows : List Fr) (leaf : Fr) :
    leafHashInAsg W rows leaf W = leaf := by
  simp only [leafHashInAsg, lt_irrefl, if_false, if_true]

/-- The leaf-hash run's define-chain (from `W+1`) + forced denotation. -/
theorem leafHashRun_props (W : ℕ) :
    ∃ n1, DefChain (W + 1) (leafHashRun W).2.2 n1
      ∧ (leafHashRun W).2.1 = n1
      ∧ ∀ a, (∀ p ∈ (leafHashRun W).2.2, p.1.eval a = p.2.eval a) →
          (leafHashRun W).1.eval a = multiFieldHashRef ((rowVars W).map (Wire.eval · a)) := by
  have hrows : ∀ w ∈ rowVars W, wBelow w (W + 1) := by
    intro w hw
    simp only [rowVars, List.mem_map, List.mem_range] at hw
    obtain ⟨i, hi, rfl⟩ := hw
    exact Nat.lt_of_lt_of_le hi (by omega)
  obtain ⟨n1, hdc, _, hn1, hforce⟩ := hashRun_props (rowVars W) (W + 1) hrows
  exact ⟨n1, hdc, hn1, hforce⟩

/-- **The leaf-hash frontend refinement.** -/
theorem leafHash_frontend (rows : List Fr) (leaf : Fr) :
    (leafHashCircuit rows.length).satisfied (leafHashAsg rows.length rows leaf)
      ↔ leaf = multiFieldHashRef rows := by
  set W := rows.length with hW
  set a := leafHashAsg W rows leaf with ha
  obtain ⟨n1, hdc, _, hforce⟩ := leafHashRun_props W
  have hbelow : ∀ v, v < W + 1 → a v = leafHashInAsg W rows leaf v := fun v hv =>
    solveChain_agree_below (leafHashRun W).2.2 (leafHashInAsg W rows leaf) hdc v hv
  have hnew : ∀ p ∈ (leafHashRun W).2.2, p.1.eval a = p.2.eval a :=
    solveChain_sat (leafHashRun W).2.2 (leafHashInAsg W rows leaf) hdc
  have hrowsEq : (rowVars W).map (Wire.eval · a) = rows := by
    have e2 : (rowVars W).map (Wire.eval · a) = (List.range W).map (fun v => rows.getD v 0) := by
      rw [rowVars, List.map_map]
      apply List.map_congr_left
      intro v hv
      rw [List.mem_range] at hv
      show a v = rows.getD v 0
      rw [hbelow v (by omega), leafHashInAsg_row W rows leaf v hv]
    rw [e2, hW]; exact map_getD_range rows
  have hleaf : a W = leaf := by rw [hbelow W (by omega)]; exact leafHashInAsg_leaf W rows leaf
  have hval : (leafHashRun W).1.eval a = multiFieldHashRef rows := by
    rw [hforce a hnew, hrowsEq]
  have key : ((leafHashRun W).1.eval a = (Wire.var W).eval a) ↔ (leaf = multiFieldHashRef rows) := by
    rw [hval]
    show (multiFieldHashRef rows = a W) ↔ (leaf = multiFieldHashRef rows)
    rw [hleaf]
    exact ⟨Eq.symm, Eq.symm⟩
  show (∀ p ∈ (leafHashRun W).2.2 ++ [((leafHashRun W).1, Wire.var W)],
      p.1.eval a = p.2.eval a) ↔ _
  rw [List.forall_mem_append, List.forall_mem_singleton]
  constructor
  · rintro ⟨_, hr⟩; exact key.mp hr
  · intro hr; exact ⟨hnew, key.mpr hr⟩

/-- **`leafHash_refines`** — the leaf-hash ReplayTemplate refinement at the R1CS level. -/
theorem leafHash_refines (rows : List Fr) (leaf : Fr) :
    Dregg2.Circuit.Emit.GnarkVerifier.gHolds (leafHashData rows.length)
        (leafHashAsg rows.length rows leaf)
      ↔ leaf = multiFieldHashRef rows := by
  unfold Dregg2.Circuit.Emit.GnarkVerifier.gHolds
  rw [← R1csFr.gHolds]
  exact leafHash_frontend rows leaf

theorem leafHash_rejects (rows : List Fr) (leaf : Fr) (h : leaf ≠ multiFieldHashRef rows) :
    ¬ Dregg2.Circuit.Emit.GnarkVerifier.gHolds (leafHashData rows.length)
        (leafHashAsg rows.length rows leaf) :=
  fun hg => h ((leafHash_refines rows leaf).mp hg)

theorem leafHash_accepts (rows : List Fr) :
    Dregg2.Circuit.Emit.GnarkVerifier.gHolds (leafHashData rows.length)
      (leafHashAsg rows.length rows (multiFieldHashRef rows)) :=
  (leafHash_refines rows _).mpr rfl

theorem leafHash_refines_emitted (rows : List Fr) (leaf : Fr) :
    Dregg2.Circuit.Emit.GnarkVerifier.satisfiedEmitted
        (Dregg2.Circuit.Emit.GnarkVerifier.emit (leafHashData rows.length))
        (leafHashAsg rows.length rows leaf)
      ↔ leaf = multiFieldHashRef rows :=
  (Dregg2.Circuit.Emit.GnarkVerifier.emit_faithful (leafHashData rows.length)
      (leafHashAsg rows.length rows leaf)).symm.trans (leafHash_refines rows leaf)

#assert_axioms leafHash_refines
#assert_axioms leafHash_refines_emitted

/-! ## §3 The semantic reference — the injection-interleaved batch walk.

`bStep` is one level of `openInputBatchRootRef`: the arity-2 compression steered by the
query bit (`b=false` ⇒ digest is the LEFT child, matching `reduced&1==0 ⇒ C(digest, sib)`),
followed — at an injection level — by the extra class-hash compression `C(node, hashGroup)`.
`batchRefRoot` folds it over the level list woven from the path pairs, the injection mask,
and the lower height classes' rows (hashed by `multiFieldHashRef`). -/

/-- One reference batch-walk level: the bit-steered arity-2 compression, then (at an
injection level) the extra class-hash compression `C(node, multiFieldHashRef grp)`. -/
def bStep (nd sib : Fr) (b : Bool) (inj : Option (List Fr)) : Fr :=
  match inj with
  | none     => (if b then compress sib nd else compress nd sib)
  | some grp => compress (if b then compress sib nd else compress nd sib) (multiFieldHashRef grp)

/-- **The reference batch-tree walk** (`openInputBatchRootRef`): fold `bStep` over the path
`(sib, bit)` pairs, consuming a lower height class (`some g`) at each masked step. Recurses
STRUCTURALLY on the path list (so it reduces definitionally); the mask/class dispatch is a
non-recursive nested match. -/
def batchRefRoot : Fr → List (Fr × Bool) → List Bool → List (List Fr) → Fr
  | nd, [], _, _ => nd
  | nd, (sib, b) :: ps, ms, gss =>
      match ms, gss with
      | true :: ms', g :: gs' => batchRefRoot (bStep nd sib b (some g)) ps ms' gs'
      | true :: ms', [] => batchRefRoot (bStep nd sib b none) ps ms' []
      | false :: ms', gs => batchRefRoot (bStep nd sib b none) ps ms' gs
      | [], gs => batchRefRoot (bStep nd sib b none) ps [] gs

/-- The circuit-forced level step (two `Select` muxes via `stepFr`, then optional
class-hash compression). On boolean bits this is `bStep` (`batchStepFrMux_encB`). -/
def batchStepFrMux (nd sib bitF : Fr) (inj : Option (List Fr)) : Fr :=
  match inj with
  | none     => stepFr nd (sib, bitF)
  | some grp => compress (stepFr nd (sib, bitF)) (multiFieldHashRef grp)

theorem batchStepFrMux_encB (nd sib : Fr) (b : Bool) (inj : Option (List Fr)) :
    batchStepFrMux nd sib (encB b) inj = bStep nd sib b inj := by
  cases inj with
  | none => simp only [batchStepFrMux, bStep, stepFr_encB]
  | some grp => simp only [batchStepFrMux, bStep, stepFr_encB]

/-! ## §4 A generic wire-accumulator `foldlM` emit lemma (element type `β`). -/

/-- The `emitsW_walk` device of `MerkleEmit`, generalized to an arbitrary element type `β`
(here the woven level `Wire × Wire × Option (List Wire)`). The step `stepB` is kept
ABSTRACT so the proof never unifies against the concrete (irreducible) `compressW` /
`multiFieldHashW` monadic value. -/
theorem emitsW_walkB {β : Type} {belE : β → ℕ → Prop}
    {stepB : Wire → β → BuilderM Wire}
    {semF : Fr → β → Assignment → Fr}
    (belE_mono : ∀ p i j, belE p i → i ≤ j → belE p j)
    (hstepB : ∀ (nd : Wire) (p : β) (bd : ℕ), wBelow nd bd → belE p bd →
      EmitsW (stepB nd p) bd (fun a => semF (nd.eval a) p a)) :
    ∀ (l : List β) (node : Wire) {bound : ℕ},
      wBelow node bound → (∀ p ∈ l, belE p bound) →
      EmitsW (l.foldlM stepB node) bound
        (fun a => l.foldl (fun nd p => semF nd p a) (node.eval a)) := by
  intro l
  induction l with
  | nil =>
      intro node bound hn _
      rw [List.foldlM_nil]
      exact (Emits.pure wBelow_mono' node hn).congr fun a => by simp
  | cons hd tl ih =>
      intro node bound hn hps
      rw [List.foldlM_cons]
      exact (Emits.bind
        (g := fun v a => tl.foldl (fun nd p => semF nd p a) v)
        (hstepB node hd bound hn (hps hd List.mem_cons_self))
        (fun parent b hb hparent =>
          ih parent hparent
            (fun p hp => belE_mono p bound b (hps p (List.mem_cons_of_mem _ hp)) hb))).congr
        fun a => by rw [List.foldl_cons]

/-! ## §5 The batch-walk builder step + its emit spec. -/

/-- One woven level's bound predicate: the sibling and bit wires, and (at an injection
level) every wire of the injected class's row block, mention only variables `< n`. -/
def belLvl (lvl : Wire × Wire × Option (List Wire)) (n : ℕ) : Prop :=
  wBelow lvl.1 n ∧ wBelow lvl.2.1 n ∧ (∀ grp ∈ lvl.2.2, ∀ w ∈ grp, wBelow w n)

theorem belLvl_mono (p : Wire × Wire × Option (List Wire)) (i j : ℕ)
    (h : belLvl p i) (hij : i ≤ j) : belLvl p j :=
  ⟨wBelow_mono h.1 hij, wBelow_mono h.2.1 hij,
    fun grp hgrp w hw => wBelow_mono (h.2.2 grp hgrp w hw) hij⟩

/-- The batch-walk builder step: the arity-2 bit-steered compression (`compressW` over two
`Select` muxes) then, at an injection level, the class leaf hash (`multiFieldHashW`) and its
compression into the running digest. Mirrors `verifyOpenInputBatchNative`'s loop body. -/
def batchWalkStepW (nd : Wire) (lvl : Wire × Wire × Option (List Wire)) : BuilderM Wire :=
  compressW (.select lvl.2.1 lvl.1 nd) (.select lvl.2.1 nd lvl.1) >>= fun node =>
    match lvl.2.2 with
    | none     => pure node
    | some grp => multiFieldHashW grp >>= fun g => compressW node g

/-- **The batch-walk step spec** — under any assignment satisfying its emitted asserts, the
step denotes `batchStepFrMux` of the evaluated level. -/
theorem batchWalkStepW_emits (nd : Wire) (lvl : Wire × Wire × Option (List Wire)) {bd : ℕ}
    (hnd : wBelow nd bd) (hlvl : belLvl lvl bd) :
    EmitsW (batchWalkStepW nd lvl) bd
      (fun a => batchStepFrMux (nd.eval a) (lvl.1.eval a) (lvl.2.1.eval a)
        (lvl.2.2.map (fun ws => ws.map (Wire.eval · a)))) := by
  obtain ⟨sib, bit, injOpt⟩ := lvl
  obtain ⟨hsib, hbit, hgrp⟩ := hlvl
  have hstep0 : EmitsW (compressW (.select bit sib nd) (.select bit nd sib)) bd
      (fun a => stepFr (nd.eval a) (sib.eval a, bit.eval a)) :=
    (compressW_emits (.select bit sib nd) (.select bit nd sib)
      ⟨hbit, hsib, hnd⟩ ⟨hbit, hnd, hsib⟩).congr fun a => stepFr_select nd sib bit a
  cases injOpt with
  | none =>
      refine (Emits.bind (g := fun v _ => v) hstep0
        (fun node b hb hnode => (Emits.pure wBelow_mono' node hnode).congr fun a => rfl)).congr
        fun a => ?_
      simp only [Option.map_none, batchStepFrMux]
  | some grp =>
      have hgrp' : ∀ w ∈ grp, wBelow w bd := hgrp grp rfl
      refine (Emits.bind
        (g := fun v a => compress v (multiFieldHashRef (grp.map (Wire.eval · a)))) hstep0
        (fun node b hb hnode =>
          Emits.bind (g := fun v a => compress (node.eval a) v)
            (multiFieldHashW_emits grp (fun w hw => wBelow_mono (hgrp' w hw) hb))
            (fun gW b' hb' hgW =>
              (compressW_emits node gW (wBelow_mono hnode hb') hgW).congr fun a => rfl))).congr
        fun a => ?_
      simp only [Option.map_some, batchStepFrMux]

/-! ## §6 The row-limb layout: contiguous per-class blocks + the honest-fill routing. -/

/-- Route a variable in the contiguous row region to its height class's row value:
class blocks are laid out in tallest-first batch order from `base`; `v` reads block `j`'s
local slot when it falls inside it. The honest-fill value of every row variable. -/
def lookupBlocks : ℕ → List (List Fr) → ℕ → Fr
  | _, [], _ => 0
  | base, g :: gs, v =>
      if v < base + g.length then g.getD (v - base) 0 else lookupBlocks (base + g.length) gs v

/-- The per-class row-limb WIRE lists: class `j` (width `w`) is the `w` variables from its
threaded base. Class 0 (from `base = 0`) is exactly `rowVars w`. -/
def groupVarsFrom (base : ℕ) : List ℕ → List (List Wire)
  | [] => []
  | w :: ws => ((List.range w).map (fun i => Wire.var (base + i))) :: groupVarsFrom (base + w) ws

/-- Under the honest fill (`a v = lookupBlocks base gss v` over the class region), the
per-class wire lists evaluate to the class rows. One flatten-slice induction. -/
theorem groupVarsFrom_eval (a : Assignment) :
    ∀ (gss : List (List Fr)) (base : ℕ),
      (∀ v, base ≤ v → v < base + gss.flatten.length → a v = lookupBlocks base gss v) →
      (groupVarsFrom base (gss.map List.length)).map (fun ws => ws.map (Wire.eval · a)) = gss := by
  intro gss
  induction gss with
  | nil => intro base _; rfl
  | cons g gs ih =>
      intro base hfill
      have hflat : (g :: gs).flatten.length = g.length + gs.flatten.length := by
        simp [List.flatten_cons]
      have hhead : (((List.range g.length).map (fun i => Wire.var (base + i))).map (Wire.eval · a)) = g := by
        rw [List.map_map]
        have hcongr : ((List.range g.length).map ((fun w => Wire.eval w a) ∘ fun i => Wire.var (base + i)))
            = (List.range g.length).map (fun i => g.getD i 0) := by
          apply List.map_congr_left
          intro i hi
          rw [List.mem_range] at hi
          show a (base + i) = g.getD i 0
          rw [hfill (base + i) (by omega) (by rw [hflat]; omega)]
          simp only [lookupBlocks]
          rw [if_pos (by omega)]
          congr 1; omega
        rw [hcongr]; exact map_getD_range g
      have htail : ∀ v, base + g.length ≤ v → v < (base + g.length) + gs.flatten.length →
          a v = lookupBlocks (base + g.length) gs v := by
        intro v hv1 hv2
        rw [hfill v (by omega) (by rw [hflat]; omega)]
        simp only [lookupBlocks]
        rw [if_neg (by omega)]
      have hgv : groupVarsFrom base ((g :: gs).map List.length)
          = ((List.range g.length).map (fun i => Wire.var (base + i)))
            :: groupVarsFrom (base + g.length) (gs.map List.length) := by
        simp only [List.map_cons, groupVarsFrom]
      rw [hgv, List.map_cons, hhead, ih (base + g.length) htail]

/-! ## §7 Weaving the class injections into the path level list. -/

/-- The circuit level list: each path `(sib, bit)` pair, tagged (at a masked step) with the
next lower class's row-limb WIRE block to inject. Mirrors `openInputBatchRootRef`'s loop:
`injMask` marks the steps at which the walk reaches a class-carrying height, and the classes
(`gvs` = the lower classes' wire blocks) are consumed in that order. -/
def weaveVars : List (Wire × Wire) → List Bool → List (List Wire)
    → List (Wire × Wire × Option (List Wire))
  | [], _, _ => []
  | (sib, bit) :: ps, ms, gvs =>
      match ms, gvs with
      | true :: ms', g :: gs' => (sib, bit, some g) :: weaveVars ps ms' gs'
      | true :: ms', [] => (sib, bit, none) :: weaveVars ps ms' []
      | false :: ms', gs => (sib, bit, none) :: weaveVars ps ms' gs
      | [], gs => (sib, bit, none) :: weaveVars ps [] gs

/-- Every woven level's wires stay below `bound` when the path pairs and class blocks do. -/
theorem weaveVars_below (bound : ℕ) :
    ∀ (ps : List (Wire × Wire)) (ms : List Bool) (gvs : List (List Wire)),
      (∀ p ∈ ps, wBelow p.1 bound ∧ wBelow p.2 bound) →
      (∀ g ∈ gvs, ∀ w ∈ g, wBelow w bound) →
      ∀ lvl ∈ weaveVars ps ms gvs, belLvl lvl bound := by
  intro ps
  induction ps with
  | nil => intro ms gvs _ _ lvl hlvl; simp [weaveVars] at hlvl
  | cons p ps ih =>
      obtain ⟨sib, bit⟩ := p
      intro ms gvs hps hgvs lvl hlvl
      have hsb : wBelow sib bound ∧ wBelow bit bound := hps _ List.mem_cons_self
      have hnone : belLvl (sib, bit, none) bound := ⟨hsb.1, hsb.2, by intro g hg; simp at hg⟩
      have hps' : ∀ p ∈ ps, wBelow p.1 bound ∧ wBelow p.2 bound :=
        fun p hp => hps p (List.mem_cons_of_mem _ hp)
      cases ms with
      | nil =>
          simp only [weaveVars] at hlvl
          rcases List.mem_cons.mp hlvl with rfl | hlvl'
          · exact hnone
          · exact ih [] gvs hps' hgvs lvl hlvl'
      | cons m ms =>
          cases m with
          | false =>
              simp only [weaveVars] at hlvl
              rcases List.mem_cons.mp hlvl with rfl | hlvl'
              · exact hnone
              · exact ih ms gvs hps' hgvs lvl hlvl'
          | true =>
              cases gvs with
              | nil =>
                  simp only [weaveVars] at hlvl
                  rcases List.mem_cons.mp hlvl with rfl | hlvl'
                  · exact hnone
                  · exact ih ms [] hps' (by intro g hg; simp at hg) lvl hlvl'
              | cons gw gvs' =>
                  simp only [weaveVars] at hlvl
                  rcases List.mem_cons.mp hlvl with rfl | hlvl'
                  · refine ⟨hsb.1, hsb.2, ?_⟩
                    intro grp hgrp w hw
                    rw [Option.mem_some_iff] at hgrp
                    subst hgrp
                    exact hgvs gw List.mem_cons_self w hw
                  · exact ih ms gvs' hps'
                      (fun g hg => hgvs g (List.mem_cons_of_mem _ hg)) lvl hlvl'

/-! ## §8 THE CRUX — the woven builder walk denotes the reference batch root. -/

-- Their equation lemmas are established (`batchStepFrMux_encB`, §5); keep the level-step and
-- the reference step OPAQUE so `isDefEq`, while reducing the woven `foldl` head against the
-- crux `show`, never unfolds them into `stepFr`/`compress`/`permute` and reduces the
-- Poseidon2 permutation over field elements (a `whnf` blowup on the accumulator).
attribute [local irreducible] bStep batchStepFrMux

/-- Under the honest fill (path pairs at the canonical layout evaluate to `sibs`/`encB bits`,
class wire blocks evaluate to `gss`), the foldl of `batchStepFrMux` over the woven level
list reproduces `batchRefRoot` — the injection-interleaved reference batch walk. -/
theorem foldl_weave (a : Assignment) :
    ∀ (sibs : List Fr) (base : ℕ) (bits : List Bool) (ms : List Bool)
      (gvs : List (List Wire)) (gss : List (List Fr)) (nd : Fr),
      sibs.length = bits.length →
      (∀ i, i < sibs.length → a (base + 2 * i) = sibs.getD i 0) →
      (∀ i, i < bits.length → a (base + 2 * i + 1) = encB (bits.getD i false)) →
      gvs.map (fun ws => ws.map (Wire.eval · a)) = gss →
      (weaveVars (pairWiresFrom base sibs.length) ms gvs).foldl
          (fun n lvl => batchStepFrMux n (lvl.1.eval a) (lvl.2.1.eval a)
            (lvl.2.2.map (fun ws => ws.map (Wire.eval · a)))) nd
        = batchRefRoot nd (sibs.zip bits) ms gss := by
  intro sibs
  induction sibs with
  | nil =>
      intro base bits ms gvs gss nd hlen _ _ _
      cases bits with
      | nil => rfl
      | cons b bs => simp at hlen
  | cons sib sibs' ih =>
      intro base bits ms gvs gss nd hlen hsib hbit hgvs
      cases bits with
      | nil => simp at hlen
      | cons b bits' =>
          have hlen' : sibs'.length = bits'.length := by simpa using hlen
          have hev1 : (Wire.var base).eval a = sib := by
            have h := hsib 0 (by simp); simpa [Wire.eval] using h
          have hev2 : (Wire.var (base + 1)).eval a = encB b := by
            have h := hbit 0 (by simp); simpa [Wire.eval] using h
          have hsib' : ∀ i, i < sibs'.length → a (base + 2 + 2 * i) = sibs'.getD i 0 := by
            intro i hi
            have h := hsib (i + 1) (by simp only [List.length_cons]; omega)
            rw [List.getD_cons_succ] at h
            rw [show base + 2 + 2 * i = base + 2 * (i + 1) from by ring]; exact h
          have hbit' : ∀ i, i < bits'.length → a (base + 2 + 2 * i + 1) = encB (bits'.getD i false) := by
            intro i hi
            have h := hbit (i + 1) (by simp only [List.length_cons]; omega)
            rw [List.getD_cons_succ] at h
            rw [show base + 2 + 2 * i + 1 = base + 2 * (i + 1) + 1 from by ring]; exact h
          have hpw : pairWiresFrom base (sib :: sibs').length
              = (Wire.var base, Wire.var (base + 1)) :: pairWiresFrom (base + 2) sibs'.length := by
            show pairWiresFrom base (sibs'.length + 1) = _
            rw [pairWiresFrom]
          rw [hpw, List.zip_cons_cons]
          cases ms with
          | nil =>
              show (weaveVars (pairWiresFrom (base + 2) sibs'.length) [] gvs).foldl
                  (fun n lvl => batchStepFrMux n (lvl.1.eval a) (lvl.2.1.eval a)
                    (lvl.2.2.map (fun ws => ws.map (Wire.eval · a))))
                  (batchStepFrMux nd ((Wire.var base).eval a) ((Wire.var (base + 1)).eval a) none)
                = batchRefRoot (bStep nd sib b none) (sibs'.zip bits') [] gss
              rw [hev1, hev2, batchStepFrMux_encB]
              exact ih (base + 2) bits' [] gvs gss (bStep nd sib b none) hlen' hsib' hbit' hgvs
          | cons m ms =>
              cases m with
              | false =>
                  show (weaveVars (pairWiresFrom (base + 2) sibs'.length) ms gvs).foldl
                      (fun n lvl => batchStepFrMux n (lvl.1.eval a) (lvl.2.1.eval a)
                        (lvl.2.2.map (fun ws => ws.map (Wire.eval · a))))
                      (batchStepFrMux nd ((Wire.var base).eval a) ((Wire.var (base + 1)).eval a) none)
                    = batchRefRoot (bStep nd sib b none) (sibs'.zip bits') ms gss
                  rw [hev1, hev2, batchStepFrMux_encB]
                  exact ih (base + 2) bits' ms gvs gss (bStep nd sib b none) hlen' hsib' hbit' hgvs
              | true =>
                  cases gvs with
                  | nil =>
                      subst hgvs
                      show (weaveVars (pairWiresFrom (base + 2) sibs'.length) ms []).foldl
                          (fun n lvl => batchStepFrMux n (lvl.1.eval a) (lvl.2.1.eval a)
                            (lvl.2.2.map (fun ws => ws.map (Wire.eval · a))))
                          (batchStepFrMux nd ((Wire.var base).eval a) ((Wire.var (base + 1)).eval a) none)
                        = batchRefRoot (bStep nd sib b none) (sibs'.zip bits') ms []
                      rw [hev1, hev2, batchStepFrMux_encB]
                      exact ih (base + 2) bits' ms [] [] (bStep nd sib b none) hlen' hsib' hbit' rfl
                  | cons gw gvs' =>
                      have hgss : gss = (gw.map (Wire.eval · a)) :: gvs'.map (fun ws => ws.map (Wire.eval · a)) := by
                        rw [← hgvs, List.map_cons]
                      subst hgss
                      show (weaveVars (pairWiresFrom (base + 2) sibs'.length) ms gvs').foldl
                          (fun n lvl => batchStepFrMux n (lvl.1.eval a) (lvl.2.1.eval a)
                            (lvl.2.2.map (fun ws => ws.map (Wire.eval · a))))
                          (batchStepFrMux nd ((Wire.var base).eval a) ((Wire.var (base + 1)).eval a)
                            (some (gw.map (Wire.eval · a))))
                        = batchRefRoot (bStep nd sib b (some (gw.map (Wire.eval · a))))
                            (sibs'.zip bits') ms (gvs'.map (fun ws => ws.map (Wire.eval · a)))
                      rw [hev1, hev2, batchStepFrMux_encB]
                      exact ih (base + 2) bits' ms gvs' (gvs'.map (fun ws => ws.map (Wire.eval · a)))
                        (bStep nd sib b (some (gw.map (Wire.eval · a)))) hlen' hsib' hbit' rfl

/-! ## §9 The composed multi-height batch circuit and its ∀-refinement.

Layout (all class row limbs first, so each class hash reads a clean contiguous block):
`var 0 … var (R-1)` = the row limbs, class `j`'s block at its cumulative offset (`R =
widths.sum`); `var R` = root; `var (R+1+2s)` = path node `s`, `var (R+1+2s+1)` = path bit
`s`; Poseidon internals mint from `R+1+2·maxLh`. The circuit is the per-level booleanity
asserts, the class-0 leaf hash, the injection-interleaved batch walk, and `finalDigest =
root`. -/

/-- Bounds for the per-class row-limb wire lists. -/
theorem groupVarsFrom_below (bound : ℕ) :
    ∀ (ws : List ℕ) (base : ℕ), base + ws.sum ≤ bound →
      ∀ g ∈ groupVarsFrom base ws, ∀ w ∈ g, wBelow w bound := by
  intro ws
  induction ws with
  | nil => intro base _ g hg; simp [groupVarsFrom] at hg
  | cons w0 ws ih =>
      intro base hbd g hg w hw
      simp only [groupVarsFrom, List.mem_cons] at hg
      rcases hg with rfl | hg'
      · simp only [List.mem_map, List.mem_range] at hw
        obtain ⟨i, hi, rfl⟩ := hw
        show base + i < bound
        rw [List.sum_cons] at hbd; omega
      · exact ih (base + w0) (by rw [List.sum_cons] at hbd; omega) g hg' w hw

/-- The class-0 leaf-hash builder run (internals mint past the whole layout). -/
def batchLeaf0Run (widths : List ℕ) (maxLh : ℕ) : Wire × (ℕ × List (Wire × Wire)) :=
  multiFieldHashW (rowVars (widths.headD 0)) (widths.sum + 1 + 2 * maxLh, [])

/-- The circuit level list: the path pairs woven with the lower classes' row-limb blocks. -/
def batchLevels (widths : List ℕ) (maxLh : ℕ) (injMask : List Bool) :
    List (Wire × Wire × Option (List Wire)) :=
  weaveVars (pairWiresFrom (widths.sum + 1) maxLh) injMask
    (groupVarsFrom (widths.headD 0) widths.tail)

/-- The injection-interleaved batch-walk builder. -/
def batchWalkW (node : Wire) (levels : List (Wire × Wire × Option (List Wire))) : BuilderM Wire :=
  levels.foldlM batchWalkStepW node

/-- The batch-walk run, from the counter the class-0 leaf hash ended at. -/
def batchWalkRun (widths : List ℕ) (maxLh : ℕ) (injMask : List Bool) :
    Wire × (ℕ × List (Wire × Wire)) :=
  batchWalkW (batchLeaf0Run widths maxLh).1 (batchLevels widths maxLh injMask)
    ((batchLeaf0Run widths maxLh).2.1, [])

/-- **The multi-height batch-opening circuit.** -/
def batchCircuit (widths : List ℕ) (maxLh : ℕ) (injMask : List Bool) : Circuit :=
  ⟨bitBoolFrom (widths.sum + 1) maxLh
    ++ ((batchLeaf0Run widths maxLh).2.2 ++ (batchWalkRun widths maxLh injMask).2.2)
    ++ [((batchWalkRun widths maxLh injMask).1, Wire.var widths.sum)]⟩

/-- The emission package for the depth-`maxLh`, class-shape-`widths`/`injMask` batch opening. -/
def batchData (widths : List ℕ) (maxLh : ℕ) (injMask : List Bool) : GnarkCircuitData :=
  { name         := "merkle_batch_bn254_input_open_v1"
    publicInputs := [("root", widths.sum)]
    gadgets      := [⟨"VerifyOpenInputBatchBn254", [widths.sum, maxLh]⟩]
    circuit      := batchCircuit widths maxLh injMask }

/-- The honest input fill: class rows routed by `lookupBlocks`, root at `R`, path nodes at
even offsets, path bits (as `0/1`) at odd offsets past `R`. Poseidon internals via
`solveChain`. -/
def batchInAsg (groupRows : List (List Fr)) (root : Fr) (sibs : List Fr) (bits : List Bool) :
    Assignment := fun v =>
  if v < groupRows.flatten.length then lookupBlocks 0 groupRows v
  else if v = groupRows.flatten.length then root
  else if (v - (groupRows.flatten.length + 1)) % 2 = 0 then
    sibs.getD ((v - (groupRows.flatten.length + 1)) / 2) 0
  else encB (bits.getD ((v - (groupRows.flatten.length + 1)) / 2) false)

/-- **The honest witness** — inputs plus the solved Poseidon internals of both runs. -/
def batchAsg (widths : List ℕ) (maxLh : ℕ) (injMask : List Bool)
    (groupRows : List (List Fr)) (root : Fr) (sibs : List Fr) (bits : List Bool) : Assignment :=
  solveChain (batchInAsg groupRows root sibs bits)
    ((batchLeaf0Run widths maxLh).2.2 ++ (batchWalkRun widths maxLh injMask).2.2)

theorem batchInAsg_row (groupRows : List (List Fr)) (root : Fr) (sibs : List Fr)
    (bits : List Bool) (v : ℕ) (hv : v < groupRows.flatten.length) :
    batchInAsg groupRows root sibs bits v = lookupBlocks 0 groupRows v := by
  simp only [batchInAsg, if_pos hv]

theorem batchInAsg_root (groupRows : List (List Fr)) (root : Fr) (sibs : List Fr)
    (bits : List Bool) : batchInAsg groupRows root sibs bits groupRows.flatten.length = root := by
  show (if groupRows.flatten.length < groupRows.flatten.length then
        lookupBlocks 0 groupRows groupRows.flatten.length
      else if groupRows.flatten.length = groupRows.flatten.length then root
      else if (groupRows.flatten.length - (groupRows.flatten.length + 1)) % 2 = 0 then
        sibs.getD ((groupRows.flatten.length - (groupRows.flatten.length + 1)) / 2) 0
      else encB (bits.getD ((groupRows.flatten.length - (groupRows.flatten.length + 1)) / 2) false)) = root
  rw [if_neg (Nat.lt_irrefl _), if_pos (rfl : groupRows.flatten.length = groupRows.flatten.length)]

theorem batchInAsg_sib (groupRows : List (List Fr)) (root : Fr) (sibs : List Fr)
    (bits : List Bool) (i : ℕ) :
    batchInAsg groupRows root sibs bits (groupRows.flatten.length + 1 + 2 * i) = sibs.getD i 0 := by
  have h1 : ¬ (groupRows.flatten.length + 1 + 2 * i < groupRows.flatten.length) := by omega
  have h2 : ¬ (groupRows.flatten.length + 1 + 2 * i = groupRows.flatten.length) := by omega
  have h3 : (groupRows.flatten.length + 1 + 2 * i - (groupRows.flatten.length + 1)) % 2 = 0 := by omega
  have h4 : (groupRows.flatten.length + 1 + 2 * i - (groupRows.flatten.length + 1)) / 2 = i := by omega
  simp only [batchInAsg, if_neg h1, if_neg h2, if_pos h3, h4]

theorem batchInAsg_bit (groupRows : List (List Fr)) (root : Fr) (sibs : List Fr)
    (bits : List Bool) (i : ℕ) :
    batchInAsg groupRows root sibs bits (groupRows.flatten.length + 1 + 2 * i + 1)
      = encB (bits.getD i false) := by
  have h1 : ¬ (groupRows.flatten.length + 1 + 2 * i + 1 < groupRows.flatten.length) := by omega
  have h2 : ¬ (groupRows.flatten.length + 1 + 2 * i + 1 = groupRows.flatten.length) := by omega
  have h3 : ¬ ((groupRows.flatten.length + 1 + 2 * i + 1 - (groupRows.flatten.length + 1)) % 2 = 0) := by omega
  have h4 : (groupRows.flatten.length + 1 + 2 * i + 1 - (groupRows.flatten.length + 1)) / 2 = i := by omega
  simp only [batchInAsg, if_neg h1, if_neg h2, if_neg h3, h4]

/-- Class 0's row block evaluates to the class-0 rows. -/
theorem batchLeaf0_corr (a : Assignment) (groupRows : List (List Fr))
    (hfill : ∀ v, v < groupRows.flatten.length → a v = lookupBlocks 0 groupRows v) :
    (rowVars ((groupRows.map List.length).headD 0)).map (Wire.eval · a) = groupRows.headD [] := by
  cases groupRows with
  | nil => rfl
  | cons g0 grest =>
      show (rowVars g0.length).map (Wire.eval · a) = g0
      rw [rowVars, List.map_map]
      have hc : ((List.range g0.length).map ((fun w => Wire.eval w a) ∘ Wire.var))
          = (List.range g0.length).map (fun i => g0.getD i 0) := by
        apply List.map_congr_left
        intro i hi
        rw [List.mem_range] at hi
        show a i = g0.getD i 0
        rw [hfill i (by rw [List.flatten_cons, List.length_append]; omega)]
        simp only [lookupBlocks]
        rw [if_pos (by omega), Nat.sub_zero]
      rw [hc]; exact map_getD_range g0

/-- The lower classes' row blocks evaluate to the lower-class rows. -/
theorem batchInj_corr (a : Assignment) (groupRows : List (List Fr))
    (hfill : ∀ v, v < groupRows.flatten.length → a v = lookupBlocks 0 groupRows v) :
    (groupVarsFrom ((groupRows.map List.length).headD 0) (groupRows.map List.length).tail).map
      (fun ws => ws.map (Wire.eval · a)) = groupRows.tail := by
  cases groupRows with
  | nil => rfl
  | cons g0 grest =>
      show (groupVarsFrom g0.length (grest.map List.length)).map (fun ws => ws.map (Wire.eval · a)) = grest
      apply groupVarsFrom_eval a grest g0.length
      intro v hv1 hv2
      have hvR : v < (g0 :: grest).flatten.length := by
        rw [List.flatten_cons, List.length_append]; omega
      rw [hfill v hvR]
      simp only [lookupBlocks]
      rw [if_neg (by omega), Nat.zero_add]

/-- The class-0 leaf run's define-chain (from `R+1+2·maxLh`) + forced denotation. -/
theorem batchLeaf0Run_props (widths : List ℕ) (maxLh : ℕ) :
    ∃ n1, DefChain (widths.sum + 1 + 2 * maxLh) (batchLeaf0Run widths maxLh).2.2 n1
      ∧ wBelow (batchLeaf0Run widths maxLh).1 n1
      ∧ (batchLeaf0Run widths maxLh).2.1 = n1
      ∧ ∀ a, (∀ p ∈ (batchLeaf0Run widths maxLh).2.2, p.1.eval a = p.2.eval a) →
          (batchLeaf0Run widths maxLh).1.eval a
            = multiFieldHashRef ((rowVars (widths.headD 0)).map (Wire.eval · a)) := by
  have hle : widths.headD 0 ≤ widths.sum := by
    cases widths with
    | nil => simp
    | cons w ws => rw [List.sum_cons]; show w ≤ w + ws.sum; omega
  have hrows : ∀ w ∈ rowVars (widths.headD 0), wBelow w (widths.sum + 1 + 2 * maxLh) := by
    intro w hw
    simp only [rowVars, List.mem_map, List.mem_range] at hw
    obtain ⟨i, hi, rfl⟩ := hw
    exact Nat.lt_of_lt_of_le hi (by omega)
  exact hashRun_props (rowVars (widths.headD 0)) (widths.sum + 1 + 2 * maxLh) hrows

/-- The batch-walk run's define-chain + forced denotation (`emitsW_walkB` + the step spec). -/
theorem batchWalkRun_props (widths : List ℕ) (maxLh : ℕ) (injMask : List Bool) :
    ∃ n2, DefChain (batchLeaf0Run widths maxLh).2.1 (batchWalkRun widths maxLh injMask).2.2 n2
      ∧ ∀ a, (∀ p ∈ (batchWalkRun widths maxLh injMask).2.2, p.1.eval a = p.2.eval a) →
          (batchWalkRun widths maxLh injMask).1.eval a
            = (batchLevels widths maxLh injMask).foldl
                (fun n lvl => batchStepFrMux n (lvl.1.eval a) (lvl.2.1.eval a)
                  (lvl.2.2.map (fun ws => ws.map (Wire.eval · a))))
                ((batchLeaf0Run widths maxLh).1.eval a) := by
  obtain ⟨n1, hdc1, hbleaf, hn1, -⟩ := batchLeaf0Run_props widths maxLh
  have hle : widths.sum + 1 + 2 * maxLh ≤ n1 := hdc1.le
  have hlvls : ∀ lvl ∈ batchLevels widths maxLh injMask, belLvl lvl n1 := by
    apply weaveVars_below n1
    · intro p hp
      obtain ⟨h1, h2⟩ := pairWiresFrom_below (widths.sum + 1 + 2 * maxLh) (widths.sum + 1) maxLh (by omega) p hp
      exact ⟨wBelow_mono h1 hle, wBelow_mono h2 hle⟩
    · intro g hg w hw
      have hsum : widths.headD 0 + widths.tail.sum = widths.sum := by
        cases widths with | nil => simp | cons w ws => simp [List.sum_cons]
      exact wBelow_mono (groupVarsFrom_below (widths.sum + 1 + 2 * maxLh) widths.tail (widths.headD 0)
        (by omega) g hg w hw) hle
  obtain ⟨Rw, n2, walkChain, hrun, hdc, -, hforce⟩ :=
    emitsW_walkB (belE := belLvl) (stepB := batchWalkStepW)
      (semF := fun v lvl a => batchStepFrMux v (lvl.1.eval a) (lvl.2.1.eval a)
        (lvl.2.2.map (fun ws => ws.map (Wire.eval · a))))
      belLvl_mono (fun nd lvl bd hnd hlvl => batchWalkStepW_emits nd lvl hnd hlvl)
      (batchLevels widths maxLh injMask) (batchLeaf0Run widths maxLh).1 hbleaf hlvls
      (batchLeaf0Run widths maxLh).2.1 [] (le_of_eq hn1.symm)
  have hwalkEq : batchWalkRun widths maxLh injMask = (Rw, (n2, walkChain)) := by
    show batchWalkW (batchLeaf0Run widths maxLh).1 (batchLevels widths maxLh injMask)
        ((batchLeaf0Run widths maxLh).2.1, []) = (Rw, (n2, walkChain))
    show ((batchLevels widths maxLh injMask).foldlM batchWalkStepW (batchLeaf0Run widths maxLh).1)
        ((batchLeaf0Run widths maxLh).2.1, []) = (Rw, (n2, walkChain))
    rw [hrun, List.nil_append]
  refine ⟨n2, ?_, ?_⟩
  · rw [hwalkEq]; exact hdc
  · intro a ha; rw [hwalkEq] at ha ⊢; exact hforce a ha

/-- The combined chain (class-0 leaf ++ batch walk) + its forced batch-root denotation. -/
theorem batchChain_props (widths : List ℕ) (maxLh : ℕ) (injMask : List Bool) :
    ∃ n2, DefChain (widths.sum + 1 + 2 * maxLh)
        ((batchLeaf0Run widths maxLh).2.2 ++ (batchWalkRun widths maxLh injMask).2.2) n2
      ∧ ∀ a, (∀ p ∈ (batchLeaf0Run widths maxLh).2.2 ++ (batchWalkRun widths maxLh injMask).2.2,
          p.1.eval a = p.2.eval a) →
          (batchWalkRun widths maxLh injMask).1.eval a
            = (batchLevels widths maxLh injMask).foldl
                (fun n lvl => batchStepFrMux n (lvl.1.eval a) (lvl.2.1.eval a)
                  (lvl.2.2.map (fun ws => ws.map (Wire.eval · a))))
                (multiFieldHashRef ((rowVars (widths.headD 0)).map (Wire.eval · a))) := by
  obtain ⟨n1, hdc1, -, hn1, hforce1⟩ := batchLeaf0Run_props widths maxLh
  obtain ⟨n2, hdc2, hforce2⟩ := batchWalkRun_props widths maxLh injMask
  refine ⟨n2, hdc1.append (hn1 ▸ hdc2), fun a ha => ?_⟩
  rw [List.forall_mem_append] at ha
  rw [hforce2 a ha.2, hforce1 a ha.1]

/-- **The frontend refinement**: the honest witness satisfies the batch circuit IFF the
injection-interleaved batch walk over the class leaf hashes reproduces the claimed input
root. -/
theorem batchOpen_frontend (groupRows : List (List Fr)) (root : Fr) (sibs : List Fr)
    (bits : List Bool) (injMask : List Bool) (hlen : sibs.length = bits.length) :
    (batchCircuit (groupRows.map List.length) sibs.length injMask).satisfied
        (batchAsg (groupRows.map List.length) sibs.length injMask groupRows root sibs bits)
      ↔ batchRefRoot (multiFieldHashRef (groupRows.headD []))
          (sibs.zip bits) injMask groupRows.tail = root := by
  set W := groupRows.map List.length with hWdef
  have hR : W.sum = groupRows.flatten.length := by rw [hWdef, List.length_flatten]
  set a := batchAsg W sibs.length injMask groupRows root sibs bits with ha
  obtain ⟨n', hdc, hforce⟩ := batchChain_props W sibs.length injMask
  have hbelow : ∀ v, v < W.sum + 1 + 2 * sibs.length → a v = batchInAsg groupRows root sibs bits v :=
    fun v hv => solveChain_agree_below
      ((batchLeaf0Run W sibs.length).2.2 ++ (batchWalkRun W sibs.length injMask).2.2)
      (batchInAsg groupRows root sibs bits) hdc v hv
  have hnew : ∀ p ∈ (batchLeaf0Run W sibs.length).2.2 ++ (batchWalkRun W sibs.length injMask).2.2,
      p.1.eval a = p.2.eval a :=
    solveChain_sat _ (batchInAsg groupRows root sibs bits) hdc
  have hfill : ∀ v, v < groupRows.flatten.length → a v = lookupBlocks 0 groupRows v := by
    intro v hv
    rw [hbelow v (by rw [hR]; omega), batchInAsg_row groupRows root sibs bits v hv]
  have hleaf0 : (rowVars (W.headD 0)).map (Wire.eval · a) = groupRows.headD [] :=
    hWdef ▸ batchLeaf0_corr a groupRows hfill
  have hinj : (groupVarsFrom (W.headD 0) W.tail).map (fun ws => ws.map (Wire.eval · a))
      = groupRows.tail := hWdef ▸ batchInj_corr a groupRows hfill
  have hroot : a W.sum = root := by rw [hbelow W.sum (by omega), hR, batchInAsg_root]
  have hsib : ∀ i, i < sibs.length → a (W.sum + 1 + 2 * i) = sibs.getD i 0 := by
    intro i hi; rw [hbelow (W.sum + 1 + 2 * i) (by omega), hR, batchInAsg_sib]
  have hbit : ∀ i, i < bits.length → a (W.sum + 1 + 2 * i + 1) = encB (bits.getD i false) := by
    intro i hi; rw [hbelow (W.sum + 1 + 2 * i + 1) (by omega), hR, batchInAsg_bit]
  have hwalk : (batchWalkRun W sibs.length injMask).1.eval a
      = batchRefRoot (multiFieldHashRef (groupRows.headD [])) (sibs.zip bits) injMask groupRows.tail := by
    rw [hforce a hnew, hleaf0]
    exact foldl_weave a sibs (W.sum + 1) bits injMask (groupVarsFrom (W.headD 0) W.tail)
      groupRows.tail (multiFieldHashRef (groupRows.headD [])) hlen hsib hbit hinj
  have hbool : ∀ p ∈ bitBoolFrom (W.sum + 1) sibs.length, p.1.eval a = p.2.eval a :=
    bitBoolFrom_holds a (W.sum + 1) sibs.length fun i hi => by
      rw [hbelow (W.sum + 1 + 2 * i + 1) (by omega), hR, batchInAsg_bit]
      cases bits.getD i false <;> simp [encB]
  show (∀ p ∈ bitBoolFrom (W.sum + 1) sibs.length
      ++ ((batchLeaf0Run W sibs.length).2.2 ++ (batchWalkRun W sibs.length injMask).2.2)
      ++ [((batchWalkRun W sibs.length injMask).1, Wire.var W.sum)], p.1.eval a = p.2.eval a) ↔ _
  rw [List.forall_mem_append, List.forall_mem_append, List.forall_mem_singleton]
  constructor
  · rintro ⟨_, hr⟩
    rw [← hwalk, hr]; exact hroot
  · intro hr
    refine ⟨⟨hbool, hnew⟩, ?_⟩
    show (batchWalkRun W sibs.length injMask).1.eval a = Wire.eval (Wire.var W.sum) a
    rw [hwalk, hr]; exact hroot.symm

/-- **`inputOpenBatch_refines`** — THE deliverable ∀-refinement, at the R1CS level the gnark
backend consumes: the lowered genuine R1CS of the emitted multi-height batch opening, under
the honest witness, is satisfied IFF the input-MMCS batch walk — the per-height-class
MultiField leaf hashes (`multiFieldHashRef`) laddered up the native path with the injected
class-hash compressions interleaved (`batchRefRoot`) — reproduces the claimed input root,
for EVERY class-row list, root, path, (length-matched) bit list, and injection schedule. A
tampered opened row limb (moving a class leaf hash), a wrong path node, a flipped bit, or a
corrupted root all move `batchRefRoot`, refuting `gHolds`. -/
theorem inputOpenBatch_refines (groupRows : List (List Fr)) (root : Fr) (sibs : List Fr)
    (bits : List Bool) (injMask : List Bool) (hlen : sibs.length = bits.length) :
    Dregg2.Circuit.Emit.GnarkVerifier.gHolds (batchData (groupRows.map List.length) sibs.length injMask)
        (batchAsg (groupRows.map List.length) sibs.length injMask groupRows root sibs bits)
      ↔ batchRefRoot (multiFieldHashRef (groupRows.headD []))
          (sibs.zip bits) injMask groupRows.tail = root := by
  unfold Dregg2.Circuit.Emit.GnarkVerifier.gHolds
  rw [← R1csFr.gHolds]
  exact batchOpen_frontend groupRows root sibs bits injMask hlen

/-- Reject polarity: a claimed root the opened classes do not ladder to is unsatisfiable. -/
theorem inputOpenBatch_rejects (groupRows : List (List Fr)) (root : Fr) (sibs : List Fr)
    (bits : List Bool) (injMask : List Bool) (hlen : sibs.length = bits.length)
    (h : batchRefRoot (multiFieldHashRef (groupRows.headD [])) (sibs.zip bits) injMask groupRows.tail ≠ root) :
    ¬ Dregg2.Circuit.Emit.GnarkVerifier.gHolds (batchData (groupRows.map List.length) sibs.length injMask)
        (batchAsg (groupRows.map List.length) sibs.length injMask groupRows root sibs bits) :=
  fun hg => h ((inputOpenBatch_refines groupRows root sibs bits injMask hlen).mp hg)

/-- Accept polarity (non-vacuity): the honest batch opening IS accepted. -/
theorem inputOpenBatch_accepts (groupRows : List (List Fr)) (sibs : List Fr) (bits : List Bool)
    (injMask : List Bool) (hlen : sibs.length = bits.length) :
    Dregg2.Circuit.Emit.GnarkVerifier.gHolds (batchData (groupRows.map List.length) sibs.length injMask)
      (batchAsg (groupRows.map List.length) sibs.length injMask groupRows
        (batchRefRoot (multiFieldHashRef (groupRows.headD [])) (sibs.zip bits) injMask groupRows.tail)
        sibs bits) :=
  (inputOpenBatch_refines groupRows _ sibs bits injMask hlen).mpr rfl

/-- **The emit tie** — the same refinement at the SERIALIZED wire form, via `emit_faithful`. -/
theorem inputOpenBatch_refines_emitted (groupRows : List (List Fr)) (root : Fr) (sibs : List Fr)
    (bits : List Bool) (injMask : List Bool) (hlen : sibs.length = bits.length) :
    Dregg2.Circuit.Emit.GnarkVerifier.satisfiedEmitted
        (Dregg2.Circuit.Emit.GnarkVerifier.emit (batchData (groupRows.map List.length) sibs.length injMask))
        (batchAsg (groupRows.map List.length) sibs.length injMask groupRows root sibs bits)
      ↔ batchRefRoot (multiFieldHashRef (groupRows.headD []))
          (sibs.zip bits) injMask groupRows.tail = root :=
  (Dregg2.Circuit.Emit.GnarkVerifier.emit_faithful
      (batchData (groupRows.map List.length) sibs.length injMask)
      (batchAsg (groupRows.map List.length) sibs.length injMask groupRows root sibs bits)).symm.trans
    (inputOpenBatch_refines groupRows root sibs bits injMask hlen)

/-! ## §10 The adversarial (soundness) face — no honest-fill hypothesis. -/

/-- **`inputOpenBatch_sound`** — over EVERY witness: the root variable `var R` is forced to
equal the batch-walk recomputation from the witness's own class rows, path nodes, and bit
values. The prover cannot satisfy the circuit while claiming a root the opened classes do
not ladder to. -/
theorem inputOpenBatch_sound (widths : List ℕ) (maxLh : ℕ) (injMask : List Bool) (a : Assignment)
    (hsat : (batchCircuit widths maxLh injMask).satisfied a) :
    a widths.sum
      = (batchLevels widths maxLh injMask).foldl
          (fun n lvl => batchStepFrMux n (lvl.1.eval a) (lvl.2.1.eval a)
            (lvl.2.2.map (fun ws => ws.map (Wire.eval · a))))
          (multiFieldHashRef ((rowVars (widths.headD 0)).map (Wire.eval · a))) := by
  obtain ⟨_, _, hforce⟩ := batchChain_props widths maxLh injMask
  have hsat' : ∀ p ∈ bitBoolFrom (widths.sum + 1) maxLh
      ++ ((batchLeaf0Run widths maxLh).2.2 ++ (batchWalkRun widths maxLh injMask).2.2)
      ++ [((batchWalkRun widths maxLh injMask).1, Wire.var widths.sum)], p.1.eval a = p.2.eval a := hsat
  rw [List.forall_mem_append, List.forall_mem_append, List.forall_mem_singleton] at hsat'
  obtain ⟨⟨_, hnew⟩, hroot⟩ := hsat'
  rw [show a widths.sum = (Wire.var widths.sum).eval a from rfl, ← hroot, hforce a hnew]

#assert_axioms batchLeaf0_corr
#assert_axioms batchInj_corr
#assert_axioms batchChain_props
#assert_axioms batchOpen_frontend
#assert_axioms inputOpenBatch_refines
#assert_axioms inputOpenBatch_rejects
#assert_axioms inputOpenBatch_accepts
#assert_axioms inputOpenBatch_refines_emitted
#assert_axioms inputOpenBatch_sound

/-! ## §11 KAT teeth — the REAL apex-shrink fixture input root (both polarities).

The four height classes {19,18,12,3} of query 0, input round 1 of
`chain/gnark/fixtures/apex_shrink_fri_real.json`, its 19-node path, query index 357832, and
the committed round-1 input root — the exact data `openInputBatchRootRef`
(`chain/gnark/stark_open_input_ref.go`) laddered to `katInputRoot`. `batchRefRoot` (the
refinement's right-hand predicate) reproduces it BIT-EXACTLY, and every tamper moves it. -/

/-- Class 0 (height 19): two width-4 matrix rows concatenated (8 base limbs). -/
def katG0 : List Fr :=
  [1515012075, 1644027478, 710008838, 1069764620, 1518310020, 1884049610, 1904091301, 1704050631]
/-- Class 1 (height 18): four width-4 rows (16 limbs). -/
def katG1 : List Fr :=
  [673423875, 664706297, 1931899510, 158149210, 1133113356, 1384102861, 187522263, 1095088913,
   684796996, 24805640, 959729680, 109327476, 689854820, 1909853986, 566436532, 1073934107]
/-- Class 2 (height 12): four width-4 rows (16 limbs). -/
def katG2 : List Fr :=
  [1117915787, 642091300, 1750569592, 242313706, 714251418, 775970689, 45910543, 1550892170,
   682948935, 1025247676, 768752747, 468074298, 831584578, 912354886, 768668927, 1836181704]
/-- Class 3 (height 3): two width-4 rows (8 limbs). -/
def katG3 : List Fr :=
  [45825524, 1088835559, 1235286852, 870073596, 45825524, 1088835559, 1235286852, 870073596]

/-- The 19 native BN254 path nodes (bottom-up), verbatim from the fixture query 0 round 1. -/
def katPath : List Fr :=
  [0x046a3c4113264bec48760e971b7b6415e619babc5035314c8790f804f61fa55a,
   0x1ebc6f6c3d041f1800b72f4da0b3605fe967377b7a5c4e791e4fe22bc81801db,
   0x04b190c209e8fd5fedd6d6a978faa1a6b4fc53068efb7f35dfbe9a8a97aee6b6,
   0x124f73e1ae5872e6d06ebd058193c6702d6fccad30ff5558c863b605a2562905,
   0x014b1fa17c4a23818e473c00cb3f98fb139df94363590796a143df535ec7c99c,
   0x13b196576882ff8e0379525d3c67888bd8a17c8ef8f5d485484db6db23bdd1b2,
   0x1f717f009a8f15b3e13f273c6ae5230a807cb9b3e2e176e7251df9b08dbc1750,
   0x186c164ff3a664be8f594e7225619c28ebdad52ef15013badb8839ca78516d06,
   0x0b8a81876d19cb1173a3bfc9a628a181cc7686f370760642e6f109f0f20a9f71,
   0x229a9ecd0ea0919a8927850d941588e8185132e0668501f8f236c082796b9a79,
   0x09ccd9f312f4141587651ed8606629e8feb915cdc855da1edc2ab674bb31b2ea,
   0x24b9ea8719b61c63143ca17b362fe24f53199b3b1d4eb75d5eed87216a6c91a5,
   0x09366e81178e75a66c4121e2d84c31c8ac81407a5ccf5366e486193f4c63a9b3,
   0x0ad657d541ff0e548126ed59da55caf61f6d6e726b581b8bd83708790b701b97,
   0x26c7dcd31302bc29381cd41f9d17ebc10ed7c19ed0e7919e22fe2a83b4cbd009,
   0x07e28d8670680290e27adad340a5404d9346d74ef8bc47b00446c6e23b11cf60,
   0x0d0b7c39946327b232b8426a95f048c9e317c13e630af057e75837c980019a1b,
   0x2c7e9df092779d85dcc837d3897d6607cbfc9fdf53c5caaa6fcfe77dc3cc310f,
   0x263b02a82f1542d47d08c8c199e3a5b43d788cabc9a10b81f24f29ce72de5ec6]

/-- The query index (357832): the 19 LSB-first path bits steer the walk. The batch tree's
max class height is 19 = the fixture's `log_global_max_height`, so the reduced index is the
full index (no shift). -/
def katBits : List Bool := (List.range 19).map (Nat.testBit 357832)

/-- The class-injection schedule: classes 1/2/3 (heights 18/12/3) inject after steps 0/6/15
(`18 - step ∈ {18,12,3}`), so the walk reaches a class-carrying height there. -/
def katMask : List Bool :=
  [true, false, false, false, false, false, true, false, false, false,
   false, false, false, false, false, true, false, false, false]

/-- The committed round-1 input commitment root (`openInputBatchRootRef` = `roots[1]`). -/
def katInputRoot : Fr := 0x0800ca135b86a94ffd34a511fc975caab11234662ccaf9cc5bc35eb4531d12f4

-- The multi-height batch walk reproduces the REAL fixture input root BIT-EXACTLY (accept):
-- class-0 leaf hash laddered up the 19-node path with classes 1/2/3 injected at steps 0/6/15.
#guard batchRefRoot (multiFieldHashRef katG0) (katPath.zip katBits) katMask [katG1, katG2, katG3]
  = katInputRoot

-- Tampered opened row limb (class-0 limb 0) — a class leaf hash moves ⇒ the root moves (reject).
#guard batchRefRoot (multiFieldHashRef (0 :: katG0.tail)) (katPath.zip katBits) katMask
    [katG1, katG2, katG3] ≠ katInputRoot
-- Wrong path node (node 0) — the root moves (reject).
#guard batchRefRoot (multiFieldHashRef katG0) ((0 :: katPath.tail).zip katBits) katMask
    [katG1, katG2, katG3] ≠ katInputRoot
-- Flipped path bit (bit 0: false → true) — the left/right swap moves the root (reject).
#guard batchRefRoot (multiFieldHashRef katG0) (katPath.zip (true :: katBits.tail)) katMask
    [katG1, katG2, katG3] ≠ katInputRoot
-- Tampered injected class row (class 3) — the injected class hash moves ⇒ the root moves (reject).
#guard batchRefRoot (multiFieldHashRef katG0) (katPath.zip katBits) katMask
    [katG1, katG2, (0 :: katG3.tail)] ≠ katInputRoot
-- Dropped injection (mask false at step 15) — class 3 never folds in ⇒ the root moves (reject).
#guard batchRefRoot (multiFieldHashRef katG0) (katPath.zip katBits)
    (katMask.take 15 ++ [false] ++ katMask.drop 16) [katG1, katG2, katG3] ≠ katInputRoot

/-! ## §12 The emitted JSON artifacts.

Two committed templates:

  * `chain/gnark/emitted/leafhash_template.json` — the per-class MMCS leaf-hash ReplayTemplate
    (`leafHashData`) at a real class width (8 limbs = two extension evals). Rows-in →
    leaf-out, NO `select`; the Go side binds the row prefix and solves the leaf.
  * `chain/gnark/emitted/inputopen_batch_template.json` — the multi-height batch opening
    (`batchData`) at the deployed round-1 shape: classes {19,18,12,3} (widths [8,16,16,8]),
    path depth 19, the {0,6,15} injection schedule. The `ReplayClosed` boundary binds
    rows/path-nodes/bits/root by index; the define-chain solves the Poseidon internals.

Byte pins are length + FNV-1a of the exact rendered string (a literal pin of a multi-MB
template would be unreadable; the digest flips on ANY byte change). -/

/-- FNV-1a over the UTF-8 bytes — the byte-pin digest. -/
def fnv1a (s : String) : UInt64 :=
  s.toUTF8.foldl (fun h b => (h ^^^ b.toUInt64) * 1099511628211) 14695981039346656037

/-- The width-8 leaf-hash template bytes (committed at `chain/gnark/emitted/leafhash_template.json`). -/
def leafHashTemplateJson : String :=
  Dregg2.Circuit.Emit.GnarkVerifier.emitGnarkJson (leafHashData 8)

/-- The deployed round-1 batch template bytes (committed at
`chain/gnark/emitted/inputopen_batch_template.json`). -/
def batchTemplateJson : String :=
  Dregg2.Circuit.Emit.GnarkVerifier.emitGnarkJson (batchData [8, 16, 16, 8] 19 katMask)

/-- The three OTHER deployed input-round batch templates — the SAME `batchData` at the real
apex-shrink per-round opened-row widths (trace / preprocessed / permutation rounds; the
quotient round is `batchTemplateJson` above). All four rounds open the height classes
{19,18,12,3} with the {0,6,15} injection schedule at depth 19, so they share `katMask` and
differ only in the per-class row widths; every instance is covered by the parametric
`inputOpenBatch_refines`. Committed at `chain/gnark/emitted/inputopen_batch_r{0,2,3}.json`. -/
def batchTemplateR0Json : String :=
  Dregg2.Circuit.Emit.GnarkVerifier.emitGnarkJson (batchData [76, 304, 8, 164] 19 katMask)
def batchTemplateR2Json : String :=
  Dregg2.Circuit.Emit.GnarkVerifier.emitGnarkJson (batchData [59, 26, 8, 82] 19 katMask)
def batchTemplateR3Json : String :=
  Dregg2.Circuit.Emit.GnarkVerifier.emitGnarkJson (batchData [72, 32, 8, 164] 19 katMask)

-- Structure pins for the leaf-hash template: one sponge block (width 8 = one rate slot) is
-- 435 emitted round-schedule asserts + the leaf pin; the ReplayTemplate boundary is 8 rows
-- + 1 leaf, with NO select gate (a pure sponge).
#guard (leafHashCircuit 8).asserts.length == 436
#guard (leafHashData 8).publicInputs.length == 9

-- Structure pin for the deployed round-1 batch shape (widths [8,16,16,8], depth 19): the 19
-- per-level booleanity asserts + class-0 leaf hash (435) + 16 plain path compressions (16·435)
-- + 3 injection levels (each path compress + class leaf hash + inject compress = 3·435) + the
-- final root pin = 19 + 435 + 6960 + 3915 + 1 = 11330. (Every class here is one sponge block:
-- `(leafHashCircuit 8).asserts.length = (leafHashCircuit 16).asserts.length = 436` = 435 + pin.)
#guard (batchCircuit [8, 16, 16, 8] 19 katMask).asserts.length == 11330

-- Byte pins of the committed artifacts: exact length + FNV-1a. Any byte drift flips the digest.
#guard leafHashTemplateJson.length == 154488
#guard fnv1a leafHashTemplateJson == 6822594251786242841
#guard batchTemplateJson.length == 4126538
#guard fnv1a batchTemplateJson == 8606667901513431991
#guard batchTemplateR0Json.length == 9915026
#guard fnv1a batchTemplateR0Json == 8675028724040056151
#guard batchTemplateR2Json.length == 5713435
#guard fnv1a batchTemplateR2Json == 12934477427165409992
#guard batchTemplateR3Json.length == 6812448
#guard fnv1a batchTemplateR3Json == 9190003375973087705

end Dregg2.Circuit.Emit.GnarkVerifier.InputOpenBatch
