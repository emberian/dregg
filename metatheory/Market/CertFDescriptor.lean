/-
# Market.CertFDescriptor — the Cert-F AIR, AUTHORED IN LEAN as an `EffectVmDescriptor2`.

`Market.CertF` proves the fhEgg Cert-F soundness core (`weak_duality`,
`certifies_epsilon_optimal`) and — at the toy `Dregg2.Circuit.ConstraintSystem` level —
emits the *equality* part of the certificate check (`certCircuit`, `certCircuit_sound`),
NAMING the feasibility inequalities as riding "the standard AIR range gadget".

The historical `circuit-prove/src/cert_f_air.rs::cert_f_descriptor` hand-built the full
`EffectVmDescriptor2` in Rust. This module closes that gap: it
AUTHORS the exact same descriptor in Lean as a total function of the public program, PROVES the
field-level emit-SOUNDNESS bridge (`certFDescriptor_emit_sound`, §6) GENERIC over every
`p : CertFProg`, and proves the explicit modular-to-integer bridge
(`certFDescriptor_emit_Certified_sound`, §7):

    Satisfied2 hash (certFDescriptorOf p) m0 f0 [] (constTrace p a)
      + canonical cells + aggregate no-wrap
      →  Market.Certified (integerFlowLP p) f π s

i.e. ANY assignment whose constant trace satisfies the deployed IR-v2 denotation `Satisfied2`
carries a certificate obeying ALL FIVE families over the BabyBear field — `A f = 0`, `0 ≤ f ≤ c`,
`s ≥ 0`, `Aᵀπ + s ≥ w`, `cᵀs − wᵀf ≤ ε` — plus the objective pin `obj ≡ wᵀf`. This is the SECURITY
direction (a satisfying trace cannot lie) — the theorem the hand-written Rust could only *test*.
The feasibility inequalities ride the range-gadget tooth `rangeGadget_forces_range` (§5), exactly
the gadget `Market.CertF` deferred to "the standard AIR range gadget", now PROVED. Section 7 does
not silently reinterpret field congruences: it bounds each complete conservation / dual / gap /
objective residual, then lifts it. The COMPLETENESS direction is witnessed executably by the
byte-identical Rust STARK (`cert_f_air.rs::air_accepts_valid_ring3` /
`stark_proves_and_verifies_ring3`).

The Rust is re-pointed onto this Lean-authored descriptor via the byte-pinned-twin discipline the
effect_vm family uses: `emitVmJson2 certFDescriptor` is the canonical wire string (committed at
`circuit/descriptors/dregg-cert-f-ir2.json`) and is exact-equality pinned against the literal in
`Market.CertFGolden`. Rust `include_str!`s and parses committed artifacts; it authors no Cert-F
constraint. A different public `(A,w,c,ε)` program is deliberately fail-closed until its own
emitted artifact, byte pin, and registry entry exist. The modular theorem is generic; its integer
interpretation additionally requires the program's aggregate no-wrap discharge from §7.

## The five constraint families (mirroring `cert_f_air.rs` exactly)

For the circulation LP `max wᵀf s.t. Af=0, 0≤f≤c`, dual `(π, s)`, a certificate `(f,π,s)`
is ε-optimal iff `Af=0 ∧ 0≤f≤c ∧ s≥0 ∧ Aᵀπ+s≥w ∧ cᵀs−wᵀf≤ε`. Over the witness columns
`(f, s, π)` + slack columns `(u, d, g)` + objective `obj`:

  1. conservation `Σ_{head=i} f_e − Σ_{tail=i} f_e = 0` — one arithmetic gate per node.
  2. box lower `f_e ≥ 0` — the range gadget on `f_e`.
  3. box upper `c_e − f_e ≥ 0` — `u_e == c_e − f_e` (gate) + range gadget on `u_e`.
  4. slack sign `s_e ≥ 0` — the range gadget on `s_e`.
  5. dual feas `π_head − π_tail + s_e − w_e ≥ 0` — `d_e == …` (gate) + range gadget on `d_e`.
  6. gap `cᵀs − wᵀf ≤ ε` — `g == ε − (cᵀs − wᵀf)` (gate) + range gadget on `g`.
  7. objective `obj == wᵀf` (gate) + expose `obj` as the one public input (`wᵀf`).

The range gadget is `certFValueBits` boolean gates `b(b−1)==0` plus one recompose gate
`col − Σⱼ 2ʲ·bⱼ == 0`, forcing `col ∈ [0, 2^bits)` — the field-soundness tooth.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Market.CertF
import Market.CertFGolden
import Dregg2.Circuit.GateExpr

namespace Market.CertFDescriptor

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2

/-! ## §1 — The public program + column layout (byte-identical to `cert_f_air.rs`). -/

/-- The in-AIR range-gadget bit-width (`cert_f_air.rs::VALUE_BITS = 28`). -/
def certFValueBits : Nat := 28

/-- The public program a Cert-F descriptor rides on: the incidence (edge list `(tail, head)`),
the objective weights `w`, the capacities `c`, and the accuracy target `ε`. The private
witness `(f, π, s)` is NOT here — it lives only in the trace. -/
structure CertFProg where
  nNodes : Nat
  edges  : List (Nat × Nat)
  w      : List Int
  c      : List Int
  eps    : Int
  /-- Registry-enforced upper bound for primal flows.  This is part of the public AIR policy,
  not witness metadata.  Values above `certFValueBits` are clamped at the base 28-bit gadget. -/
  flowBits : Nat
  /-- Registry-enforced upper bound for dual slacks, likewise part of the public AIR policy. -/
  slackBits : Nat
  deriving Repr

namespace CertFProg

def m (p : CertFProg) : Nat := p.edges.length
def tailAt (p : CertFProg) (e : Nat) : Nat := (p.edges.getD e (0, 0)).1
def headAt (p : CertFProg) (e : Nat) : Nat := (p.edges.getD e (0, 0)).2
def wAt (p : CertFProg) (e : Nat) : Int := p.w.getD e 0
def cAt (p : CertFProg) (e : Nat) : Int := p.c.getD e 0

/-- Column layout — the EXACT `CertFWitness::*_col` offsets. -/
def fCol   (_p : CertFProg) (e : Nat) : Nat := e
def sCol   (p : CertFProg) (e : Nat) : Nat := p.m + e
def piCol  (p : CertFProg) (i : Nat) : Nat := 2 * p.m + i
def objCol (p : CertFProg) : Nat := 2 * p.m + p.nNodes
def uCol   (p : CertFProg) (e : Nat) : Nat := p.objCol + 1 + e
def dCol   (p : CertFProg) (e : Nat) : Nat := p.objCol + 1 + p.m + e
def gCol   (p : CertFProg) : Nat := p.objCol + 1 + 2 * p.m
def bitBase (p : CertFProg) : Nat := p.gCol + 1
/-- Range-bit column: `bit_base + target·VALUE_BITS + j` (`range_bit_col`). -/
def rangeBitCol (p : CertFProg) (target j : Nat) : Nat := p.bitBase + target * certFValueBits + j
/-- Width of the historical scalar + `f,u,s,d,g` range-bit prefix. -/
def coreWidth (p : CertFProg) : Nat := p.bitBase + (4 * p.m + 1) * certFValueBits
/-- Dedicated potential range-bit column.  Potentials were the only certificate scalars with no
range gadget in v1; keeping this band after the historical prefix makes the compatibility break
explicit and leaves every old scalar/bit offset stable. -/
def potentialRangeBitCol (p : CertFProg) (i j : Nat) : Nat :=
  p.coreWidth + i * certFValueBits + j
/-- Effective policy bounds cannot exceed the 28-bit base gadget whose bit columns they reuse. -/
def effectiveFlowBits (p : CertFProg) : Nat := min p.flowBits certFValueBits
def effectiveSlackBits (p : CertFProg) : Nat := min p.slackBits certFValueBits
/-- Full trace width: the historical prefix plus one 28-bit range decomposition per potential. -/
def width (p : CertFProg) : Nat := p.coreWidth + p.nNodes * certFValueBits

end CertFProg

/-! ## §2 — Expression / gate constructors (byte-identical to `cert_f_air.rs`). -/

/-- `x − y` as an `EmittedExpr` (`cert_f_air.rs::sub`). -/
def esub (x y : EmittedExpr) : EmittedExpr := .add x (.mul (.const (-1)) y)

/-- A pure per-row vanishing gate `body == 0` (`cert_f_air.rs::gate`). -/
def egate (body : EmittedExpr) : VmConstraint2 := .base (.gate body)

/-- The `j`-th boolean gate body `bⱼ·(bⱼ−1)` of a range gadget. -/
def boolExpr (bitCol : Nat → Nat) (j : Nat) : EmittedExpr :=
  Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toEmitted
    (Dregg2.Circuit.GateExpr.gBoolEnc2 (.leaf (bitCol j)))

theorem boolExpr_eq (bitCol : Nat → Nat) (j : Nat) :
    boolExpr bitCol j = let b := EmittedExpr.var (bitCol j); .mul b (esub b (.const 1)) := rfl

/-- The recompose gate body `col − Σⱼ 2ʲ·bⱼ` of a range gadget. -/
def recomposeExpr (col : Nat) (bitCol : Nat → Nat) : EmittedExpr :=
  (List.range certFValueBits).foldl
    (fun acc j => esub acc (.mul (.const ((2 : Int) ^ j)) (EmittedExpr.var (bitCol j))))
    (EmittedExpr.var col)

/-- Recompose against the first `bits` columns of an existing range decomposition.  This is the
deployed tight-range guard: the original 28-bit recompose remains, while this second equality
forces every bit at position `bits` and above to be zero without allocating a duplicate band. -/
def tightRecomposeExpr (bits col : Nat) (bitCol : Nat → Nat) : EmittedExpr :=
  (List.range bits).foldl
    (fun acc j => esub acc (.mul (.const ((2 : Int) ^ j)) (EmittedExpr.var (bitCol j))))
    (EmittedExpr.var col)

/-- The range gadget for one target column: `certFValueBits` boolean gates `b(b−1)==0` plus one
recompose gate `col − Σⱼ 2ʲ·bⱼ == 0` (`cert_f_air.rs::range_gadget`). -/
def rangeGadget (col : Nat) (bitCol : Nat → Nat) : List VmConstraint2 :=
  ((List.range certFValueBits).map (fun j => egate (boolExpr bitCol j))) ++
  [ egate (recomposeExpr col bitCol) ]

/-! ## §3 — The descriptor (the five families, in `cert_f_air.rs` order). -/

/-- Conservation body at node `i`: `Σ_{head=i} f_e − Σ_{tail=i} f_e` (`cert_f_descriptor` step 1). -/
def consBody (p : CertFProg) (i : Nat) : EmittedExpr :=
  (List.range p.m).foldl
    (fun body e =>
      let body := if p.headAt e == i then .add body (EmittedExpr.var (p.fCol e)) else body
      if p.tailAt e == i then esub body (EmittedExpr.var (p.fCol e)) else body)
    (.const 0)

/-- The historical Cert-F constraint prefix, retained byte-for-byte so the v2 admission policy is
an auditable append rather than a rewrite of the already-proved field certificate. -/
def certFCoreConstraints (p : CertFProg) : List VmConstraint2 :=
  -- 1. conservation: one gate per node.
  ((List.range p.nNodes).map (fun i => egate (consBody p i)))
  -- 2. box lower f_e ≥ 0.
  ++ (((List.range p.m).map (fun e =>
        rangeGadget (p.fCol e) (fun j => p.rangeBitCol e j))).flatten)
  -- 3. box upper c_e − f_e ≥ 0: u_e == c_e − f_e (gate) + range gadget on u_e.
  ++ (((List.range p.m).map (fun e =>
        egate (.add (esub (EmittedExpr.var (p.uCol e)) (.const (p.cAt e))) (EmittedExpr.var (p.fCol e)))
        :: rangeGadget (p.uCol e) (fun j => p.rangeBitCol (p.m + e) j))).flatten)
  -- 4. slack sign s_e ≥ 0.
  ++ (((List.range p.m).map (fun e =>
        rangeGadget (p.sCol e) (fun j => p.rangeBitCol (2 * p.m + e) j))).flatten)
  -- 5. dual feas: d_e == π_head − π_tail + s_e − w_e (gate) + range gadget on d_e.
  ++ (((List.range p.m).map (fun e =>
        let dualExpr :=
          esub (.add (esub (EmittedExpr.var (p.piCol (p.headAt e))) (EmittedExpr.var (p.piCol (p.tailAt e))))
                     (EmittedExpr.var (p.sCol e)))
               (.const (p.wAt e))
        egate (esub (EmittedExpr.var (p.dCol e)) dualExpr)
        :: rangeGadget (p.dCol e) (fun j => p.rangeBitCol (3 * p.m + e) j))).flatten)
  -- 6. gap cᵀs − wᵀf ≤ ε: g == ε − (cᵀs − wᵀf) (gate) + range gadget on g.
  ++ ( egate ((List.range p.m).foldl
        (fun body e =>
          esub (.add body (.mul (.const (p.cAt e)) (EmittedExpr.var (p.sCol e))))
               (.mul (.const (p.wAt e)) (EmittedExpr.var (p.fCol e))))
        (esub (EmittedExpr.var p.gCol) (.const p.eps)))
      :: rangeGadget p.gCol (fun j => p.rangeBitCol (4 * p.m) j))
  -- 7. objective obj == wᵀf (gate) + expose it as the public clearing volume.
  ++ [ egate ((List.range p.m).foldl
         (fun body e => esub body (.mul (.const (p.wAt e)) (EmittedExpr.var (p.fCol e))))
         (EmittedExpr.var p.objCol))
     , .base (.piBinding .first p.objCol 0) ]

/-- The integer-admission range policy appended to the historical Cert-F AIR. -/
def certFAdmissionConstraints (p : CertFProg) : List VmConstraint2 :=
  -- 8. INTEGER-ADMISSION GUARDS.  Reuse the existing boolean bands to enforce the registry's
  -- tighter f/s policies, then range every potential in a fresh 28-bit band.  These constraints
  -- are descriptor semantics: callers cannot opt out while presenting the same registered wire.
  ((List.range p.m).map (fun e =>
        egate (tightRecomposeExpr p.effectiveFlowBits (p.fCol e)
          (fun j => p.rangeBitCol e j))))
  ++ ((List.range p.m).map (fun e =>
        egate (tightRecomposeExpr p.effectiveSlackBits (p.sCol e)
          (fun j => p.rangeBitCol (2 * p.m + e) j))))
  ++ (((List.range p.nNodes).map (fun i =>
        rangeGadget (p.piCol i) (fun j => p.potentialRangeBitCol i j))).flatten)

/-- The full deployed Cert-F constraint list: proved field core plus enforced integer policy. -/
def certFConstraints (p : CertFProg) : List VmConstraint2 :=
  certFCoreConstraints p ++ certFAdmissionConstraints p

/-- **The Lean-authored Cert-F descriptor**, a total function of the public program: the exact
`EffectVmDescriptor2` that `cert_f_air.rs::cert_f_descriptor` hand-builds. -/
def certFDescriptorOf (p : CertFProg) : EffectVmDescriptor2 :=
  { name        := "cert-f"
  , traceWidth  := p.width
  , piCount     := 1
  , tables      := []
  , constraints := certFConstraints p
  , hashSites   := []
  , ranges      := [] }

/-! ## §4 — The worked 3-cycle instance (the twin of `cert_f_air.rs::ring3_cert`). -/

/-- The directed triangle `0→1→2→0`, unit weights + caps, `ε = 0` — the public program of
`Market.CertF.ringLP` and `cert_f_air.rs::ring3_cert`. -/
def ring3Prog : CertFProg :=
  { nNodes := 3, edges := [(0, 1), (1, 2), (2, 0)], w := [1, 1, 1], c := [1, 1, 1], eps := 0
  , flowBits := 28, slackBits := 28 }

/-- The Lean-authored Cert-F descriptor for the worked 3-cycle. -/
def certFDescriptor : EffectVmDescriptor2 := certFDescriptorOf ring3Prog

/-! ### Structural shape pins (byte-agreement with the Rust layout). -/

-- ring3 v2: historical width 381 + 3·28 potential bits = 465.
#guard certFDescriptor.name == "cert-f"
#guard certFDescriptor.piCount == 1
#guard certFDescriptor.traceWidth == 465
#guard ring3Prog.width == 465
-- historical 389 + 3 flow guards + 3 slack guards + 3·29 potential range gates = 482.
#guard certFDescriptor.constraints.length == 482
#guard certFDescriptor.tables.length == 0
#guard certFDescriptor.hashSites.length == 0
#guard certFDescriptor.ranges.length == 0

/- Exact provenance pin: the committed Rust `include_str!` artifact is this
literal, and any emitter drift fails the Lean build. -/
#guard emitVmJson2 certFDescriptor == Market.CertFGolden.CERT_F_RING3_GOLDEN

/-! ## §4b — The first REAL market shape past the toy: a 3-asset / 4-order DrEX batch.

`fhegg-solver/src/bin/fhegg_clear.rs` maps a revealed DrEX batch to the trade-circulation LP:
nodes = assets, one edge per order `(wantAsset → offerAsset)`, `cap = offerAmount`,
`weight = priority`. This program is that LP for a concrete 4-order batch over assets
`{0, 1, 2}` — a 3-ring of trades plus one reverse pair (the smallest shape with BOTH a
multi-hop ring and a bilateral leg, i.e. a genuine multi-edge circulation, not a bare cycle):

  order 0: offers 5 of asset 1 for asset 0, priority 1  →  edge (0,1), c 5, w 1
  order 1: offers 5 of asset 2 for asset 1, priority 1  →  edge (1,2), c 5, w 1
  order 2: offers 5 of asset 0 for asset 2, priority 1  →  edge (2,0), c 5, w 1
  order 3: offers 3 of asset 0 for asset 1, priority 3  →  edge (1,0), c 3, w 3

at FIXED-POINT SCALE 100 (the `from_solution_json` scale — `w, c` are the solver's f64 program
×100, so a bridged real solve matches these constants exactly), with a PRESCRIPTIVE accuracy
budget `ε = 2000` (~1.1% of the optimum `wᵀf = 180000`): a REAL solver output with a nonzero
achieved gap ≤ ε registers and proves — the ε=0-only trap the ring-3 era had is structurally
gone. Unique optimum `f = (500, 200, 200, 300)`, dual `π = (200, 0, 100)`, tight gap 0. -/
def market4Prog : CertFProg :=
  { nNodes := 3
  , edges  := [(0, 1), (1, 2), (2, 0), (1, 0)]
  , w      := [100, 100, 100, 300]
  , c      := [500, 500, 500, 300]
  , eps    := 2000
  , flowBits := 21
  , slackBits := 19 }

/-- The Lean-authored Cert-F descriptor for the 3-asset/4-order market batch. -/
def certFMarket4Descriptor : EffectVmDescriptor2 := certFDescriptorOf market4Prog

-- market4 v2: historical width 497 + 3·28 potential bits = 581.
#guard certFMarket4Descriptor.name == "cert-f"
#guard certFMarket4Descriptor.piCount == 1
#guard certFMarket4Descriptor.traceWidth == 581
#guard market4Prog.width == 581
-- historical 507 + 4 flow guards + 4 slack guards + 3·29 potential range gates = 602.
#guard certFMarket4Descriptor.constraints.length == 602
-- Conservation-only no-wrap: max node degree (3) · 2^28 < p. This does NOT bound the weighted
-- objective/gap or unrestricted potential differences; §7 accounts for those separately.
#guard 3 * 2 ^ certFValueBits < 2013265921

/- Exact provenance pin: the committed `dregg-cert-f-market4-ir2.json` artifact is this literal,
and any emitter drift fails the Lean build. (No new proof needed: §6's emit-soundness is generic
over the program — this pin plus the registry entry IS the whole registration.) -/
#guard emitVmJson2 certFMarket4Descriptor == Market.CertFGolden.CERT_F_MARKET4_GOLDEN

/-! ## §5 — The RANGE-GADGET soundness lemma (the tooth `Market.CertF` deferred to "the standard
AIR range gadget"). This is the reusable core: a satisfied range gadget FORCES its target into
`[0, 2^bits)` over ℤ (under the deployed canonicality range-check invariant). -/

open Dregg2.Circuit.Emit.EffectVmEmitTransfer (pPrimeInt)

/-- The deployed range-check invariant: a cell is a canonical representative `0 ≤ x < p`. -/
def CanonCell (x : ℤ) : Prop := 0 ≤ x ∧ x < 2013265921

/-- Two canonical representatives congruent mod `p` are equal. -/
theorem eq_of_modEq_of_canon {a b : ℤ} (h : a ≡ b [ZMOD 2013265921])
    (ha : CanonCell a) (hb : CanonCell b) : a = b := by
  obtain ⟨ha0, ha1⟩ := ha; obtain ⟨hb0, hb1⟩ := hb
  obtain ⟨k, hk⟩ := h.dvd; omega

/-- A canonical cell whose booleanity gate vanishes mod `p` is `0` or `1` over ℤ. -/
theorem binary_of_boolExpr {a : Assignment} {bc : Nat → Nat} {j : Nat}
    (h : (boolExpr bc j).eval a ≡ 0 [ZMOD 2013265921]) (hc : CanonCell (a (bc j))) :
    a (bc j) = 0 ∨ a (bc j) = 1 := by
  obtain ⟨h0, h1⟩ := hc
  have hev : (boolExpr bc j).eval a = a (bc j) * (a (bc j) - 1) := by
    simp only [boolExpr_eq, esub, EmittedExpr.eval]; ring
  rw [hev] at h
  have hd : (2013265921 : ℤ) ∣ a (bc j) * (a (bc j) - 1) := Int.modEq_zero_iff_dvd.mp h
  rcases pPrimeInt.dvd_mul.mp hd with hx | hx
  · obtain ⟨k, hk⟩ := hx; left; omega
  · obtain ⟨k, hk⟩ := hx; right; omega

/-- `esub x y` evaluates to `x − y`. -/
theorem esub_eval (x y : EmittedExpr) (a : Assignment) :
    (esub x y).eval a = x.eval a - y.eval a := by
  simp [esub, EmittedExpr.eval]; ring

/-- The recompose fold evaluates to `col − Σⱼ 2ʲ·bⱼ` (over the bit list). -/
theorem recompose_foldl_eval (a : Assignment) (bc : Nat → Nat) :
    ∀ (l : List Nat) (e0 : EmittedExpr),
      (l.foldl (fun acc j => esub acc (.mul (.const ((2 : Int) ^ j)) (EmittedExpr.var (bc j)))) e0).eval a
        = e0.eval a - ((l.map (fun j => (2 : Int) ^ j * a (bc j))).sum) := by
  intro l
  induction l with
  | nil => intro e0; simp
  | cons x xs ih =>
      intro e0
      rw [List.foldl_cons, ih]
      simp only [List.map_cons, List.sum_cons, esub, EmittedExpr.eval]
      ring

theorem recomposeExpr_eval (col : Nat) (bc : Nat → Nat) (a : Assignment) :
    (recomposeExpr col bc).eval a
      = a col - (((List.range certFValueBits).map (fun j => (2 : Int) ^ j * a (bc j))).sum) := by
  have := recompose_foldl_eval a bc (List.range certFValueBits) (EmittedExpr.var col)
  simpa [recomposeExpr, EmittedExpr.eval] using this

/-- Evaluation formula for the deployed tight-range recompose gate. -/
theorem tightRecomposeExpr_eval (bits col : Nat) (bc : Nat → Nat) (a : Assignment) :
    (tightRecomposeExpr bits col bc).eval a
      = a col - (((List.range bits).map (fun j => (2 : Int) ^ j * a (bc j))).sum) := by
  have := recompose_foldl_eval a bc (List.range bits) (EmittedExpr.var col)
  simpa [tightRecomposeExpr, EmittedExpr.eval] using this

/-- The weighted bit sum of `n` booleans lies in `[0, 2^n)`. -/
theorem bitsum_bounds (a : Assignment) (bc : Nat → Nat) :
    ∀ n, (∀ j < n, a (bc j) = 0 ∨ a (bc j) = 1) →
      0 ≤ ((List.range n).map (fun j => (2 : Int) ^ j * a (bc j))).sum
       ∧ ((List.range n).map (fun j => (2 : Int) ^ j * a (bc j))).sum < 2 ^ n := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ k ih =>
      intro hbit
      obtain ⟨ih0, ih1⟩ := ih (fun j hj => hbit j (by omega))
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      have h2k : (0 : ℤ) ≤ 2 ^ k := by positivity
      have hpow : (2 : ℤ) ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
      rcases hbit k (by omega) with h | h <;> rw [h] <;> constructor <;> nlinarith [ih0, ih1, h2k]

/-- **THE RANGE-GADGET SOUNDNESS TOOTH.** If every boolean gate and the recompose gate of a range
gadget vanish mod `p`, and the target + its bits are canonical, then the target lies in
`[0, 2^certFValueBits)` over ℤ. This is exactly the feasibility inequality `Market.CertF` named as
"riding the standard AIR range gadget" — now PROVED, not deferred. -/
theorem rangeGadget_forces_range (a : Assignment) (col : Nat) (bc : Nat → Nat)
    (hbool : ∀ j < certFValueBits, (boolExpr bc j).eval a ≡ 0 [ZMOD 2013265921])
    (hrec : (recomposeExpr col bc).eval a ≡ 0 [ZMOD 2013265921])
    (hcolCanon : CanonCell (a col))
    (hbitCanon : ∀ j < certFValueBits, CanonCell (a (bc j))) :
    0 ≤ a col ∧ a col < 2 ^ certFValueBits := by
  set S := ((List.range certFValueBits).map (fun j => (2 : Int) ^ j * a (bc j))).sum with hS
  have hbitBool : ∀ j < certFValueBits, (a (bc j) = 0 ∨ a (bc j) = 1) := fun j hj =>
    binary_of_boolExpr (hbool j hj) (hbitCanon j hj)
  -- the recompose gate pins `a col ≡ S`
  have hcolS : a col ≡ S [ZMOD 2013265921] := by
    have h : (a col - S) ≡ 0 [ZMOD 2013265921] := by rw [← recomposeExpr_eval]; exact hrec
    obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp h
    exact Int.modEq_iff_dvd.mpr ⟨-k, by linear_combination -hk⟩
  -- `S ∈ [0, 2^bits)`
  obtain ⟨hS0, hS1⟩ := bitsum_bounds a bc certFValueBits hbitBool
  have hcol : a col = S :=
    eq_of_modEq_of_canon hcolS hcolCanon ⟨hS0, lt_trans hS1 (by norm_num [certFValueBits])⟩
  exact ⟨by rw [hcol]; exact hS0, by rw [hcol]; exact hS1⟩

/-- A satisfying tight recompose gate forces the target below the policy bit bound.  Booleanity is
supplied by the historical 28-bit gadget; the added gate is therefore only one affine equality per
target, not a duplicate bit-decomposition. -/
theorem tightRecompose_forces_range (a : Assignment) (bits col : Nat) (bc : Nat → Nat)
    (hbits : bits ≤ certFValueBits)
    (hbool : ∀ j < bits, (boolExpr bc j).eval a ≡ 0 [ZMOD 2013265921])
    (hrec : (tightRecomposeExpr bits col bc).eval a ≡ 0 [ZMOD 2013265921])
    (hcolCanon : CanonCell (a col))
    (hbitCanon : ∀ j < bits, CanonCell (a (bc j))) :
    0 ≤ a col ∧ a col < 2 ^ bits := by
  set S := ((List.range bits).map (fun j => (2 : Int) ^ j * a (bc j))).sum with hS
  have hbitBool : ∀ j < bits, (a (bc j) = 0 ∨ a (bc j) = 1) := fun j hj =>
    binary_of_boolExpr (hbool j hj) (hbitCanon j hj)
  have hcolS : a col ≡ S [ZMOD 2013265921] := by
    have h : (a col - S) ≡ 0 [ZMOD 2013265921] := by
      rw [← tightRecomposeExpr_eval]
      exact hrec
    obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp h
    exact Int.modEq_iff_dvd.mpr ⟨-k, by linear_combination -hk⟩
  obtain ⟨hS0, hS1⟩ := bitsum_bounds a bc bits hbitBool
  have hpow : (2 : ℤ) ^ bits ≤ 2 ^ certFValueBits :=
    pow_le_pow_right₀ (by norm_num) hbits
  have hSp : S < 2013265921 := by
    have h28 : (2 : ℤ) ^ certFValueBits < 2013265921 := by norm_num [certFValueBits]
    exact (lt_of_lt_of_le hS1 hpow).trans h28
  have hcol : a col = S := eq_of_modEq_of_canon hcolS hcolCanon ⟨hS0, hSp⟩
  exact ⟨by rw [hcol]; exact hS0, by rw [hcol]; exact hS1⟩

/-! ## §6 — The EMIT-SOUNDNESS BRIDGE: a `Satisfied2`-satisfying Cert-F trace forces the certificate.

GENERIC over the public program `p : CertFProg` — NOT just `ring3Prog`. This section establishes the
modular field facts for every descriptor produced by the total function. Registration still needs
an EMITTED + byte-pinned artifact; interpreting those facts as an integer `Market.Certified` also
needs the honest aggregate no-wrap discharge made explicit in §7.

The honest trace is `TRACE_HEIGHT = 8` identical rows of one assignment `a` (the twin of
`cert_f_air.rs::base_trace`, whose every row is the same certificate data). We extract, from
`Satisfied2`, that every gate body vanishes on `a`, then read the certificate soundness off `a`
using §5's range-gadget tooth for the feasibility families and the arithmetic gates for
conservation, the slack pins, the gap, and the objective. This is the theorem `cert_f_air.rs`
could only *test*. -/

/-- The all-present flat memory boundary is irrelevant here (the descriptor declares no mem/map ops),
so the boundary images are free — take the zero images over the empty address list. -/
def m0 : ℤ → ℤ := fun _ => 0
def f0 : ℤ → ℤ × Nat := fun _ => (0, 0)

/-- The honest constant trace: `TRACE_HEIGHT = 8` identical rows of `a`, empty auxiliary tables
(no mem/map ops), and the objective column published as the single public input. -/
def constTrace (p : CertFProg) (a : Assignment) : VmTrace :=
  { rows := List.replicate 8 a
  , pub  := fun _ => a p.objCol
  , tf   := fun _ => [] }

@[simp] theorem constTrace_rows_length (p : CertFProg) (a : Assignment) :
    (constTrace p a).rows.length = 8 := by
  simp [constTrace]

@[simp] theorem constTrace_loc0 (p : CertFProg) (a : Assignment) :
    (envAt (constTrace p a) 0).loc = a := by
  funext k; simp [envAt, constTrace, List.getD]

/-- **Extraction: a satisfied descriptor makes every one of its gate bodies vanish on `a`.** Read off
row 0 (which is NOT the last row, `1 ≠ 8`, so the `when_transition` gate fires). -/
theorem gate_vanishes {hash : List ℤ → ℤ} {p : CertFProg} {a : Assignment}
    (hsat : Satisfied2 hash (certFDescriptorOf p) m0 f0 [] (constTrace p a))
    {body : EmittedExpr} (hmem : egate body ∈ certFConstraints p) :
    body.eval a ≡ 0 [ZMOD 2013265921] := by
  have hc : egate body ∈ (certFDescriptorOf p).constraints := hmem
  have h := hsat.rowConstraints 0 (by simp) (egate body) hc
  simpa [egate, VmConstraint2.holdsAt, VmConstraint.holdsVm] using h

/-- **Extraction: the objective public-input binding.** On the first row (`isFirst = true`) the
`piBinding` forces the objective column to equal the published clearing volume. -/
theorem obj_pi_bound {hash : List ℤ → ℤ} {p : CertFProg} {a : Assignment}
    (hsat : Satisfied2 hash (certFDescriptorOf p) m0 f0 [] (constTrace p a)) :
    a p.objCol ≡ (constTrace p a).pub 0 [ZMOD 2013265921] := by
  have hmem : (VmConstraint2.base (.piBinding .first p.objCol 0)) ∈ (certFDescriptorOf p).constraints := by
    show _ ∈ certFConstraints p
    apply List.mem_append_left
    simp only [certFCoreConstraints]
    apply List.mem_append_right; exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)
  have h := hsat.rowConstraints 0 (by simp) _ hmem
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, envAt, constTrace] using h

/-! ### Membership helpers for the constraint families (byte-position bookkeeping). -/

/-- The conservation gate for node `i` is in the constraint list (the leftmost family). -/
theorem cons_mem (p : CertFProg) (i : Nat) (hi : i < p.nNodes) :
    egate (consBody p i) ∈ certFConstraints p := by
  have hin : egate (consBody p i)
      ∈ (List.range p.nNodes).map (fun i => egate (consBody p i)) :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  apply List.mem_append_left
  simp only [certFCoreConstraints]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hin)))))

/-- The box-lower range gadget for edge `e` sits in the second family (`FLO`); every one of its
boolean gates and its recompose gate is in the constraint list. -/
theorem boxLower_gadget_mem (p : CertFProg) (e : Nat) (he : e < p.m) :
    ∀ c ∈ rangeGadget (p.fCol e) (fun j => p.rangeBitCol e j),
      c ∈ certFConstraints p := by
  intro c hc
  have hflat : c ∈ ((List.range p.m).map (fun e =>
      rangeGadget (p.fCol e) (fun j => p.rangeBitCol e j))).flatten := by
    apply List.mem_flatten.mpr
    exact ⟨_, List.mem_map.mpr ⟨e, List.mem_range.mpr he, rfl⟩, hc⟩
  apply List.mem_append_left
  simp only [certFCoreConstraints]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hflat)))))

/-- Generic: membership in a `(map f l).flatten`. -/
theorem flatten_map_mem {α β : Type*} (f : α → List β) (l : List α) (x : β) (a : α)
    (ha : a ∈ l) (hx : x ∈ f a) : x ∈ (l.map f).flatten :=
  List.mem_flatten.mpr ⟨f a, List.mem_map.mpr ⟨a, ha, rfl⟩, hx⟩

/-- The slack range gadget for edge `e` (fourth family, `FSL`). -/
theorem slack_gadget_mem (p : CertFProg) (e : Nat) (he : e < p.m) :
    ∀ c ∈ rangeGadget (p.sCol e) (fun j => p.rangeBitCol (2 * p.m + e) j),
      c ∈ certFConstraints p := by
  intro c hc
  have hflat := flatten_map_mem
    (fun e => rangeGadget (p.sCol e) (fun j => p.rangeBitCol (2 * p.m + e) j))
    (List.range p.m) c e (List.mem_range.mpr he) hc
  apply List.mem_append_left
  simp only [certFCoreConstraints]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ hflat)))

/-- The box-upper gate + range gadget for edge `e` (third family, `FUP`). -/
theorem boxUpper_cell_mem (p : CertFProg) (e : Nat) (he : e < p.m) :
    ∀ c ∈ (egate (.add (esub (EmittedExpr.var (p.uCol e)) (.const (p.cAt e)))
              (EmittedExpr.var (p.fCol e)))
          :: rangeGadget (p.uCol e) (fun j => p.rangeBitCol (p.m + e) j)),
      c ∈ certFConstraints p := by
  intro c hc
  have hflat := flatten_map_mem
    (fun e => egate (.add (esub (EmittedExpr.var (p.uCol e)) (.const (p.cAt e)))
                (EmittedExpr.var (p.fCol e)))
              :: rangeGadget (p.uCol e) (fun j => p.rangeBitCol (p.m + e) j))
    (List.range p.m) c e (List.mem_range.mpr he) hc
  apply List.mem_append_left
  simp only [certFCoreConstraints]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_right _ hflat))))

/-- The dual-feas gate + range gadget for edge `e` (fifth family, `FDU`). -/
theorem dual_cell_mem (p : CertFProg) (e : Nat) (he : e < p.m) :
    ∀ c ∈ (egate (esub (EmittedExpr.var (p.dCol e))
              (esub (.add (esub (EmittedExpr.var (p.piCol (p.headAt e)))
                              (EmittedExpr.var (p.piCol (p.tailAt e))))
                        (EmittedExpr.var (p.sCol e)))
                    (.const (p.wAt e))))
          :: rangeGadget (p.dCol e) (fun j => p.rangeBitCol (3 * p.m + e) j)),
      c ∈ certFConstraints p := by
  intro c hc
  have hflat := flatten_map_mem
    (fun e => egate (esub (EmittedExpr.var (p.dCol e))
                (esub (.add (esub (EmittedExpr.var (p.piCol (p.headAt e)))
                                (EmittedExpr.var (p.piCol (p.tailAt e))))
                          (EmittedExpr.var (p.sCol e)))
                      (.const (p.wAt e))))
              :: rangeGadget (p.dCol e) (fun j => p.rangeBitCol (3 * p.m + e) j))
    (List.range p.m) c e (List.mem_range.mpr he) hc
  apply List.mem_append_left
  simp only [certFCoreConstraints]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hflat))

/-- The gap gate + range gadget (sixth family, `GAP`). -/
theorem gap_mem (p : CertFProg) : ∀ c ∈
    (egate ((List.range p.m).foldl
        (fun body e =>
          esub (.add body (.mul (.const (p.cAt e)) (EmittedExpr.var (p.sCol e))))
               (.mul (.const (p.wAt e)) (EmittedExpr.var (p.fCol e))))
        (esub (EmittedExpr.var p.gCol) (.const p.eps)))
      :: rangeGadget p.gCol (fun j => p.rangeBitCol (4 * p.m) j)),
      c ∈ certFConstraints p := by
  intro c hc
  apply List.mem_append_left
  simp only [certFCoreConstraints]
  exact List.mem_append_left _ (List.mem_append_right _ hc)

/-- The objective gate `obj == wᵀf` (seventh family, head of the final chunk). -/
theorem obj_gate_mem (p : CertFProg) :
    egate ((List.range p.m).foldl
        (fun body e => esub body (.mul (.const (p.wAt e)) (EmittedExpr.var (p.fCol e))))
        (EmittedExpr.var p.objCol)) ∈ certFConstraints p := by
  apply List.mem_append_left
  simp only [certFCoreConstraints]
  exact List.mem_append_right _ List.mem_cons_self

/-! ### Membership of the enforced integer-admission guards. -/

theorem flow_tight_mem (p : CertFProg) (e : Nat) (he : e < p.m) :
    egate (tightRecomposeExpr p.effectiveFlowBits (p.fCol e)
      (fun j => p.rangeBitCol e j)) ∈ certFConstraints p := by
  apply List.mem_append_right
  simp only [certFAdmissionConstraints]
  apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨e, List.mem_range.mpr he, rfl⟩

theorem slack_tight_mem (p : CertFProg) (e : Nat) (he : e < p.m) :
    egate (tightRecomposeExpr p.effectiveSlackBits (p.sCol e)
      (fun j => p.rangeBitCol (2 * p.m + e) j)) ∈ certFConstraints p := by
  apply List.mem_append_right
  simp only [certFAdmissionConstraints]
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨e, List.mem_range.mpr he, rfl⟩

theorem potential_gadget_mem (p : CertFProg) (i : Nat) (hi : i < p.nNodes) :
    ∀ c ∈ rangeGadget (p.piCol i) (fun j => p.potentialRangeBitCol i j),
      c ∈ certFConstraints p := by
  intro c hc
  apply List.mem_append_right
  simp only [certFAdmissionConstraints]
  apply List.mem_append_right
  exact flatten_map_mem
    (fun i => rangeGadget (p.piCol i) (fun j => p.potentialRangeBitCol i j))
    (List.range p.nNodes) c i (List.mem_range.mpr hi) hc

/-! ### The per-gadget gate membership within one `rangeGadget`. -/

theorem boolGate_in_gadget (col : Nat) (bc : Nat → Nat) (j : Nat) (hj : j < certFValueBits) :
    egate (boolExpr bc j) ∈ rangeGadget col bc :=
  List.mem_append_left _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)

theorem recGate_in_gadget (col : Nat) (bc : Nat → Nat) :
    egate (recomposeExpr col bc) ∈ rangeGadget col bc :=
  List.mem_append_right _ (List.mem_singleton.mpr rfl)

/-! ### §6.1 — The emit-soundness theorems: a satisfied Cert-F trace forces the certificate.
All GENERIC over the public program `p : CertFProg`. -/

/-- **CONSERVATION SOUNDNESS.** A `Satisfied2`-satisfying trace makes every node's conservation
residual `Σ_{head=i} f_e − Σ_{tail=i} f_e` vanish mod `p` — `A f = 0` over the field. -/
theorem certFDescriptor_conservation_sound {hash : List ℤ → ℤ} {p : CertFProg} {a : Assignment}
    (hsat : Satisfied2 hash (certFDescriptorOf p) m0 f0 [] (constTrace p a))
    (i : Nat) (hi : i < p.nNodes) :
    (consBody p i).eval a ≡ 0 [ZMOD 2013265921] :=
  gate_vanishes hsat (cons_mem p i hi)

/-- **BOX-LOWER SOUNDNESS `f_e ≥ 0`.** The box-lower range gadget forces every flow into
`[0, 2^certFValueBits)` — the primal box lower bound (via §5's tooth). -/
theorem certFDescriptor_box_lower_sound {hash : List ℤ → ℤ} {p : CertFProg} {a : Assignment}
    (hcanon : ∀ col, CanonCell (a col))
    (hsat : Satisfied2 hash (certFDescriptorOf p) m0 f0 [] (constTrace p a))
    (e : Nat) (he : e < p.m) :
    0 ≤ a (p.fCol e) ∧ a (p.fCol e) < 2 ^ certFValueBits := by
  refine rangeGadget_forces_range a (p.fCol e) (fun j => p.rangeBitCol e j)
    (fun j hj => ?_) ?_ (hcanon _) (fun j _ => hcanon _)
  · exact gate_vanishes hsat (boxLower_gadget_mem p e he _ (boolGate_in_gadget _ _ j hj))
  · exact gate_vanishes hsat (boxLower_gadget_mem p e he _ (recGate_in_gadget _ _))

/-- **SLACK-SIGN SOUNDNESS `s_e ≥ 0`.** The slack range gadget forces every dual slack into
`[0, 2^certFValueBits)` — the dual sign constraint (via §5's tooth). -/
theorem certFDescriptor_slack_sound {hash : List ℤ → ℤ} {p : CertFProg} {a : Assignment}
    (hcanon : ∀ col, CanonCell (a col))
    (hsat : Satisfied2 hash (certFDescriptorOf p) m0 f0 [] (constTrace p a))
    (e : Nat) (he : e < p.m) :
    0 ≤ a (p.sCol e) ∧ a (p.sCol e) < 2 ^ certFValueBits := by
  refine rangeGadget_forces_range a (p.sCol e)
    (fun j => p.rangeBitCol (2 * p.m + e) j) (fun j hj => ?_) ?_ (hcanon _) (fun j _ => hcanon _)
  · exact gate_vanishes hsat (slack_gadget_mem p e he _ (boolGate_in_gadget _ _ j hj))
  · exact gate_vanishes hsat (slack_gadget_mem p e he _ (recGate_in_gadget _ _))

/-- The deployed registry policy, not a caller hypothesis, forces every primal flow below its
program-specific bound. -/
theorem certFDescriptor_flow_tight_sound {hash : List ℤ → ℤ} {p : CertFProg} {a : Assignment}
    (hcanon : ∀ col, CanonCell (a col))
    (hsat : Satisfied2 hash (certFDescriptorOf p) m0 f0 [] (constTrace p a))
    (e : Nat) (he : e < p.m) :
    0 ≤ a (p.fCol e) ∧ a (p.fCol e) < 2 ^ p.effectiveFlowBits := by
  refine tightRecompose_forces_range a p.effectiveFlowBits (p.fCol e)
    (fun j => p.rangeBitCol e j) (Nat.min_le_right _ _) (fun j hj => ?_) ?_
    (hcanon _) (fun j _ => hcanon _)
  · exact gate_vanishes hsat
      (boxLower_gadget_mem p e he _ (boolGate_in_gadget _ _ j (lt_of_lt_of_le hj (Nat.min_le_right _ _))))
  · exact gate_vanishes hsat (flow_tight_mem p e he)

/-- The deployed registry policy forces every dual slack below its program-specific bound. -/
theorem certFDescriptor_slack_tight_sound {hash : List ℤ → ℤ} {p : CertFProg} {a : Assignment}
    (hcanon : ∀ col, CanonCell (a col))
    (hsat : Satisfied2 hash (certFDescriptorOf p) m0 f0 [] (constTrace p a))
    (e : Nat) (he : e < p.m) :
    0 ≤ a (p.sCol e) ∧ a (p.sCol e) < 2 ^ p.effectiveSlackBits := by
  refine tightRecompose_forces_range a p.effectiveSlackBits (p.sCol e)
    (fun j => p.rangeBitCol (2 * p.m + e) j) (Nat.min_le_right _ _) (fun j hj => ?_) ?_
    (hcanon _) (fun j _ => hcanon _)
  · exact gate_vanishes hsat
      (slack_gadget_mem p e he _ (boolGate_in_gadget _ _ j (lt_of_lt_of_le hj (Nat.min_le_right _ _))))
  · exact gate_vanishes hsat (slack_tight_mem p e he)

/-- Potentials are now range-checked in the descriptor itself; v1 left these columns unrestricted. -/
theorem certFDescriptor_potential_sound {hash : List ℤ → ℤ} {p : CertFProg} {a : Assignment}
    (hcanon : ∀ col, CanonCell (a col))
    (hsat : Satisfied2 hash (certFDescriptorOf p) m0 f0 [] (constTrace p a))
    (i : Nat) (hi : i < p.nNodes) :
    0 ≤ a (p.piCol i) ∧ a (p.piCol i) < 2 ^ certFValueBits := by
  refine rangeGadget_forces_range a (p.piCol i) (fun j => p.potentialRangeBitCol i j)
    (fun j hj => ?_) ?_ (hcanon _) (fun j _ => hcanon _)
  · exact gate_vanishes hsat
      (potential_gadget_mem p i hi _ (boolGate_in_gadget _ _ j hj))
  · exact gate_vanishes hsat
      (potential_gadget_mem p i hi _ (recGate_in_gadget _ _))

/-- **GAP-SLACK RANGE `g ≥ 0`.** The gap slack `g` is forced into `[0, 2^certFValueBits)` by its
range gadget. Combined with `certFDescriptor_gap_gate_sound` (the pin `g ≡ ε − (cᵀs − wᵀf)`),
this is the ε-optimality clause over the field. -/
theorem certFDescriptor_gap_sound {hash : List ℤ → ℤ} {p : CertFProg} {a : Assignment}
    (hcanon : ∀ col, CanonCell (a col))
    (hsat : Satisfied2 hash (certFDescriptorOf p) m0 f0 [] (constTrace p a)) :
    0 ≤ a p.gCol ∧ a p.gCol < 2 ^ certFValueBits := by
  refine rangeGadget_forces_range a p.gCol
    (fun j => p.rangeBitCol (4 * p.m) j) (fun j hj => ?_) ?_ (hcanon _) (fun j _ => hcanon _)
  · exact gate_vanishes hsat (gap_mem p _ (List.mem_cons_of_mem _ (boolGate_in_gadget _ _ j hj)))
  · exact gate_vanishes hsat (gap_mem p _ (List.mem_cons_of_mem _ (recGate_in_gadget _ _)))

/-- **BOX-UPPER SOUNDNESS `f_e ≤ c_e`.** The box-upper slack `u_e` is forced `≥ 0` by its range
gadget, and its gate pins `u_e == c_e − f_e` — so `c_e − f_e ≥ 0` over the field, i.e. the primal
box upper bound. -/
theorem certFDescriptor_box_upper_sound {hash : List ℤ → ℤ} {p : CertFProg} {a : Assignment}
    (hcanon : ∀ col, CanonCell (a col))
    (hsat : Satisfied2 hash (certFDescriptorOf p) m0 f0 [] (constTrace p a))
    (e : Nat) (he : e < p.m) :
    (0 ≤ a (p.uCol e) ∧ a (p.uCol e) < 2 ^ certFValueBits)
    ∧ (a (p.uCol e) - p.cAt e + a (p.fCol e)) ≡ 0 [ZMOD 2013265921] := by
  refine ⟨rangeGadget_forces_range a (p.uCol e)
      (fun j => p.rangeBitCol (p.m + e) j) (fun j hj => ?_) ?_ (hcanon _) (fun j _ => hcanon _), ?_⟩
  · exact gate_vanishes hsat (boxUpper_cell_mem p e he _ (List.mem_cons_of_mem _ (boolGate_in_gadget _ _ j hj)))
  · exact gate_vanishes hsat (boxUpper_cell_mem p e he _ (List.mem_cons_of_mem _ (recGate_in_gadget _ _)))
  · have h := gate_vanishes hsat (boxUpper_cell_mem p e he _ (List.mem_cons_self))
    have : ((esub (EmittedExpr.var (p.uCol e)) (.const (p.cAt e))).add
              (EmittedExpr.var (p.fCol e))).eval a
            = a (p.uCol e) - p.cAt e + a (p.fCol e) := by
      simp only [esub, EmittedExpr.eval]; ring
    rw [this] at h; exact h

/-- **DUAL-FEASIBILITY SOUNDNESS `π_head − π_tail + s_e − w_e ≥ 0`.** The dual slack `d_e` is forced
`≥ 0` by its range gadget, and its gate pins `d_e == π_head − π_tail + s_e − w_e` — so `Aᵀπ + s ≥ w`
over the field. -/
theorem certFDescriptor_dual_sound {hash : List ℤ → ℤ} {p : CertFProg} {a : Assignment}
    (hcanon : ∀ col, CanonCell (a col))
    (hsat : Satisfied2 hash (certFDescriptorOf p) m0 f0 [] (constTrace p a))
    (e : Nat) (he : e < p.m) :
    (0 ≤ a (p.dCol e) ∧ a (p.dCol e) < 2 ^ certFValueBits)
    ∧ (a (p.dCol e)
        - (a (p.piCol (p.headAt e)) - a (p.piCol (p.tailAt e))
           + a (p.sCol e) - p.wAt e)) ≡ 0 [ZMOD 2013265921] := by
  refine ⟨rangeGadget_forces_range a (p.dCol e)
      (fun j => p.rangeBitCol (3 * p.m + e) j) (fun j hj => ?_) ?_ (hcanon _) (fun j _ => hcanon _), ?_⟩
  · exact gate_vanishes hsat (dual_cell_mem p e he _ (List.mem_cons_of_mem _ (boolGate_in_gadget _ _ j hj)))
  · exact gate_vanishes hsat (dual_cell_mem p e he _ (List.mem_cons_of_mem _ (recGate_in_gadget _ _)))
  · have h := gate_vanishes hsat (dual_cell_mem p e he _ (List.mem_cons_self))
    have : (esub (EmittedExpr.var (p.dCol e))
              (esub (.add (esub (EmittedExpr.var (p.piCol (p.headAt e)))
                              (EmittedExpr.var (p.piCol (p.tailAt e))))
                        (EmittedExpr.var (p.sCol e)))
                    (.const (p.wAt e)))).eval a
            = a (p.dCol e)
              - (a (p.piCol (p.headAt e)) - a (p.piCol (p.tailAt e))
                 + a (p.sCol e) - p.wAt e) := by
      simp only [esub, EmittedExpr.eval]; ring
    rw [this] at h; exact h

/-! ### §6.2 — The gap and objective GATE pins (previously only range-checked, never extracted:
without `g ≡ ε − (cᵀs − wᵀf)` the bundle's `g ≥ 0` said nothing about ε). -/

/-- `cᵀs − wᵀf` read off the trace columns — the duality gap over the field. -/
def gapOf (p : CertFProg) (a : Assignment) : ℤ :=
  ((List.range p.m).map (fun e => p.cAt e * a (p.sCol e) - p.wAt e * a (p.fCol e))).sum

/-- `wᵀf` read off the trace columns — the cleared volume over the field. -/
def objOf (p : CertFProg) (a : Assignment) : ℤ :=
  ((List.range p.m).map (fun e => p.wAt e * a (p.fCol e))).sum

/-- The gap-gate fold evaluates to `e0 + Σ_e (c_e·s_e − w_e·f_e)`. -/
theorem gap_foldl_eval (p : CertFProg) (a : Assignment) :
    ∀ (l : List Nat) (e0 : EmittedExpr),
      (l.foldl (fun body e =>
          esub (.add body (.mul (.const (p.cAt e)) (EmittedExpr.var (p.sCol e))))
               (.mul (.const (p.wAt e)) (EmittedExpr.var (p.fCol e)))) e0).eval a
        = e0.eval a
          + ((l.map (fun e => p.cAt e * a (p.sCol e) - p.wAt e * a (p.fCol e))).sum) := by
  intro l
  induction l with
  | nil => intro e0; simp
  | cons x xs ih =>
      intro e0
      rw [List.foldl_cons, ih]
      simp only [List.map_cons, List.sum_cons, esub, EmittedExpr.eval]
      ring

/-- The objective-gate fold evaluates to `e0 − Σ_e w_e·f_e`. -/
theorem obj_foldl_eval (p : CertFProg) (a : Assignment) :
    ∀ (l : List Nat) (e0 : EmittedExpr),
      (l.foldl (fun body e =>
          esub body (.mul (.const (p.wAt e)) (EmittedExpr.var (p.fCol e)))) e0).eval a
        = e0.eval a - ((l.map (fun e => p.wAt e * a (p.fCol e))).sum) := by
  intro l
  induction l with
  | nil => intro e0; simp
  | cons x xs ih =>
      intro e0
      rw [List.foldl_cons, ih]
      simp only [List.map_cons, List.sum_cons, esub, EmittedExpr.eval]
      ring

/-- **GAP-GATE SOUNDNESS.** The gap gate pins the gap slack: `g ≡ ε − (cᵀs − wᵀf)` mod `p`.
Together with `certFDescriptor_gap_sound` (`g ≥ 0`), this is `cᵀs − wᵀf ≤ ε` over the field —
the ε-optimality clause, the whole point of the certificate
(`Market.certifies_epsilon_optimal`). -/
theorem certFDescriptor_gap_gate_sound {hash : List ℤ → ℤ} {p : CertFProg} {a : Assignment}
    (hsat : Satisfied2 hash (certFDescriptorOf p) m0 f0 [] (constTrace p a)) :
    a p.gCol ≡ p.eps - gapOf p a [ZMOD 2013265921] := by
  have h := gate_vanishes hsat (gap_mem p _ List.mem_cons_self)
  have hev : ((List.range p.m).foldl
      (fun body e =>
        esub (.add body (.mul (.const (p.cAt e)) (EmittedExpr.var (p.sCol e))))
             (.mul (.const (p.wAt e)) (EmittedExpr.var (p.fCol e))))
      (esub (EmittedExpr.var p.gCol) (.const p.eps))).eval a
      = a p.gCol - p.eps + gapOf p a := by
    rw [gap_foldl_eval]
    simp only [esub, EmittedExpr.eval, gapOf]
    ring
  rw [hev] at h
  obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp h
  exact Int.modEq_iff_dvd.mpr ⟨-k, by linear_combination -hk⟩

/-- **OBJECTIVE-GATE SOUNDNESS.** The objective gate pins the published column: `obj ≡ wᵀf` mod `p`
— with `obj_pi_bound`, the world-visible public input IS the cleared volume of the hidden flow. -/
theorem certFDescriptor_obj_gate_sound {hash : List ℤ → ℤ} {p : CertFProg} {a : Assignment}
    (hsat : Satisfied2 hash (certFDescriptorOf p) m0 f0 [] (constTrace p a)) :
    a p.objCol ≡ objOf p a [ZMOD 2013265921] := by
  have h := gate_vanishes hsat (obj_gate_mem p)
  have hev : ((List.range p.m).foldl
      (fun body e =>
        esub body (.mul (.const (p.wAt e)) (EmittedExpr.var (p.fCol e))))
      (EmittedExpr.var p.objCol)).eval a
      = a p.objCol - objOf p a := by
    rw [obj_foldl_eval]
    simp only [EmittedExpr.eval, objOf]
  rw [hev] at h
  obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp h
  exact Int.modEq_iff_dvd.mpr ⟨-k, by linear_combination -hk⟩

/-- **THE EMIT-SOUNDNESS BRIDGE (the theorem `cert_f_air.rs` could only TEST), GENERIC over the
public program.** A `Satisfied2`-satisfying Cert-F trace (over a canonical assignment — the
deployed range-check invariant) forces the FULL Cert-F certificate over the BabyBear field, for
ANY `p : CertFProg`, ALL FIVE families PLUS the gate pins:

  * `A f = 0` (conservation);
  * `f ≥ 0` (box lower) and `u ≥ 0` with `u ≡ c − f` (box upper);
  * `s ≥ 0` (slack sign);
  * `d ≥ 0` with `d ≡ Aᵀπ + s − w` (dual feasibility);
  * `g ≥ 0` with `g ≡ ε − (cᵀs − wᵀf)` (the ε-optimality gap);
  * `obj ≡ wᵀf` (the published cleared volume is the real objective).

This is the modular precursor of the certificate `Market.Certified` decides. It must be composed
with §7's aggregate no-wrap contract before the ordered-ring keystone
`certifies_epsilon_optimal` applies; per-cell range bounds alone do not justify that step. -/
theorem certFDescriptor_emit_sound {hash : List ℤ → ℤ} (p : CertFProg) {a : Assignment}
    (hcanon : ∀ col, CanonCell (a col))
    (hsat : Satisfied2 hash (certFDescriptorOf p) m0 f0 [] (constTrace p a)) :
    (∀ i < p.nNodes, (consBody p i).eval a ≡ 0 [ZMOD 2013265921])
    ∧ (∀ e < p.m, 0 ≤ a (p.fCol e))
    ∧ (∀ e < p.m, 0 ≤ a (p.uCol e)
         ∧ (a (p.uCol e) - p.cAt e + a (p.fCol e)) ≡ 0 [ZMOD 2013265921])
    ∧ (∀ e < p.m, 0 ≤ a (p.sCol e))
    ∧ (∀ e < p.m, 0 ≤ a (p.dCol e)
         ∧ (a (p.dCol e)
             - (a (p.piCol (p.headAt e)) - a (p.piCol (p.tailAt e))
                + a (p.sCol e) - p.wAt e)) ≡ 0 [ZMOD 2013265921])
    ∧ (0 ≤ a p.gCol ∧ a p.gCol ≡ p.eps - gapOf p a [ZMOD 2013265921])
    ∧ a p.objCol ≡ objOf p a [ZMOD 2013265921] :=
  ⟨fun i hi => certFDescriptor_conservation_sound hsat i hi
  , fun e he => (certFDescriptor_box_lower_sound hcanon hsat e he).1
  , fun e he => ⟨(certFDescriptor_box_upper_sound hcanon hsat e he).1.1
               , (certFDescriptor_box_upper_sound hcanon hsat e he).2⟩
  , fun e he => (certFDescriptor_slack_sound hcanon hsat e he).1
  , fun e he => ⟨(certFDescriptor_dual_sound hcanon hsat e he).1.1
               , (certFDescriptor_dual_sound hcanon hsat e he).2⟩
  , ⟨(certFDescriptor_gap_sound hcanon hsat).1, certFDescriptor_gap_gate_sound hsat⟩
  , certFDescriptor_obj_gate_sound hsat⟩

/-! ## §7 — The modular-to-integer bridge.

`certFDescriptor_emit_sound` deliberately stops at field congruences.  A congruence is not an
integer equality: an aggregate conservation row, dual expression, objective, or gap can differ from
its intended value by a whole BabyBear modulus even though every individually range-checked cell is
small.  This section states the exact, reusable no-wrap contract needed to cross that boundary and
then proves the integer Cert-F predicate.

The contract is on the *aggregate residuals*, not merely on individual cells.  It therefore makes
the degree / coefficient accounting visible to each registered program: a registrar can discharge
the fields below from public degree and coefficient bounds (or from tighter program-specific range
gadgets), but the generic theorem does not pretend those bounds follow from 28-bit cells alone.
-/

/-- The BabyBear modulus used by the deployed descriptor, as an integer. -/
def babyBearModulus : ℤ := 2013265921

/-- An integer is in the unique zero-residue window.  This is the minimal symmetric no-wrap
condition used below: if `x ≡ 0 (mod p)` and `-p < x < p`, then `x = 0`. -/
def InZeroResidueWindow (x : ℤ) : Prop :=
  -babyBearModulus < x ∧ x < babyBearModulus

/-- **Aggregate no-wrap contract for Cert-F.**  Every field gate which must become an integer
equality gets a bound on its complete integer residual.  In particular:

* `conservation` accounts for all incident flows at a node (hence node degree);
* `boxUpper` accounts for both range cells and the public capacity;
* `dual` accounts for both potentials, slack, and the public weight;
* `gap` accounts for the full `cᵀs − wᵀf` weighted sums and `ε`;
* `objective` accounts for the full weighted objective, not each product separately.

These are intentionally hypotheses, not consequences of per-cell canonicality. -/
structure CertFIntegerNoWrap (p : CertFProg) (a : Assignment) : Prop where
  conservation : ∀ i < p.nNodes, InZeroResidueWindow ((consBody p i).eval a)
  boxUpper : ∀ e < p.m,
    InZeroResidueWindow (a (p.uCol e) - p.cAt e + a (p.fCol e))
  dual : ∀ e < p.m,
    InZeroResidueWindow
      (a (p.dCol e)
        - (a (p.piCol (p.headAt e)) - a (p.piCol (p.tailAt e))
           + a (p.sCol e) - p.wAt e))
  gap : InZeroResidueWindow (a p.gCol - p.eps + gapOf p a)
  objective : InZeroResidueWindow (a p.objCol - objOf p a)

/-- The exact list-indexed integer Cert-F predicate represented by the descriptor.  This is the
integer, rather than BabyBear-modular, form of all five certificate families, plus the published
objective equality.  `consBody` is the incidence row `A f`; the dual inequality is
`Aᵀπ + s ≥ w`; and `gapOf` is exactly `cᵀs − wᵀf`. -/
structure IntegerCertF (p : CertFProg) (a : Assignment) : Prop where
  conservation : ∀ i < p.nNodes, (consBody p i).eval a = 0
  flow_nonneg : ∀ e < p.m, 0 ≤ a (p.fCol e)
  flow_le_capacity : ∀ e < p.m, a (p.fCol e) ≤ p.cAt e
  slack_nonneg : ∀ e < p.m, 0 ≤ a (p.sCol e)
  dual_feasible : ∀ e < p.m,
    p.wAt e ≤ a (p.piCol (p.headAt e)) - a (p.piCol (p.tailAt e)) + a (p.sCol e)
  gap_le : gapOf p a ≤ p.eps
  objective_exact : a p.objCol = objOf p a

/-! ### §7.1 — Identification with `Market.Certified`.

The list-indexed predicate above is not a lookalike: the definitions below interpret the public
edge list as the usual incidence-matrix `FlowLP`, and the bridge theorem below returns
`Market.Certified` itself. -/

/-- Edge endpoints used by the descriptor are actual nodes of the public program.  The descriptor's
`getD` layout is total even for malformed programs, so this well-formedness condition is explicit at
the integer-LP boundary. -/
structure CertFProg.IntegerWellFormed (p : CertFProg) : Prop where
  tail_lt : ∀ e < p.m, p.tailAt e < p.nNodes
  head_lt : ∀ e < p.m, p.headAt e < p.nNodes

/-- **Registry admission condition for integer Cert-F soundness.**  A program is integer-admissible
only when (1) every endpoint is a real node and (2) *every canonical satisfying trace* has all five
aggregate residuals in the unique-residue window.  A single honest witness satisfying
`CertFIntegerNoWrap` is a non-vacuity example, not this uniform security theorem.

Current registries must either prove this property from program-wide public bounds or enforce the
needed tighter ranges in the descriptor.  Emission + byte pinning alone establishes only the §6
field theorem. -/
structure CertFProg.IntegerAdmission (p : CertFProg) : Prop where
  wellFormed : p.IntegerWellFormed
  noWrap_of_satisfied : ∀ (hash : List ℤ → ℤ) (a : Assignment),
    (∀ col, CanonCell (a col)) →
    Satisfied2 hash (certFDescriptorOf p) m0 f0 [] (constTrace p a) →
    CertFIntegerNoWrap p a

/-- Integer incidence coefficient of edge `e` in node row `i`: `+1` at the head and `-1` at the
tail (a self-loop contributes zero). -/
def incidenceCoeff (p : CertFProg) (i e : Nat) : ℤ :=
  (if p.headAt e == i then 1 else 0) - (if p.tailAt e == i then 1 else 0)

/-- The ordinary integer circulation LP denoted by a descriptor program. -/
def integerFlowLP (p : CertFProg) : Market.FlowLP (Fin p.nNodes) (Fin p.m) ℤ :=
  { A := fun i e => incidenceCoeff p i.1 e.1
  , w := fun e => p.wAt e.1
  , c := fun e => p.cAt e.1
  , ε := p.eps }

/-- Trace projections giving the primal flow, node potentials, and dual slacks. -/
def integerFlow (p : CertFProg) (a : Assignment) : Fin p.m → ℤ :=
  fun e => a (p.fCol e.1)
def integerPotential (p : CertFProg) (a : Assignment) : Fin p.nNodes → ℤ :=
  fun i => a (p.piCol i.1)
def integerSlack (p : CertFProg) (a : Assignment) : Fin p.m → ℤ :=
  fun e => a (p.sCol e.1)

/-- Both deployed programs have honest in-range endpoints; this closes the structural side of the
integer interpretation concretely (the aggregate arithmetic no-wrap side remains witness-bound). -/
theorem ring3Prog_integerWellFormed : ring3Prog.IntegerWellFormed := by
  constructor
  · intro e he
    have he' : e < 3 := by simpa [ring3Prog, CertFProg.m] using he
    interval_cases e <;> norm_num [ring3Prog, CertFProg.tailAt]
  · intro e he
    have he' : e < 3 := by simpa [ring3Prog, CertFProg.m] using he
    interval_cases e <;> norm_num [ring3Prog, CertFProg.headAt]

theorem market4Prog_integerWellFormed : market4Prog.IntegerWellFormed := by
  constructor
  · intro e he
    have he' : e < 4 := by simpa [market4Prog, CertFProg.m] using he
    interval_cases e <;> norm_num [market4Prog, CertFProg.tailAt]
  · intro e he
    have he' : e < 4 := by simpa [market4Prog, CertFProg.m] using he
    interval_cases e <;> norm_num [market4Prog, CertFProg.headAt]

/-- The scalar columns of the documented market4 optimum (`f=(500,200,200,300)`,
`π=(200,0,100)`, `s=(300,0,0,100)`, exact objective 180000 and gap zero).  Range-bit columns are
irrelevant to the aggregate no-wrap check and are set to zero here. -/
def market4HonestAssignment : Assignment := fun col =>
  if col < 4 then [500, 200, 200, 300].getD col 0
  else if col < 8 then [300, 0, 0, 100].getD (col - 4) 0
  else if col < 11 then [200, 0, 100].getD (col - 8) 0
  else if col = 11 then 180000
  else if col < 16 then [0, 300, 300, 0].getD (col - 12) 0
  else if col < 20 then 0
  else if col = 20 then 2000
  else 0

/-- **Concrete aggregate discharge.**  The real market4 witness lies in the unique-residue window
for every conservation, box, dual, whole-gap, and whole-objective residual.  This checks the large
weighted sums themselves (`180000`), not only their constituent 28-bit cells. -/
theorem market4Honest_noWrap :
    CertFIntegerNoWrap market4Prog market4HonestAssignment := by
  constructor
  · intro i hi
    have hi' : i < 3 := by simpa [market4Prog] using hi
    interval_cases i <;> simp only [InZeroResidueWindow] <;> decide
  · intro e he
    have he' : e < 4 := by simpa [market4Prog, CertFProg.m] using he
    interval_cases e <;> simp only [InZeroResidueWindow] <;> decide
  · intro e he
    have he' : e < 4 := by simpa [market4Prog, CertFProg.m] using he
    interval_cases e <;> simp only [InZeroResidueWindow] <;> decide
  · simp only [InZeroResidueWindow]; decide
  · simp only [InZeroResidueWindow]; decide

/-- Evaluate a conservation fold as the corresponding weighted list sum. -/
theorem cons_foldl_eval (p : CertFProg) (a : Assignment) (i : Nat) :
    ∀ (l : List Nat) (e0 : EmittedExpr),
      (l.foldl
        (fun body e =>
          let body := if p.headAt e == i then .add body (EmittedExpr.var (p.fCol e)) else body
          if p.tailAt e == i then esub body (EmittedExpr.var (p.fCol e)) else body)
        e0).eval a
      = e0.eval a
        + (l.map (fun e => incidenceCoeff p i e * a (p.fCol e))).sum := by
  intro l
  induction l with
  | nil => intro e0; simp
  | cons e es ih =>
      intro e0
      rw [List.foldl_cons, ih]
      simp only [List.map_cons, List.sum_cons]
      by_cases hh : p.headAt e == i <;> by_cases ht : p.tailAt e == i <;>
        simp [hh, ht, incidenceCoeff, esub, EmittedExpr.eval] <;> ring

/-- `consBody` is the integer incidence row dot the trace flow. -/
theorem consBody_eval_eq_list_sum (p : CertFProg) (a : Assignment) (i : Nat) :
    (consBody p i).eval a =
      ((List.range p.m).map (fun e => incidenceCoeff p i e * a (p.fCol e))).sum := by
  have h := cons_foldl_eval p a i (List.range p.m) (.const 0)
  simpa [consBody, EmittedExpr.eval] using h

/-- List-range and `Finset.range` sums agree. -/
theorem list_range_map_sum_eq_finset_sum {R : Type*} [AddCommMonoid R]
    (f : Nat → R) : ∀ n,
    ((List.range n).map f).sum = ∑ e ∈ Finset.range n, f e := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]
      simp

/-- The descriptor conservation expression is exactly the `FlowLP` matrix-vector product. -/
theorem consBody_eval_eq_mulVec (p : CertFProg) (a : Assignment) (i : Fin p.nNodes) :
    (consBody p i.1).eval a =
      Matrix.mulVec (integerFlowLP p).A (integerFlow p a) i := by
  rw [consBody_eval_eq_list_sum, list_range_map_sum_eq_finset_sum]
  simp only [integerFlowLP, integerFlow, Matrix.mulVec, dotProduct]
  rw [← Fin.sum_univ_eq_sum_range
    (fun e => incidenceCoeff p i.1 e * a (p.fCol e)) p.m]

/-- The transpose-incidence action is the head potential minus the tail potential. -/
theorem potential_vecMul_eq_difference (p : CertFProg) (a : Assignment)
    (hwell : p.IntegerWellFormed) (e : Fin p.m) :
    Matrix.vecMul (integerPotential p a) (integerFlowLP p).A e =
      a (p.piCol (p.headAt e.1)) - a (p.piCol (p.tailAt e.1)) := by
  classical
  let h : Fin p.nNodes := ⟨p.headAt e.1, hwell.head_lt e.1 e.2⟩
  let t : Fin p.nNodes := ⟨p.tailAt e.1, hwell.tail_lt e.1 e.2⟩
  change (∑ i : Fin p.nNodes,
      a (p.piCol i.1) * incidenceCoeff p i.1 e.1) =
    a (p.piCol h.1) - a (p.piCol t.1)
  simp only [incidenceCoeff, mul_sub]
  rw [Finset.sum_sub_distrib]
  have hh : ∀ i : Fin p.nNodes, p.headAt e.1 = i.1 ↔ h = i := by
    intro i; simp [h, Fin.ext_iff]
  have ht : ∀ i : Fin p.nNodes, p.tailAt e.1 = i.1 ↔ t = i := by
    intro i; simp [t, Fin.ext_iff]
  simp [hh, ht]

/-- `gapOf` is exactly the `FlowLP` dual objective minus primal objective. -/
theorem gapOf_eq_flowLP_gap (p : CertFProg) (a : Assignment) :
    gapOf p a =
      (integerFlowLP p).c ⬝ᵥ (integerSlack p a) -
        (integerFlowLP p).w ⬝ᵥ (integerFlow p a) := by
  rw [gapOf, list_range_map_sum_eq_finset_sum]
  rw [← Fin.sum_univ_eq_sum_range
    (fun e => p.cAt e * a (p.sCol e) - p.wAt e * a (p.fCol e)) p.m]
  simp only [integerFlowLP, integerSlack, integerFlow, dotProduct, Finset.sum_sub_distrib]

/-- The exact list-indexed predicate is a `Market.Certified` certificate for the denoted integer
circulation LP.  This theorem contains no field arithmetic; it identifies the two formulations. -/
theorem integerCertF_is_Certified (p : CertFProg) (a : Assignment)
    (hwell : p.IntegerWellFormed) (hcert : IntegerCertF p a) :
    Market.Certified (integerFlowLP p) (integerFlow p a)
      (integerPotential p a) (integerSlack p a) := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · funext i
    rw [← consBody_eval_eq_mulVec]
    exact hcert.conservation i.1 i.2
  · intro e
    exact hcert.flow_nonneg e.1 e.2
  · intro e
    exact hcert.flow_le_capacity e.1 e.2
  · intro e
    exact hcert.slack_nonneg e.1 e.2
  · intro e
    change p.wAt e.1 ≤
      Matrix.vecMul (integerPotential p a) (integerFlowLP p).A e + a (p.sCol e.1)
    rw [potential_vecMul_eq_difference p a hwell e]
    exact hcert.dual_feasible e.1 e.2
  · rw [← gapOf_eq_flowLP_gap]
    exact hcert.gap_le

/-! ### §7.2 — Exact numeric boundaries enforced by the deployed programs.

The v1 descriptor did not range-check node potentials, and market4's 28-bit `f`/`s` cells were too
wide once multiplied by public coefficients.  The boundary lemmas below identify the sufficient
bounds independently of their implementation.  Section 8 then discharges every hypothesis from the
new descriptor constraints themselves, yielding unconditional registry admission.
-/

/-- Ring3's aggregate residuals cannot wrap once all three potentials are also in the existing
28-bit value window. All other bounds are extracted from the satisfying descriptor itself. -/
theorem ring3_noWrap_of_potential_range {hash : List ℤ → ℤ} {a : Assignment}
    (hcanon : ∀ col, CanonCell (a col))
    (hsat : Satisfied2 hash (certFDescriptorOf ring3Prog) m0 f0 [] (constTrace ring3Prog a))
    (hpi : ∀ i < ring3Prog.nNodes, a (ring3Prog.piCol i) < 2 ^ certFValueBits) :
    CertFIntegerNoWrap ring3Prog a := by
  have hf0 := certFDescriptor_box_lower_sound hcanon hsat 0 (by decide)
  have hf1 := certFDescriptor_box_lower_sound hcanon hsat 1 (by decide)
  have hf2 := certFDescriptor_box_lower_sound hcanon hsat 2 (by decide)
  have hu0 := (certFDescriptor_box_upper_sound hcanon hsat 0 (by decide)).1
  have hu1 := (certFDescriptor_box_upper_sound hcanon hsat 1 (by decide)).1
  have hu2 := (certFDescriptor_box_upper_sound hcanon hsat 2 (by decide)).1
  have hs0 := certFDescriptor_slack_sound hcanon hsat 0 (by decide)
  have hs1 := certFDescriptor_slack_sound hcanon hsat 1 (by decide)
  have hs2 := certFDescriptor_slack_sound hcanon hsat 2 (by decide)
  have hd0 := (certFDescriptor_dual_sound hcanon hsat 0 (by decide)).1
  have hd1 := (certFDescriptor_dual_sound hcanon hsat 1 (by decide)).1
  have hd2 := (certFDescriptor_dual_sound hcanon hsat 2 (by decide)).1
  have hg := certFDescriptor_gap_sound hcanon hsat
  have hp0 := hcanon (ring3Prog.piCol 0)
  have hp1 := hcanon (ring3Prog.piCol 1)
  have hp2 := hcanon (ring3Prog.piCol 2)
  have hp0' := hpi 0 (by decide)
  have hp1' := hpi 1 (by decide)
  have hp2' := hpi 2 (by decide)
  have hobj := hcanon ring3Prog.objCol
  norm_num [CanonCell, ring3Prog, CertFProg.fCol, CertFProg.sCol, CertFProg.piCol,
    CertFProg.objCol, CertFProg.uCol, CertFProg.dCol, CertFProg.gCol, CertFProg.m,
    certFValueBits] at hf0 hf1 hf2 hu0 hu1 hu2 hs0 hs1 hs2 hd0 hd1 hd2 hg
  have hp0lo : 0 ≤ a 6 := by simpa [ring3Prog, CertFProg.piCol, CertFProg.m] using hp0.1
  have hp1lo : 0 ≤ a 7 := by simpa [ring3Prog, CertFProg.piCol, CertFProg.m] using hp1.1
  have hp2lo : 0 ≤ a 8 := by simpa [ring3Prog, CertFProg.piCol, CertFProg.m] using hp2.1
  have hp0hi : a 6 < 268435456 := by
    simpa [ring3Prog, CertFProg.piCol, CertFProg.m, certFValueBits] using hp0'
  have hp1hi : a 7 < 268435456 := by
    simpa [ring3Prog, CertFProg.piCol, CertFProg.m, certFValueBits] using hp1'
  have hp2hi : a 8 < 268435456 := by
    simpa [ring3Prog, CertFProg.piCol, CertFProg.m, certFValueBits] using hp2'
  have hobjlo : 0 ≤ a 9 := by simpa [ring3Prog, CertFProg.objCol, CertFProg.m] using hobj.1
  have hobjhi : a 9 < 2013265921 := by
    simpa [ring3Prog, CertFProg.objCol, CertFProg.m, CanonCell] using hobj.2
  have hrange : List.range 3 = [0, 1, 2] := by decide
  constructor
  · intro i hi
    have hi' : i < 3 := by simpa [ring3Prog] using hi
    interval_cases i <;> simp only [InZeroResidueWindow] <;>
      rw [consBody_eval_eq_list_sum] <;>
      simp only [ring3Prog, CertFProg.m, List.length_cons, List.length_nil] <;>
      rw [hrange] <;>
      simp [incidenceCoeff, CertFProg.headAt,
        CertFProg.tailAt, CertFProg.fCol, babyBearModulus] <;> omega
  · intro e he
    have he' : e < 3 := by simpa [ring3Prog, CertFProg.m] using he
    interval_cases e <;>
      simp only [InZeroResidueWindow] <;>
      norm_num [ring3Prog, CertFProg.uCol, CertFProg.objCol, CertFProg.m,
        CertFProg.cAt, CertFProg.fCol, babyBearModulus] <;> omega
  · intro e he
    have he' : e < 3 := by simpa [ring3Prog, CertFProg.m] using he
    interval_cases e <;>
      simp only [InZeroResidueWindow] <;>
      norm_num [ring3Prog, CertFProg.dCol, CertFProg.objCol, CertFProg.m,
        CertFProg.piCol, CertFProg.headAt, CertFProg.tailAt, CertFProg.sCol,
        CertFProg.wAt, babyBearModulus] <;> omega
  · simp [InZeroResidueWindow, babyBearModulus, gapOf, ring3Prog, hrange,
      CertFProg.gCol, CertFProg.objCol, CertFProg.m, CertFProg.cAt,
      CertFProg.sCol, CertFProg.wAt, CertFProg.fCol]
    omega
  · simp [InZeroResidueWindow, babyBearModulus, objOf, ring3Prog, hrange,
      CertFProg.objCol, CertFProg.m, CertFProg.wAt, CertFProg.fCol]
    omega

/-- Market4's coefficient accounting closes with 21-bit flows, 19-bit dual slacks, and 28-bit
potentials. These are the largest simple power-of-two bounds obtained from the two load-bearing
aggregate estimates:

* objective: `(Σw)2²¹ = 600·2²¹ < p`;
* gap upper side: `2²⁸ + (Σc)2¹⁹ = 2²⁸ + 1800·2¹⁹ < p`.

The deployed market4 policy now enforces exactly these three bounds. -/
theorem market4_noWrap_of_tight_ranges {hash : List ℤ → ℤ} {a : Assignment}
    (hcanon : ∀ col, CanonCell (a col))
    (hsat : Satisfied2 hash (certFDescriptorOf market4Prog) m0 f0 [] (constTrace market4Prog a))
    (hflow : ∀ e < market4Prog.m, a (market4Prog.fCol e) < 2 ^ 21)
    (hslack : ∀ e < market4Prog.m, a (market4Prog.sCol e) < 2 ^ 19)
    (hpi : ∀ i < market4Prog.nNodes, a (market4Prog.piCol i) < 2 ^ certFValueBits) :
    CertFIntegerNoWrap market4Prog a := by
  have hf0 := certFDescriptor_box_lower_sound hcanon hsat 0 (by decide)
  have hf1 := certFDescriptor_box_lower_sound hcanon hsat 1 (by decide)
  have hf2 := certFDescriptor_box_lower_sound hcanon hsat 2 (by decide)
  have hf3 := certFDescriptor_box_lower_sound hcanon hsat 3 (by decide)
  have hf0' := hflow 0 (by decide)
  have hf1' := hflow 1 (by decide)
  have hf2' := hflow 2 (by decide)
  have hf3' := hflow 3 (by decide)
  have hu0 := (certFDescriptor_box_upper_sound hcanon hsat 0 (by decide)).1
  have hu1 := (certFDescriptor_box_upper_sound hcanon hsat 1 (by decide)).1
  have hu2 := (certFDescriptor_box_upper_sound hcanon hsat 2 (by decide)).1
  have hu3 := (certFDescriptor_box_upper_sound hcanon hsat 3 (by decide)).1
  have hs0 := certFDescriptor_slack_sound hcanon hsat 0 (by decide)
  have hs1 := certFDescriptor_slack_sound hcanon hsat 1 (by decide)
  have hs2 := certFDescriptor_slack_sound hcanon hsat 2 (by decide)
  have hs3 := certFDescriptor_slack_sound hcanon hsat 3 (by decide)
  have hs0' := hslack 0 (by decide)
  have hs1' := hslack 1 (by decide)
  have hs2' := hslack 2 (by decide)
  have hs3' := hslack 3 (by decide)
  have hd0 := (certFDescriptor_dual_sound hcanon hsat 0 (by decide)).1
  have hd1 := (certFDescriptor_dual_sound hcanon hsat 1 (by decide)).1
  have hd2 := (certFDescriptor_dual_sound hcanon hsat 2 (by decide)).1
  have hd3 := (certFDescriptor_dual_sound hcanon hsat 3 (by decide)).1
  have hg := certFDescriptor_gap_sound hcanon hsat
  have hp0 := hcanon (market4Prog.piCol 0)
  have hp1 := hcanon (market4Prog.piCol 1)
  have hp2 := hcanon (market4Prog.piCol 2)
  have hp0' := hpi 0 (by decide)
  have hp1' := hpi 1 (by decide)
  have hp2' := hpi 2 (by decide)
  have hobj := hcanon market4Prog.objCol
  norm_num [market4Prog, CertFProg.fCol, CertFProg.sCol, CertFProg.objCol,
    CertFProg.uCol, CertFProg.dCol, CertFProg.gCol, CertFProg.m, certFValueBits]
    at hf0 hf1 hf2 hf3 hf0' hf1' hf2' hf3' hu0 hu1 hu2 hu3
      hs0 hs1 hs2 hs3 hs0' hs1' hs2' hs3' hd0 hd1 hd2 hd3 hg
  have hp0lo : 0 ≤ a 8 := by simpa [market4Prog, CertFProg.piCol, CertFProg.m] using hp0.1
  have hp1lo : 0 ≤ a 9 := by simpa [market4Prog, CertFProg.piCol, CertFProg.m] using hp1.1
  have hp2lo : 0 ≤ a 10 := by simpa [market4Prog, CertFProg.piCol, CertFProg.m] using hp2.1
  have hp0hi : a 8 < 268435456 := by
    simpa [market4Prog, CertFProg.piCol, CertFProg.m, certFValueBits] using hp0'
  have hp1hi : a 9 < 268435456 := by
    simpa [market4Prog, CertFProg.piCol, CertFProg.m, certFValueBits] using hp1'
  have hp2hi : a 10 < 268435456 := by
    simpa [market4Prog, CertFProg.piCol, CertFProg.m, certFValueBits] using hp2'
  have hobjlo : 0 ≤ a 11 := by simpa [market4Prog, CertFProg.objCol, CertFProg.m] using hobj.1
  have hobjhi : a 11 < 2013265921 := by
    simpa [market4Prog, CertFProg.objCol, CertFProg.m, CanonCell] using hobj.2
  have hrange : List.range 4 = [0, 1, 2, 3] := by decide
  constructor
  · intro i hi
    have hi' : i < 3 := by simpa [market4Prog] using hi
    interval_cases i <;> simp only [InZeroResidueWindow] <;>
      rw [consBody_eval_eq_list_sum] <;>
      simp only [market4Prog, CertFProg.m, List.length_cons, List.length_nil] <;>
      rw [hrange] <;>
      simp [incidenceCoeff, CertFProg.headAt, CertFProg.tailAt, CertFProg.fCol,
        babyBearModulus] <;> omega
  · intro e he
    have he' : e < 4 := by simpa [market4Prog, CertFProg.m] using he
    interval_cases e <;>
      simp only [InZeroResidueWindow] <;>
      norm_num [market4Prog, CertFProg.uCol, CertFProg.objCol, CertFProg.m,
        CertFProg.cAt, CertFProg.fCol, babyBearModulus] <;> omega
  · intro e he
    have he' : e < 4 := by simpa [market4Prog, CertFProg.m] using he
    interval_cases e <;>
      simp only [InZeroResidueWindow] <;>
      norm_num [market4Prog, CertFProg.dCol, CertFProg.objCol, CertFProg.m,
        CertFProg.piCol, CertFProg.headAt, CertFProg.tailAt, CertFProg.sCol,
        CertFProg.wAt, babyBearModulus] <;> omega
  · simp [InZeroResidueWindow, babyBearModulus, gapOf, market4Prog, hrange,
      CertFProg.gCol, CertFProg.objCol, CertFProg.m, CertFProg.cAt,
      CertFProg.sCol, CertFProg.wAt, CertFProg.fCol]
    omega
  · simp [InZeroResidueWindow, babyBearModulus, objOf, market4Prog, hrange,
      CertFProg.objCol, CertFProg.m, CertFProg.wAt, CertFProg.fCol]
    omega

/-- Ring3 becomes uniformly registry-admissible if the registry can prove (or a re-emitted
descriptor enforces) the missing 28-bit potential guard on every canonical satisfying trace. -/
theorem ring3_IntegerAdmission_of_potential_guard
    (hguard : ∀ (hash : List ℤ → ℤ) (a : Assignment),
      (∀ col, CanonCell (a col)) →
      Satisfied2 hash (certFDescriptorOf ring3Prog) m0 f0 [] (constTrace ring3Prog a) →
      ∀ i < ring3Prog.nNodes, a (ring3Prog.piCol i) < 2 ^ certFValueBits) :
    ring3Prog.IntegerAdmission := by
  refine ⟨ring3Prog_integerWellFormed, ?_⟩
  intro hash a hcanon hsat
  exact ring3_noWrap_of_potential_range hcanon hsat (hguard hash a hcanon hsat)

/-- Market4 becomes uniformly registry-admissible if the registry can prove (or a re-emitted
descriptor enforces) precisely the 21-bit flow, 19-bit slack, and 28-bit potential guards on every
canonical satisfying trace. No honest-witness assumption appears. -/
theorem market4_IntegerAdmission_of_tight_range_guards
    (hguard : ∀ (hash : List ℤ → ℤ) (a : Assignment),
      (∀ col, CanonCell (a col)) →
      Satisfied2 hash (certFDescriptorOf market4Prog) m0 f0 [] (constTrace market4Prog a) →
      (∀ e < market4Prog.m, a (market4Prog.fCol e) < 2 ^ 21) ∧
      (∀ e < market4Prog.m, a (market4Prog.sCol e) < 2 ^ 19) ∧
      (∀ i < market4Prog.nNodes, a (market4Prog.piCol i) < 2 ^ certFValueBits)) :
    market4Prog.IntegerAdmission := by
  refine ⟨market4Prog_integerWellFormed, ?_⟩
  intro hash a hcanon hsat
  obtain ⟨hf, hs, hp⟩ := hguard hash a hcanon hsat
  exact market4_noWrap_of_tight_ranges hcanon hsat hf hs hp

/-! ### §7.3 — Deployed registry admission (no caller-supplied guard hypotheses). -/

/-- Ring3's potential range guard is a real AIR tooth, hence every canonical satisfying trace is
integer-admissible. -/
theorem ring3Prog_integerAdmission : ring3Prog.IntegerAdmission :=
  ring3_IntegerAdmission_of_potential_guard (by
    intro hash a hcanon hsat i hi
    exact (certFDescriptor_potential_sound hcanon hsat i hi).2)

/-- Market4's 21-bit flow, 19-bit slack, and 28-bit potential policies are all enforced by the
Lean-authored descriptor.  This is the uniform security theorem: no honest-witness premise and no
range hypothesis is accepted from a caller. -/
theorem market4Prog_integerAdmission : market4Prog.IntegerAdmission :=
  market4_IntegerAdmission_of_tight_range_guards (by
    intro hash a hcanon hsat
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      simpa [market4Prog, CertFProg.effectiveFlowBits, certFValueBits] using
        (certFDescriptor_flow_tight_sound hcanon hsat e he).2
    · intro e he
      simpa [market4Prog, CertFProg.effectiveSlackBits, certFValueBits] using
        (certFDescriptor_slack_tight_sound hcanon hsat e he).2
    · intro i hi
      exact (certFDescriptor_potential_sound hcanon hsat i hi).2)

/-! ### §7.4 — Why the admission guards are load-bearing.

These are scalar countermodels to the retired v1 policy. They do not rely on an honest witness.
Each exhibits values accepted by the old per-cell ranges and arithmetic congruence but false as the
intended integer statement.  The new appended constraints reject these exact value classes.
-/

/-- **Unranged potential obstruction (already on ring3).** Let the tail potential be `p-1`, head
potential/slack/dual-slack be zero, and weight be one. Both potentials are canonical, `d=s=0` satisfy
the deployed 28-bit ranges, and the dual gate residual is exactly `p`, hence zero in BabyBear. But
the integer inequality `1 ≤ π_head - π_tail + s` is false. -/
theorem ring3_unranged_potential_wraps_dual_gate :
    CanonCell 2013265920 ∧ CanonCell 0 ∧
    ((0 : ℤ) ≤ 0 ∧ (0 : ℤ) < 2 ^ certFValueBits) ∧
    ((0 : ℤ) - (0 - 2013265920 + 0 - 1)) ≡ 0 [ZMOD 2013265921] ∧
    ¬ ((1 : ℤ) ≤ 0 - 2013265920 + 0) := by
  refine ⟨by norm_num [CanonCell], by norm_num [CanonCell], by norm_num [certFValueBits], ?_, by norm_num⟩
  exact Int.modEq_zero_iff_dvd.mpr ⟨1, by norm_num⟩

/-- **Market4 objective obstruction.** Four legal 28-bit flow cells at their maximum give
`wᵀf = (Σw)(2²⁸-1) = 600(2²⁸-1)`. The canonical objective `2013265241` is congruent to
that total but differs by `79p`. Thus canonical `obj` plus individually ranged `f` does not make the
published objective exact. -/
theorem market4_28bit_objective_wraps :
    let F : ℤ := 2 ^ certFValueBits - 1
    (0 ≤ F ∧ F < 2 ^ certFValueBits) ∧
    CanonCell 2013265241 ∧
    (2013265241 : ℤ) ≡ 600 * F [ZMOD 2013265921] ∧
    (2013265241 : ℤ) ≠ 600 * F := by
  dsimp
  refine ⟨by norm_num [certFValueBits], by norm_num [CanonCell], ?_, by norm_num [certFValueBits]⟩
  exact Int.modEq_iff_dvd.mpr ⟨79, by norm_num [certFValueBits]⟩

/-- **Market4 gap obstruction.** With four legal 28-bit slacks at their maximum and zero flow,
the weighted gap is `(Σc)(2²⁸-1) = 1800(2²⁸-1)`. The legal 28-bit gap slack `g=4040`
satisfies `g - ε + gap = 240p`, so the field gap gate passes even though the integer gap is vastly
larger than `ε=2000`. -/
theorem market4_28bit_gap_wraps :
    let S : ℤ := 2 ^ certFValueBits - 1
    (0 ≤ S ∧ S < 2 ^ certFValueBits) ∧
    ((0 : ℤ) ≤ 4040 ∧ (4040 : ℤ) < 2 ^ certFValueBits) ∧
    ((4040 : ℤ) - 2000 + 1800 * S) ≡ 0 [ZMOD 2013265921] ∧
    ¬ (1800 * S ≤ (2000 : ℤ)) := by
  dsimp
  refine ⟨by norm_num [certFValueBits], by norm_num [certFValueBits], ?_, by norm_num [certFValueBits]⟩
  exact Int.modEq_zero_iff_dvd.mpr ⟨240, by norm_num [certFValueBits]⟩

/-- A zero congruence in the unique zero-residue window is an integer zero. -/
theorem eq_zero_of_modEq_zero_of_window {x : ℤ}
    (hmod : x ≡ 0 [ZMOD 2013265921]) (hwindow : InZeroResidueWindow x) : x = 0 := by
  obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp hmod
  rcases hwindow with ⟨hlo, hhi⟩
  simp only [babyBearModulus] at hlo hhi
  omega

/-- **THE INTEGER EMIT-SOUNDNESS BRIDGE.**  A satisfying canonical trace, together with honest
aggregate no-wrap bounds, yields the exact integer Cert-F conditions.  No modular inequality is
silently reinterpreted as an integer inequality: every such step first proves its residual is zero
over `ℤ` using `CertFIntegerNoWrap`. -/
theorem certFDescriptor_emit_integer_sound {hash : List ℤ → ℤ} (p : CertFProg)
    {a : Assignment} (hcanon : ∀ col, CanonCell (a col))
    (hnowrap : CertFIntegerNoWrap p a)
    (hsat : Satisfied2 hash (certFDescriptorOf p) m0 f0 [] (constTrace p a)) :
    IntegerCertF p a := by
  have hfield := certFDescriptor_emit_sound p hcanon hsat
  refine
    { conservation := ?_
      flow_nonneg := hfield.2.1
      flow_le_capacity := ?_
      slack_nonneg := hfield.2.2.2.1
      dual_feasible := ?_
      gap_le := ?_
      objective_exact := ?_ }
  · intro i hi
    exact eq_zero_of_modEq_zero_of_window (hfield.1 i hi) (hnowrap.conservation i hi)
  · intro e he
    have hz := eq_zero_of_modEq_zero_of_window (hfield.2.2.1 e he).2
      (hnowrap.boxUpper e he)
    have hu := (hfield.2.2.1 e he).1
    omega
  · intro e he
    have hz := eq_zero_of_modEq_zero_of_window (hfield.2.2.2.2.1 e he).2
      (hnowrap.dual e he)
    have hd := (hfield.2.2.2.2.1 e he).1
    omega
  · have hz : a p.gCol - p.eps + gapOf p a = 0 :=
      eq_zero_of_modEq_zero_of_window
        (by
          have h := hfield.2.2.2.2.2.1.2
          obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp h
          exact Int.modEq_zero_iff_dvd.mpr ⟨-k, by linear_combination -hk⟩)
        hnowrap.gap
    have hg := hfield.2.2.2.2.2.1.1
    linarith
  · apply sub_eq_zero.mp
    exact eq_zero_of_modEq_zero_of_window
      (by
        have h := hfield.2.2.2.2.2.2
        obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp h
        exact Int.modEq_zero_iff_dvd.mpr ⟨-k, by linear_combination -hk⟩)
      hnowrap.objective

/-- **CONDITIONAL INTEGER BRIDGE TO `Market.Certified`.**  A well-formed public edge program,
canonical satisfying trace, and witness-specific aggregate no-wrap proof yield the actual
ordered-ring certificate consumed by `Market.certifies_epsilon_optimal`.  This is not an
unconditional deployed-descriptor claim; `certFDescriptor_admitted_emit_Certified_sound` below
packages the uniform registry obligation. The conjunction also pins the published objective to the
exact integer `wᵀf`. -/
theorem certFDescriptor_emit_Certified_sound {hash : List ℤ → ℤ} (p : CertFProg)
    {a : Assignment} (hwell : p.IntegerWellFormed)
    (hcanon : ∀ col, CanonCell (a col))
    (hnowrap : CertFIntegerNoWrap p a)
    (hsat : Satisfied2 hash (certFDescriptorOf p) m0 f0 [] (constTrace p a)) :
    Market.Certified (integerFlowLP p) (integerFlow p a)
        (integerPotential p a) (integerSlack p a)
      ∧ a p.objCol = objOf p a := by
  have hint := certFDescriptor_emit_integer_sound p hcanon hnowrap hsat
  exact ⟨integerCertF_is_Certified p a hwell hint, hint.objective_exact⟩

/-- **Uniform registry theorem.**  Once a public program carries an `IntegerAdmission` proof, every
canonical satisfying trace yields `Market.Certified` without a witness-specific side condition at
the call site.  Neither `ring3Prog` nor `market4Prog` is claimed admitted merely because one honest
witness is small; admission requires the uniform `noWrap_of_satisfied` field above. -/
theorem certFDescriptor_admitted_emit_Certified_sound {hash : List ℤ → ℤ} (p : CertFProg)
    (hadmit : p.IntegerAdmission) {a : Assignment}
    (hcanon : ∀ col, CanonCell (a col))
    (hsat : Satisfied2 hash (certFDescriptorOf p) m0 f0 [] (constTrace p a)) :
    Market.Certified (integerFlowLP p) (integerFlow p a)
        (integerPotential p a) (integerSlack p a)
      ∧ a p.objCol = objOf p a :=
  certFDescriptor_emit_Certified_sound p hadmit.wellFormed hcanon
    (hadmit.noWrap_of_satisfied hash a hcanon hsat) hsat

/-- The deployed ring3 wire admits only exact integer certificates. -/
theorem ring3_deployed_emit_Certified_sound {hash : List ℤ → ℤ} {a : Assignment}
    (hcanon : ∀ col, CanonCell (a col))
    (hsat : Satisfied2 hash certFDescriptor m0 f0 [] (constTrace ring3Prog a)) :
    Market.Certified (integerFlowLP ring3Prog) (integerFlow ring3Prog a)
        (integerPotential ring3Prog a) (integerSlack ring3Prog a)
      ∧ a ring3Prog.objCol = objOf ring3Prog a :=
  certFDescriptor_admitted_emit_Certified_sound ring3Prog ring3Prog_integerAdmission hcanon hsat

/-- The deployed market4 wire admits only exact integer certificates.  The range assumptions are
derived from the wire itself through `market4Prog_integerAdmission`; no caller supplies them. -/
theorem market4_deployed_emit_Certified_sound {hash : List ℤ → ℤ} {a : Assignment}
    (hcanon : ∀ col, CanonCell (a col))
    (hsat : Satisfied2 hash certFMarket4Descriptor m0 f0 [] (constTrace market4Prog a)) :
    Market.Certified (integerFlowLP market4Prog) (integerFlow market4Prog a)
        (integerPotential market4Prog a) (integerSlack market4Prog a)
      ∧ a market4Prog.objCol = objOf market4Prog a :=
  certFDescriptor_admitted_emit_Certified_sound market4Prog market4Prog_integerAdmission hcanon hsat

/-- **Negative polarity: modular dual feasibility can wrap.**  A negative integer dual expression
`-1` has the same BabyBear residue as the nonnegative canonical slack `p-1`.  Thus the field facts
`0 ≤ d` and `d ≡ q` do *not* imply the integer inequality `0 ≤ q`; the aggregate no-wrap
hypothesis in `certFDescriptor_emit_integer_sound` is load-bearing. -/
theorem dual_feasibility_wrap_counterexample :
    (0 : ℤ) ≤ 2013265920 ∧
    (2013265920 : ℤ) ≡ -1 [ZMOD 2013265921] ∧
    ¬ (0 : ℤ) ≤ -1 := by
  constructor
  · norm_num
  constructor
  · exact Int.modEq_iff_dvd.mpr ⟨-1, by norm_num⟩
  · norm_num

/-! ### §7.5 — The ε-gap REFUSAL tooth (satisfiable AND refutable, at the descriptor level).

`market4_deployed_emit_Certified_sound` says every canonical satisfying trace carries a true
integer certificate.  The contrapositive must be EXHIBITED, not implied: a witness whose integer
duality gap exceeds the public budget is REFUSED by the deployed wire — for every hash, and for
every choice of the remaining cells consistent with that witness's scalar columns.  The general
refusal below reads ONLY the gap violation and canonicality, so the refusal is *because of* the
ε-gap, not incidental to some other broken cell. -/

/-- **The general ε-gap refusal.**  For any admitted public program, a canonical assignment whose
integer duality gap `cᵀs − wᵀf` strictly exceeds the public budget `ε` has NO satisfying trace:
the soundness chain itself refuses the violated certificate. -/
theorem certFDescriptor_gap_violation_refused {hash : List ℤ → ℤ} (p : CertFProg)
    (hadmit : p.IntegerAdmission) {a : Assignment}
    (hcanon : ∀ col, CanonCell (a col))
    (hgap : p.eps < gapOf p a) :
    ¬ Satisfied2 hash (certFDescriptorOf p) m0 f0 [] (constTrace p a) := by
  intro hsat
  obtain ⟨⟨_, _, hgap_le⟩, -⟩ :=
    certFDescriptor_admitted_emit_Certified_sound p hadmit hcanon hsat
  rw [← gapOf_eq_flowLP_gap] at hgap_le
  have hle : gapOf p a ≤ p.eps := hgap_le
  exact absurd hle (not_le.mpr hgap)

/-- Every scalar the honest market4 witness carries is a canonical BabyBear representative.
(The binder is ascribed `ℕ` rather than left to infer `Var` so the `ω`-facts elaborate at the
type `omega` recognizes; `Var` is a reducible abbrev of `ℕ`, so use sites unify definitionally.) -/
theorem market4Honest_canon : ∀ col : ℕ, CanonCell (market4HonestAssignment col) := by
  intro col
  simp only [CanonCell]
  by_cases h : col < 21
  · interval_cases col <;> decide
  · have h1 : ¬ col < 4 := by omega
    have h2 : ¬ col < 8 := by omega
    have h3 : ¬ col < 11 := by omega
    have h4 : col ≠ 11 := by omega
    have h5 : ¬ col < 16 := by omega
    have h6 : ¬ col < 20 := by omega
    have h7 : col ≠ 20 := by omega
    simp [market4HonestAssignment, h1, h2, h3, h4, h5, h6, h7]

/-- The HOSTILE market4 witness: the honest optimum with the single dual slack `s₁` bumped
`0 → 500` (column `5 = market4Prog.sCol 1`).  This adds `c₁·500 = 250000` to the duality gap —
far past `ε = 2000` — while every cell stays canonical. -/
def market4GapViolatingAssignment : Assignment := fun col =>
  if col = 5 then 500 else market4HonestAssignment col

theorem market4GapViolating_canon : ∀ col : ℕ, CanonCell (market4GapViolatingAssignment col) := by
  intro col
  by_cases h : col = 5
  · subst h
    simp only [CanonCell]
    decide
  · simpa [market4GapViolatingAssignment, h] using market4Honest_canon col

/-- **THE ε-GAP REFUSAL, INSTANTIATED ON THE DEPLOYED WIRE.**  The mutation is asserted PRESENT
before the verdict (the hostile witness differs from the honest baseline exactly at `s₁`), the
achieved integer gap is computed (`250000 > ε = 2000`), and the deployed market4 descriptor
REFUSES it: no hash admits a canonical satisfying trace over this witness.  Together with
`market4_deployed_emit_Certified_sound` (the accepting side), the ε-optimality clause is both
satisfiable and refutable at the descriptor level. -/
theorem market4_gap_violation_witness_refused (hash : List ℤ → ℤ) :
    market4Prog.sCol 1 = 5
    ∧ market4GapViolatingAssignment 5 = 500
    ∧ market4HonestAssignment 5 = 0
    ∧ gapOf market4Prog market4GapViolatingAssignment = 250000
    ∧ market4Prog.eps < gapOf market4Prog market4GapViolatingAssignment
    ∧ ¬ Satisfied2 hash certFMarket4Descriptor m0 f0 []
        (constTrace market4Prog market4GapViolatingAssignment) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
  exact certFDescriptor_gap_violation_refused market4Prog market4Prog_integerAdmission
    market4GapViolating_canon (by decide)

/-! ### Axiom hygiene — the emit-soundness keystones pinned kernel-clean. -/

#assert_all_clean [Market.CertFDescriptor.rangeGadget_forces_range,
  Market.CertFDescriptor.tightRecompose_forces_range,
  Market.CertFDescriptor.certFDescriptor_conservation_sound,
  Market.CertFDescriptor.certFDescriptor_box_lower_sound,
  Market.CertFDescriptor.certFDescriptor_box_upper_sound,
  Market.CertFDescriptor.certFDescriptor_slack_sound,
  Market.CertFDescriptor.certFDescriptor_flow_tight_sound,
  Market.CertFDescriptor.certFDescriptor_slack_tight_sound,
  Market.CertFDescriptor.certFDescriptor_potential_sound,
  Market.CertFDescriptor.certFDescriptor_dual_sound,
  Market.CertFDescriptor.certFDescriptor_gap_sound,
  Market.CertFDescriptor.certFDescriptor_gap_gate_sound,
  Market.CertFDescriptor.certFDescriptor_obj_gate_sound,
  Market.CertFDescriptor.certFDescriptor_emit_sound,
  Market.CertFDescriptor.eq_zero_of_modEq_zero_of_window,
  Market.CertFDescriptor.certFDescriptor_emit_integer_sound,
  Market.CertFDescriptor.integerCertF_is_Certified,
  Market.CertFDescriptor.certFDescriptor_emit_Certified_sound,
  Market.CertFDescriptor.certFDescriptor_admitted_emit_Certified_sound,
  Market.CertFDescriptor.ring3Prog_integerWellFormed,
  Market.CertFDescriptor.market4Prog_integerWellFormed,
  Market.CertFDescriptor.market4Honest_noWrap,
  Market.CertFDescriptor.ring3_noWrap_of_potential_range,
  Market.CertFDescriptor.market4_noWrap_of_tight_ranges,
  Market.CertFDescriptor.ring3_IntegerAdmission_of_potential_guard,
  Market.CertFDescriptor.market4_IntegerAdmission_of_tight_range_guards,
  Market.CertFDescriptor.ring3Prog_integerAdmission,
  Market.CertFDescriptor.market4Prog_integerAdmission,
  Market.CertFDescriptor.ring3_deployed_emit_Certified_sound,
  Market.CertFDescriptor.market4_deployed_emit_Certified_sound,
  Market.CertFDescriptor.ring3_unranged_potential_wraps_dual_gate,
  Market.CertFDescriptor.market4_28bit_objective_wraps,
  Market.CertFDescriptor.market4_28bit_gap_wraps,
  Market.CertFDescriptor.dual_feasibility_wrap_counterexample,
  Market.CertFDescriptor.certFDescriptor_gap_violation_refused,
  Market.CertFDescriptor.market4_gap_violation_witness_refused]

end Market.CertFDescriptor

-- Stronger than pinning only the eight public keystones above: audit every theorem in the emitted
-- descriptor namespace, including all range/membership plumbing used to derive them.
#assert_namespace_axioms Market.CertFDescriptor
