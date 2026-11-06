/-
# Attested automaton with a full-width, root-seeded ordered route (initiative #1)

`weldBoundInstance` applies the shared Lean `RouteChain8` generator to the legacy full-root weld.
It adds one admitted arity-16 chip lookup per binary symbol, 17 columns, 9 public inputs and
28 constraints. All eight public automaton-root lanes seed the chain; all eight final route lanes
and the record's symbol count are public. The legacy descriptor remains the weak control.

`weldBound_classifies_or_collides` connects the public record commitment to the exact trace word
and the classification under the committed automaton. Its residuals retain the supplied bad-row
heap or name a pair on the actual/reference route computations. Both route collision inputs are
canonical 16-felt blocks, the digest has eight canonical lanes, and no global injectivity premise
occurs. `AttestedAutomatonRoute8Witness` supplies all premises jointly and refutes both residuals
on honest replay; its substitution pair isolates the missing record-opening check.

Scope: map openings still use the dense eight-lane model, not the deployed padded indexed-Merkle
root model. The route theorem assumes canonical cells and sound chip tables. The explicit trace
height bound (< BabyBear's modulus) rules out counter wrap; the Rust `verify_route8` wrapper
checks it against proof height and public length. This first served route shape has no active-row
padding gates: its Rust witness helper accepts only nonempty power-of-two symbol counts.
-/
import Dregg2.Circuit.Emit.AttestedAutomatonBound
import Dregg2.Circuit.Emit.RouteChain8
import Dregg2.Circuit.Emit.RouteChain8Canonical

namespace Dregg2.Circuit.Emit.AttestedAutomatonRoute8
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.AttestedAutomatonWeld8
open Dregg2.Circuit.Emit.AttestedAutomatonLanes8
open Dregg2.Circuit.Emit.AttestedAutomatonBound
open Dregg2.Circuit.Emit.DfaRoutingTableEmit (CURRENT SYMBOL NEXT)
open Dregg2.Circuit.DeployedHeapTree (Heap8Scheme)
set_option autoImplicit false

def weldRouteConfig : RouteChain8.Config :=
  { baseWidth := WELD_WIDTH, basePiCount := WELD_PI_COUNT,
    current := CURRENT, symbol := SYMBOL, next := NEXT,
    domain := 1464159288, seed := some 2 }

def WELD_BOUND_NAME : String := "dregg-attested-automaton::map-committed-weld8-bound-v1"
def weldBoundDesc (name : String) : EffectVmDescriptor2 :=
  RouteChain8.decorate name (weldDesc name) weldRouteConfig

def weldBoundInstance : EffectVmDescriptor2 := weldBoundDesc WELD_BOUND_NAME

/-- Exact descriptor counts; the map path cost is unchanged, the route adds one chip per symbol. -/
theorem weldBound_shape :
    weldBoundInstance.traceWidth = 28 ∧ weldBoundInstance.piCount = 19 ∧
    weldBoundInstance.constraints.length = 50 ∧ weldBoundInstance.tables.length = 4 := by decide

/-- The full eight-lane map denotation survives the route decorator. -/
theorem forgetLanes8 {S8 : Heap8Scheme} {hash : List ℤ → ℤ} {name : String}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2Lanes8 S8 hash (weldBoundDesc name) minit mfin maddrs t) :
    Satisfied2Lanes8 S8 hash (weldDesc name) minit mfin maddrs t := by
  have hm : memLog (weldBoundDesc name) t = memLog (weldDesc name) t := by
    simp [weldBoundDesc, memLog, RouteChain8.memOps_decorate]
  have hp : mapLog8 (weldBoundDesc name) t = mapLog8 (weldDesc name) t := by
    simp [weldBoundDesc, mapLog8, RouteChain8.mapOps_decorate]
  refine {
    rowConstraints := fun i hi x hx => h.rowConstraints i hi x (List.mem_append_left _ hx)
    rowHashes := h.rowHashes
    rowRanges := h.rowRanges
    memAddrsNodup := h.memAddrsNodup
    memClosed := by simpa [hm] using h.memClosed
    memDisciplined := by simpa [hm] using h.memDisciplined
    memBalanced := by simpa [hm] using h.memBalanced
    memTableFaithful := by simpa [hm] using h.memTableFaithful
    mapTableFaithful8 := by simpa [hp] using h.mapTableFaithful8
    publicTablesFaithful := fun td htd => h.publicTablesFaithful td (RouteChain8.base_tables _ _ _ _ htd)
    publicLookupBalanced := ?_ }
  intro td htd
  have hb := h.publicLookupBalanced td (RouteChain8.base_tables _ _ _ _ htd)
  have hn : td.id ≠ .poseidon2 := by
    simp only [weldDesc, List.mem_cons, List.not_mem_nil, or_false] at htd
    rcases htd with rfl | rfl | rfl; all_goals decide
  cases hs : td.sem <;> simp only [hs] at hb ⊢ <;> try trivial
  simpa only [weldBoundDesc, RouteChain8.lookupLog_decorate name (weldDesc name) weldRouteConfig t td.id hn]
    using hb

/-- The ordered payloads computed by a record holder from the automaton and initial state. -/
def recordPayloads (d : Dregg2.Crypto.DfaAcceptanceAir.TableDfa Nat Nat) :
    Nat → Nat → List Nat → List (List ℤ)
  | _, _, [] => []
  | q, i, y :: ys =>
      [1464159288, i+1, q, y, d.step q y] :: recordPayloads d (d.step q y) (i+1) ys

theorem recordPayloads_length (d : Dregg2.Crypto.DfaAcceptanceAir.TableDfa Nat Nat)
    (q i : Nat) (w : List Nat) : (recordPayloads d q i w).length = w.length := by
  induction w generalizing q i with
  | nil => rfl
  | cons y ys ih => simp only [recordPayloads, List.length_cons, ih]

theorem recordPayloads_width (d : Dregg2.Crypto.DfaAcceptanceAir.TableDfa Nat Nat)
    (q i : Nat) (w : List Nat) : ∀ p ∈ recordPayloads d q i w, p.length = 5 := by
  induction w generalizing q i with
  | nil => simp [recordPayloads]
  | cons y ys ih =>
    intro p hp
    change p ∈ ([1464159288, (i+1 : Nat), q, y, d.step q y] : List ℤ) ::
      recordPayloads d (d.step q y) (i+1) ys at hp
    rcases List.mem_cons.mp hp with rfl | hp
    · rfl
    · exact ih _ _ p hp

theorem recordPayloads_word (d : Dregg2.Crypto.DfaAcceptanceAir.TableDfa Nat Nat)
    (q i : Nat) (w : List Nat) :
    (recordPayloads d q i w).map (fun p => (p.getD 3 0).toNat) = w := by
  induction w generalizing q i with
  | nil => rfl
  | cons y ys ih =>
    change y :: (recordPayloads d (d.step q y) (i+1) ys).map
      (fun p => (p.getD 3 0).toNat) = y :: ys
    rw [ih]

/-- Isolate exactly the generated constraints; map openings retain their eight-lane meaning. -/
theorem routeRowsHold {S8 : Heap8Scheme} {hash : List ℤ → ℤ} {name : String}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2Lanes8 S8 hash (weldBoundDesc name) minit mfin maddrs t) :
    RouteChain8Refine.RowsHold weldRouteConfig hash t := by
  intro i hi x hx
  have hh := h.rowConstraints i hi x (List.mem_append_right _ hx)
  have hn : ∀ m, x ≠ .mapOp m := by
    intro m he
    subst x
    simp [RouteChain8.constraints, RouteChain8.lanes, RouteChain8.chip, RouteChain8.copy,
      RouteChain8.seedPin, RouteChain8.outputPin, RouteChain8.indexFirst, RouteChain8.indexStep,
      RouteChain8.indexLast, weldRouteConfig] at hx
  cases x <;> try exact hh
  exact False.elim (hn _ rfl)

/-- Full-width record commitment, seeded by all eight public automaton-root lanes. -/
def recordCommit (H : List ℤ → List ℤ) (t : VmTrace)
    (d : Dregg2.Crypto.DfaAcceptanceAir.TableDfa Nat Nat) (q : Nat) (w : List Nat) : List ℤ :=
  RouteChain8Binding.fold H (RouteChain8Refine.seed weldRouteConfig t) (recordPayloads d q 0 w)

def recordFind (H : List ℤ → List ℤ) (t : VmTrace)
    (d : Dregg2.Crypto.DfaAcceptanceAir.TableDfa Nat Nat) (q : Nat) (w : List Nat) :
    List ℤ × List ℤ :=
  RouteChain8Binding.find H (RouteChain8Refine.seed weldRouteConfig t)
    (RouteChain8Refine.seed weldRouteConfig t) (RouteChain8Refine.payloads weldRouteConfig t)
    (recordPayloads d q 0 w)

def CanonicalValues (xs : List ℤ) : Prop := ∀ x ∈ xs, 0 ≤ x ∧ x < 2013265921

/-- Ordinary state/symbol/index bounds discharge the reference encoding's canonicality premise. -/
theorem recordPayloads_canonical (d : Dregg2.Crypto.DfaAcceptanceAir.TableDfa Nat Nat)
    (hstep : ∀ s y, d.step s y < 2013265921) (q i : Nat) (w : List Nat)
    (hq : q < 2013265921) (hindex : i + w.length < 2013265921)
    (hsym : ∀ y ∈ w, y < 2013265921) :
    ∀ p ∈ recordPayloads d q i w, CanonicalValues p := by
  have natCan : ∀ n : Nat, n < 2013265921 → 0 ≤ (n : ℤ) ∧ (n : ℤ) < 2013265921 := by
    intro n hn
    exact ⟨Int.natCast_nonneg n, by exact_mod_cast hn⟩
  induction w generalizing q i with
  | nil => simp [recordPayloads]
  | cons y ys ih =>
    intro p hp
    change p ∈ ([1464159288, (i+1 : Nat), q, y, d.step q y] : List ℤ) ::
      recordPayloads d (d.step q y) (i+1) ys at hp
    rcases List.mem_cons.mp hp with rfl | hp
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · decide
      · apply natCan; simp only [List.length_cons] at hindex; omega
      · exact natCan q hq
      · exact natCan y (hsym y List.mem_cons_self)
      · exact natCan _ (hstep q y)
    · exact ih _ _ (hstep q y) (by simpa [List.length_cons, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hindex)
        (fun y hy => hsym y (List.mem_cons_of_mem _ hy)) p hp

/-- Canonical public/trace cells supply canonical seeded payloads, including the fixed domain. -/
theorem route_values_canonical {t : VmTrace} (hc : RouteChain8Refine.Canonical t) :
    CanonicalValues (RouteChain8Refine.seed weldRouteConfig t) ∧
    ∀ p ∈ RouteChain8Refine.payloads weldRouteConfig t, CanonicalValues p := by
  exact ⟨RouteChain8Canonical.seed_canonical _ _ hc,
    RouteChain8Canonical.trace_payloads_canonical _ _ hc (by decide)⟩

/-- A full-width collision at arity sixteen, with each input on its corresponding actual route. -/
def RecordCollision (H : List ℤ → List ℤ) (t : VmTrace)
    (d : Dregg2.Crypto.DfaAcceptanceAir.TableDfa Nat Nat) (q : Nat) (w : List Nat) : Prop :=
  RouteChain8Binding.Collision H (recordFind H t d q w) ∧
  (recordFind H t d q w).1.length = 16 ∧ (recordFind H t d q w).2.length = 16 ∧
  (recordFind H t d q w).1 ∈ RouteChain8Binding.preimages H
    (RouteChain8Refine.seed weldRouteConfig t) (RouteChain8Refine.payloads weldRouteConfig t) ∧
  (recordFind H t d q w).2 ∈ RouteChain8Binding.preimages H
    (RouteChain8Refine.seed weldRouteConfig t) (recordPayloads d q 0 w) ∧
  CanonicalValues (recordFind H t d q w).1 ∧ CanonicalValues (recordFind H t d q w).2

/-- Honest replay refutes the exact residual independently of any hash-security assumption. -/
theorem honest_record_no_collision (H : List ℤ → List ℤ) (t : VmTrace)
    (d : Dregg2.Crypto.DfaAcceptanceAir.TableDfa Nat Nat) (q : Nat) (w : List Nat)
    (hp : RouteChain8Refine.payloads weldRouteConfig t = recordPayloads d q 0 w) :
    ¬ RecordCollision H t d q w := by
  intro hc
  have hh := hc.1
  unfold recordFind at hh
  rw [hp] at hh
  exact RouteChain8Binding.no_self_collision H _ _ hh

/-- The published route and length identify the read record, or exhibit a full-width collision
on the actual trace/reference routes. The length equality follows from AIR, with the explicit
height-admission bound excluding field wraparound. -/
theorem weldBound_reads_or_collides {S8 : Heap8Scheme} {hash : List ℤ → ℤ} {name : String}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2Lanes8 S8 hash (weldBoundDesc name) minit mfin maddrs t)
    (hc : RouteChain8Refine.Canonical t) (hne : t.rows ≠ [])
    (hheight : t.rows.length < 2013265921)
    (H : List ℤ → List ℤ) (hwidth : ∀ input, (H input).length = 8)
    (hHcan : ∀ input, CanonicalValues (H input))
    (hs : ChipTableSoundN H (t.tf .poseidon2))
    (d : Dregg2.Crypto.DfaAcceptanceAir.TableDfa Nat Nat) (q : Nat) (w : List Nat)
    (hrecord : ∀ p ∈ recordPayloads d q 0 w, CanonicalValues p)
    (hroute : RouteChain8Refine.publicRoute weldRouteConfig t = recordCommit H t d q w)
    (hlen : t.pub (RouteChain8.lengthPi weldRouteConfig) = (w.length : ℤ)) :
    readWord t = w ∨ RecordCollision H t d q w := by
  have hr := routeRowsHold h
  have he := RouteChain8Refine.route_eq_fold H hs hr hc hne
  have hl := RouteChain8Refine.length_exact hr hc hne hheight
  have hlN : t.rows.length = w.length := Int.ofNat.inj (hl.symm.trans hlen)
  rcases RouteChain8Binding.chain_binds_or_collides H 5
      (RouteChain8Refine.seed weldRouteConfig t) (RouteChain8Refine.payloads weldRouteConfig t)
      (recordPayloads d q 0 w) (RouteChain8Refine.payload_width _ _)
      (recordPayloads_width d q 0 w)
      (by simpa only [RouteChain8Refine.payloads, List.length_map, recordPayloads_length] using hlN)
      (he.symm.trans hroute) with hp | hcoll
  · left
    have hh := congrArg (List.map (fun p : List ℤ => (p.getD 3 0).toNat)) hp
    rw [recordPayloads_word] at hh
    simp only [RouteChain8Refine.payloads, List.map_map] at hh
    exact hh
  · right
    have hseed : (RouteChain8Refine.seed weldRouteConfig t).length = 8 := by
      simp [RouteChain8Refine.seed, RouteChain8.lanes]
    have hcan := route_values_canonical hc
    have ha := RouteChain8Canonical.collision_inputs_admitted H hwidth hHcan _ _ _ _
      hseed hseed hcan.1 hcan.1 (RouteChain8Refine.payload_width _ _)
      (recordPayloads_width d q 0 w) hcan.2 hrecord hcoll
    exact ⟨hcoll, ha.1, ha.2.1, ha.2.2.2.2.1, ha.2.2.2.2.2, ha.2.2.1, ha.2.2.2.1⟩

/-- End-to-end content-bound statement for the public committed automaton: either the record
is exactly the trace's word and classifies to the public final state, or a supplied row heap
collides at a bad edge, or the named actual/reference full-width route pair collides. -/
theorem weldBound_classifies_or_collides
    {S8 : Heap8Scheme} {hash : List ℤ → ℤ} {name : String}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2Lanes8 S8 hash (weldBoundDesc name) minit mfin maddrs t)
    (openings : RowHeaps S8 t) (htf : WeldRangeTablesFaithful t.tf)
    (hc : RouteChain8Refine.Canonical t) (hne : t.rows ≠ [])
    (hheight : t.rows.length < 2013265921)
    (H : List ℤ → List ℤ) (hwidth : ∀ input, (H input).length = 8)
    (hHcan : ∀ input, CanonicalValues (H input))
    (hs : ChipTableSoundN H (t.tf .poseidon2))
    (d : Dregg2.Crypto.DfaAcceptanceAir.TableDfa Nat Nat)
    (hdstep : ∀ s y, d.step s y < Dregg2.Circuit.Emit.AttestedAutomatonEmit.ASTATES)
    {m : Dregg2.Substrate.Heap.FeltHeap} (hd : CommitsAutomaton8By S8 m (pubRoot t) d)
    (q : Nat) (hq : q < 2013265921)
    (hpi : t.pub Dregg2.Circuit.Emit.DfaRoutingTableEmit.PI_INITIAL = Int.ofNat q)
    (f : Nat) (hf : f < 2013265921)
    (hpf : t.pub Dregg2.Circuit.Emit.DfaRoutingTableEmit.PI_FINAL = Int.ofNat f)
    (w : List Nat)
    (hrecord : ∀ p ∈ recordPayloads d q 0 w, CanonicalValues p)
    (hroute : RouteChain8Refine.publicRoute weldRouteConfig t = recordCommit H t d q w)
    (hlen : t.pub (RouteChain8.lengthPi weldRouteConfig) = (w.length : ℤ)) :
    (readWord t = w ∧
      (f = Dregg2.Crypto.DfaAcceptanceAir.classifyFrom d q w ∨ RowCollision S8 t d openings m)) ∨
      RecordCollision H t d q w := by
  rcases weldBound_reads_or_collides h hc hne hheight H hwidth hHcan hs d q w hrecord hroute hlen with hw | hcoll
  · left
    refine ⟨hw, ?_⟩
    have hr := weld8_run_or_collides (forgetLanes8 h) openings htf hne d hdstep hd q hq hpi f hf hpf
    simpa only [hw] using hr
  · exact Or.inr hcoll

/-- The proof and public endpoints, with the supplied record deliberately not checked. -/
def WeakAccepts (S8 : Heap8Scheme) (hash : List ℤ → ℤ) (name : String)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (q f : Nat) (_record : List Nat) : Prop :=
  Satisfied2Lanes8 S8 hash (weldBoundDesc name) minit mfin maddrs t ∧
  t.pub Dregg2.Circuit.Emit.DfaRoutingTableEmit.PI_INITIAL = Int.ofNat q ∧
  t.pub Dregg2.Circuit.Emit.DfaRoutingTableEmit.PI_FINAL = Int.ofNat f

/-- Record-aware verification of the SAME proof and public statement: additionally check the
reference record's full-width route and length against the published values. -/
def StrongAccepts (S8 : Heap8Scheme) (hash : List ℤ → ℤ) (name : String)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (H : List ℤ → List ℤ) (d : Dregg2.Crypto.DfaAcceptanceAir.TableDfa Nat Nat)
    (q f : Nat) (record : List Nat) : Prop :=
  WeakAccepts S8 hash name minit mfin maddrs t q f record ∧
  RouteChain8Refine.publicRoute weldRouteConfig t = recordCommit H t d q record ∧
  t.pub (RouteChain8.lengthPi weldRouteConfig) = (record.length : ℤ)

/-- Soundness of the actual strong acceptance relation, consuming its record-opening checks. -/
theorem strongAccepts_sound
    {S8 : Heap8Scheme} {hash : List ℤ → ℤ} {name : String}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (H : List ℤ → List ℤ) (d : Dregg2.Crypto.DfaAcceptanceAir.TableDfa Nat Nat)
    (q f : Nat) (w : List Nat)
    (h : StrongAccepts S8 hash name minit mfin maddrs t H d q f w)
    (openings : RowHeaps S8 t) (htf : WeldRangeTablesFaithful t.tf)
    (hc : RouteChain8Refine.Canonical t) (hne : t.rows ≠ [])
    (hheight : t.rows.length < 2013265921)
    (hwidth : ∀ input, (H input).length = 8) (hHcan : ∀ input, CanonicalValues (H input))
    (hs : ChipTableSoundN H (t.tf .poseidon2))
    (hdstep : ∀ s y, d.step s y < Dregg2.Circuit.Emit.AttestedAutomatonEmit.ASTATES)
    {m : Dregg2.Substrate.Heap.FeltHeap} (hd : CommitsAutomaton8By S8 m (pubRoot t) d)
    (hq : q < 2013265921) (hf : f < 2013265921)
    (hrecord : ∀ p ∈ recordPayloads d q 0 w, CanonicalValues p) :
    (readWord t = w ∧
      (f = Dregg2.Crypto.DfaAcceptanceAir.classifyFrom d q w ∨ RowCollision S8 t d openings m)) ∨
      RecordCollision H t d q w :=
  weldBound_classifies_or_collides h.1.1 openings htf hc hne hheight H hwidth hHcan hs d
    hdstep hd q hq h.1.2.1 f hf h.1.2.2 w hrecord h.2.1 h.2.2

/-- info: 'Dregg2.Circuit.Emit.AttestedAutomatonRoute8.strongAccepts_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms strongAccepts_sound

/-- info: 'Dregg2.Circuit.Emit.AttestedAutomatonRoute8.weldBound_reads_or_collides' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms weldBound_reads_or_collides
/-- info: 'Dregg2.Circuit.Emit.AttestedAutomatonRoute8.weldBound_classifies_or_collides' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms weldBound_classifies_or_collides
/-- info: 'Dregg2.Circuit.Emit.AttestedAutomatonRoute8.honest_record_no_collision' depends on axioms: [propext] -/
#guard_msgs in
#print axioms honest_record_no_collision

#assert_all_clean [weldBound_shape, forgetLanes8, recordPayloads_length, recordPayloads_width,
  recordPayloads_word, recordPayloads_canonical, routeRowsHold, route_values_canonical, honest_record_no_collision, weldBound_reads_or_collides, weldBound_classifies_or_collides, strongAccepts_sound]
end Dregg2.Circuit.Emit.AttestedAutomatonRoute8
