/- Ordered, public-length-bound table routing. The legacy exact-public shape binds only
an edge multiset. This additive served shape retains its certified table/DFA lowering and
adds the common eight-lane route commitment, including an explicit position per absorb. -/
import Dregg2.Circuit.Emit.RouteChain8
namespace Dregg2.Circuit.Emit.DfaRoutingTableRoute8
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.DfaRoutingTableEmit
open Dregg2.Circuit.Emit.RouteChain8
set_option autoImplicit false
/-- Distinct from the attested-weld domain, canonical in BabyBear. -/
def ROUTE_DOMAIN : Nat := 1414677048
def config : Config :=
  { baseWidth := TRT_WIDTH, basePiCount := TRT_PI_COUNT,
    current := CURRENT, symbol := SYMBOL, next := NEXT, domain := ROUTE_DOMAIN, seed := none }
/-- The descriptor bytes commit the declared transition table; the public route commits its order. -/
def tableRoutingBoundDesc (name : String) (tbl : List (List Nat)) : EffectVmDescriptor2 :=
  decorate name (tableRoutingDesc name tbl) config
def demoBoundDesc : EffectVmDescriptor2 :=
  tableRoutingBoundDesc "dregg-dfa-routing-table::route8-bound-v1" [[0,1,0],[0,2,0]]

theorem bound_shape (name : String) (tbl : List (List Nat)) :
    (tableRoutingBoundDesc name tbl).traceWidth = 20 ∧
    (tableRoutingBoundDesc name tbl).piCount = 11 ∧
    (tableRoutingBoundDesc name tbl).constraints.length = 32 := by
  exact shape name (tableRoutingDesc name tbl) config

/-- The existing generic classification theorem applies after forgetting the route columns. -/
theorem forget_bound {hash : List ℤ → ℤ} {name : String} {tbl : List (List Nat)}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2Public hash (tableRoutingBoundDesc name tbl) minit mfin maddrs t) :
    Satisfied2Public hash (tableRoutingDesc name tbl) minit mfin maddrs t := by
  apply forgetPublic (d := tableRoutingDesc name tbl) (c := config) (name := name) ?_ h
  intro td htd
  have ht : td = transitionTableDef tbl := by simpa [tableRoutingDesc_tables] using htd
  subst td
  simp [transitionTableDef, TRT_TID]

/-- info: 'Dregg2.Circuit.Emit.DfaRoutingTableRoute8.forget_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms forget_bound
end Dregg2.Circuit.Emit.DfaRoutingTableRoute8
