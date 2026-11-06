/-
Lean source for the depth-uniform binary membership block formerly authored in
`circuit/src/membership_descriptor_general.rs`. The depth parameter changes only
the descriptor name: it does NOT constrain trace height. The refinement proves
membership along the actual trace's path. The output digest remains one felt;
seven auxiliary permutation lanes do not widen its public commitment.
-/
import Dregg2.Circuit.DescriptorIR2
namespace Dregg2.Circuit.Emit.BinaryMembershipEmit
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmRow)
set_option autoImplicit false

def CUR : Nat := 0
def SIB : Nat := 1
def DIR : Nat := 2
def LEFT : Nat := 3
def RIGHT : Nat := 4
def PAR : Nat := 5
def LANE_BASE : Nat := 6
def WIDTH : Nat := 13
def PI_LEAF : Nat := 0
def PI_ROOT : Nat := 1

def neg (e : EmittedExpr) : EmittedExpr := .mul (.const (-1)) e

def dirBody : EmittedExpr := .mul (.var DIR) (.add (.var DIR) (.const (-1)))

def leftBody : EmittedExpr :=
  .add (.var LEFT) (.add (neg (.var CUR))
    (.add (neg (.mul (.var DIR) (.var SIB))) (.mul (.var DIR) (.var CUR))))

def rightBody : EmittedExpr :=
  .add (.var RIGHT) (.add (neg (.var SIB))
    (.add (neg (.mul (.var DIR) (.var CUR))) (.mul (.var DIR) (.var SIB))))

def parentLookup : VmConstraint2 :=
  .lookup ⟨.poseidon2, chipLookupTuple [.var LEFT, .var RIGHT] PAR [6,7,8,9,10,11,12]⟩

def continuity : WindowConstraint :=
  ⟨.add (.nxt CUR) (.mul (.const (-1)) (.loc PAR)), true⟩

def constraints : List VmConstraint2 :=
  [ .base (.gate dirBody), .base (.gate leftBody), .base (.gate rightBody), parentLookup,
    .windowGate continuity,
    .base (.piBinding .first CUR PI_LEAF), .base (.piBinding .last PAR PI_ROOT),
    .base (.boundary .last dirBody), .base (.boundary .last leftBody),
    .base (.boundary .last rightBody) ]

def membershipDesc (depth : Nat) : EffectVmDescriptor2 :=
  { name := "merkle-membership::poseidon2-binary-general-depth" ++ toString depth
    traceWidth := WIDTH
    piCount := 2
    tables := []
    constraints := constraints
    hashSites := []
    ranges := [] }

/-- The artifact is a template: Rust changes only its historical depth name. -/
def templateDesc : EffectVmDescriptor2 := membershipDesc 2

theorem shape (depth : Nat) :
    (membershipDesc depth).traceWidth = 13 ∧ (membershipDesc depth).piCount = 2 ∧
    (membershipDesc depth).constraints.length = 10 := ⟨rfl, rfl, rfl⟩

/-- Depth labeling does not insert an invisible constraint on physical trace height. -/
theorem constraints_depth_uniform (d e : Nat) :
    (membershipDesc d).constraints = (membershipDesc e).constraints := rfl

/-- info: 'Dregg2.Circuit.Emit.BinaryMembershipEmit.shape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms shape
/-- info: 'Dregg2.Circuit.Emit.BinaryMembershipEmit.constraints_depth_uniform' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms constraints_depth_uniform
end Dregg2.Circuit.Emit.BinaryMembershipEmit
