/-
  The certified Pancake chain: Lean-authored compiler stages with their emit-correctness
  proofs. Roots are the same set the source tree declares, so this cut builds the same
  library — no more, no less. Lean 4 core only (BitVec, omega, simp): no Mathlib, no
  external package, hence no `require`. Pinned via the sibling lean-toolchain.

  `PanSem.*` is CakeML's panSem (`evaluate` and what it calls), exported mechanically
  from HOL4 by DreggNet's p3-bridge exporter (generated files carry a DO-NOT-EDIT
  header; Prelude/Tactics/Support are the hand-written trusted and proof-support half).
  `Pancake.LadderPanSem` states the ladder's rungs against that export.
-/
import Lake
open Lake DSL

package «orb-compiler» where
  -- keep the build deterministic; no default extra options
  leanOptions := #[]

@[default_target]
lean_lib Pancake where
  srcDir := "."
  roots := #[`Dsl.EmitPancake, `Pancake.Sem, `Pancake.Lower, `Pancake.EmitCorrectRegion, `Pancake.EmitCorrectCompose, `Pancake.EmitCorrectLoop, `Pancake.EmitCorrectClock, `Pancake.BytesModel, `Pancake.StructModel, `Pancake.SerializeCompile, `Pancake.RealStageDemo, `Pancake.NatToDecCompile, `Pancake.NatToDecFull, `Pancake.StageProg, `Pancake.StageCompile, `Pancake.StageMore, `Pancake.SerializeFull, `Pancake.SerializeHeaders, `Pancake.SerializeStruct, `Pancake.StageEvenMore, `Pancake.StructEmit, `Pancake.StageLiftHeader, `Pancake.StatusLineEmit, `Pancake.ModelUnify, `Pancake.ByteCopy, `Pancake.FullResponseCompile, `Pancake.ProofProducing, `Pancake.ServeFragment, `Pancake.ServeSlice, `Pancake.ServeEmit, `Pancake.LowerBridge, `Pancake.LowerBridgeSem, `Pancake.ServeExportServes, `Pancake.ServeConfigServe, `Pancake.ServeCompose, `Pancake.StageProg2, `Pancake.StageLiftGate, `Pancake.StageYetMore, `Pancake.ServeFull, `Pancake.DslServe, `Pancake.StageLift2, `Pancake.StageLift2Inst, `Pancake.StageLift2Cond, `Pancake.PredEval, `Pancake.CondRespProto, `Pancake.PanSemAgree, `Pancake.LadderPanSem]

/-- CakeML's panSem exported from HOL4 (see the header comment above). Every module,
including the generated vectors `PanSem.GenVectors` (checker 3), is a target. -/
@[default_target]
lean_lib PanSem where
  srcDir := "."
  globs := #[.submodules `PanSem]
