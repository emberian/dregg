/- Execute the actual consumer wrappers. The returned values carry Certified.hdec;
this is execution evidence, not a theorem discharged by a native evaluator. -/
import Dregg2.Policy.Compositional
open Dregg2.Policy

def main : IO Unit := do
  let r := Re.alt (.lit [7]) (.lit [9])
  let tests := [[], [7], [9], [8], [7, 9]]
  let whole ← match certifySurface r with
    | .error e => throw (IO.userError e)
    | .ok (c, _) => pure (tests.map fun w => c.t.acc (c.t.run c.t.start w))
  let absent ← match certifySurfaceAbsence r with
    | .error e => throw (IO.userError e)
    | .ok (c, _) => pure (tests.map fun w => c.t.acc (c.t.run c.t.start w))
  unless whole == [false, true, true, false, false] do
    throw (IO.userError s!"whole-word wrapper regression: {whole}")
  unless absent == [true, false, false, true, false] do
    throw (IO.userError s!"absence wrapper regression: {absent}")
  IO.println "{\"pattern\":\"byte7|byte9\",\"words\":[[],[7],[9],[8],[7,9]],\"whole\":[false,true,true,false,false],\"absence\":[true,false,false,true,false],\"status\":\"pass\"}"
