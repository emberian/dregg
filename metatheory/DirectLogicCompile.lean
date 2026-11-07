/-
# DirectLogicCompile -- `lake exe direct_logic_compile`: the direct-logic front end, extracted

Reads request lines on stdin and writes one reply per request, each terminated by a line `end`:

    DIRECT-LOGIC-COMPILE-1 <src nodes> <atoms> <pred entries> <quant instances> <expanded> <hex>

The hex field is the canonical source encoding (Rust `canonical_source_bytes`).  The reply is
`Dregg2.Logic.DirectLogicProgramIR2.respond` of the line, verbatim: the descriptor it carries is
`emitVmJson2` of `compileProgram`, the function the module's soundness and completeness theorems
are about.  Argument handling and line I/O are the untheorem'd shell.
-/

import Dregg2.Logic.DirectLogicProgramIR2

open Dregg2.Logic.DirectLogicProgramIR2

partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let line <- stdin.getLine
  if line.isEmpty then return
  let request := line.trimAsciiEnd.toString
  if request.isEmpty then loop stdin stdout else
  stdout.putStr (respond request ++ "end\n")
  stdout.flush
  loop stdin stdout

def main : IO UInt32 := do
  loop (<- IO.getStdin) (<- IO.getStdout)
  return 0
