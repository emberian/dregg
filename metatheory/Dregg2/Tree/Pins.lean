/-
# Dregg2.Tree.Pins: executable pins for the schema reader and the corpus checker

The repairs of codex round 1 (`docs/automata/tree/CODEX.md`), each as a refusal the earlier
checker did not make.
-/
import Dregg2.Tree.Instance
import Dregg2.Tree.Json

namespace Dregg2.Tree.Pins

open Dregg2.Tree

def sch (s : String) : Option Schema := (Json.parseString s).bind schemaOfJVal
def val (s : String) : JVal := (Json.parseString s).getD .null

def validAt (s v : String) : Option Bool := (sch s).map fun S => valid S (val v) S.root

-- finding 1: `enum` refuses non-strings (it used to accept `null` under `{"enum":["Bash"]}`)
#guard validAt "{\"defs\":[{\"enum\":[\"Bash\"]}],\"root\":0}" "null" == some false
#guard validAt "{\"defs\":[{\"enum\":[\"Bash\"]}],\"root\":0}" "[]" == some false
#guard validAt "{\"defs\":[{\"enum\":[\"Bash\"]}],\"root\":0}" "\"Bash\"" == some true
-- finding 2: explicit empty lists, dangling child references and unknown wrapper keys are refused
#guard (sch "{\"defs\":[{\"type\":[]}],\"root\":0}").isNone
#guard (sch "{\"defs\":[{\"anyOf\":[]}],\"root\":0}").isNone
#guard (sch "{\"defs\":[{\"enum\":[]}],\"root\":0}").isNone
#guard (sch "{\"defs\":[{\"items\":999}],\"root\":0}").isNone
#guard (sch "{\"defs\":[{\"properties\":{\"a\":7}}],\"root\":0}").isNone
#guard (sch "{\"defs\":[{}],\"root\":0,\"uniqueItems\":true}").isNone
#guard (sch "{\"defs\":[{\"uniqueItems\":true}],\"root\":0}").isNone
#guard (sch "{\"defs\":[{\"type\":\"object\",\"required\":[\"name\"]}],\"root\":0}").isSome
-- the schema semantics on a tool-call shape: required, additionalProperties, anyOf by lower index
def toolSchema : String :=
  "{\"defs\":[{\"type\":\"string\"},{\"type\":\"object\",\"properties\":{\"command\":0},\"required\":[\"command\"]}," ++
  "{\"type\":\"object\",\"properties\":{\"name\":0,\"input\":1},\"required\":[\"name\",\"input\"],\"additionalProperties\":false}],\"root\":2}"
#guard validAt toolSchema "{\"name\":\"Bash\",\"input\":{\"command\":\"ls\"}}" == some true
#guard validAt toolSchema "{\"name\":\"Bash\",\"input\":{}}" == some false
#guard validAt toolSchema "{\"name\":\"Bash\",\"input\":{\"command\":\"ls\"},\"x\":1}" == some false
#guard validAt toolSchema "{\"name\":7,\"input\":{\"command\":\"ls\"}}" == some false
-- the compiled automaton agrees (compile_correct), checked on the same records
#guard (sch toolSchema).map (fun S => (compile S).eval (val "{\"name\":\"Bash\",\"input\":{\"command\":\"ls\"}}") ==
  some (bitsOf S (val "{\"name\":\"Bash\",\"input\":{\"command\":\"ls\"}}"))) == some true

end Dregg2.Tree.Pins
