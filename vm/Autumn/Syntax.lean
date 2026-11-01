import Autumn.Instr
import Autumn.Examples

namespace Autumn
namespace Syntax

/-- In-Lean authoring helpers (Lean frontend stub). -/
def litInt (n : Int) : Term := .int n
def litAtom (s : String) : Term := .atom s
def litBool (b : Bool) : Term := .bool b

def fn (name : FunName) (arity locals : Nat) (code : Array Instr) : Function :=
  { name, arity, locals, code }

def mod (entry : FunName) (functions : Array Function) : Module :=
  Module.ofFunctions entry functions

def codeMod (name : String) (functions : Array Function) : CodeModule :=
  { name, functions }

def program (entry : FunName) (modules : Array CodeModule) : Module :=
  { format := 1, entry, modules }

/-- Demo module authored purely in Lean (same as addMain). -/
def leanDemoModule : Module := addMainModule

end Syntax
end Autumn
