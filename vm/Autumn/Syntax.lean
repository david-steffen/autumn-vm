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

def mod (version : Nat) (entry : FunName) (functions : Array Function) : Module :=
  { version, entry, functions }

/-- Demo module authored purely in Lean (same as addMain). -/
def leanDemoModule : Module := addMainModule

end Syntax
end Autumn
