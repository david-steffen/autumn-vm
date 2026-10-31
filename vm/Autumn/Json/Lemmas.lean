import Autumn.Json.Encode
import Autumn.Json.Decode
import Autumn.WellFormed

/-!
# Encode ↔ Decode roundtrip

JSON is the Mix ↔ Lean contract. Start with tags; extend to Instr/Module as needed.
-/

namespace Autumn

theorem decodeTag_encodeTag (t : Tag) :
    Json.Decode.decodeTag (Json.Encode.encodeTag t) = .ok t := by
  cases t <;> rfl

/-- Completeness for resolvable names: Prop ⇒ Bool. -/
theorem FunName.resolvableB_complete (m : Module) (name : FunName)
    (h : FunName.resolvable m name) : FunName.resolvableB m name = true := by
  simp only [FunName.resolvable, FunName.resolvableB, Bool.or_eq_true] at h ⊢
  exact h

end Autumn
