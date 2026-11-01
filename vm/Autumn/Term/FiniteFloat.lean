/-!
Finite IEEE binary64 values for Autumn terms.

Exponent field 2047 (infinities / NaNs) is unrepresentable. Arithmetic goes
through `Float.Model` and returns `none` when the IEEE result is non-finite.
Clean-room teaching model (MIT); not derived from Lynx sources.
-/

namespace Autumn.Term

/-- A finite IEEE binary64 value in canonical field form. -/
structure FiniteFloat where
  negative : Bool
  /-- Biased exponent; `2047` (inf/NaN) is excluded. -/
  exponent : Fin 2047
  /-- Trailing significand (52 bits). -/
  fraction : Fin (2 ^ 52)
  deriving DecidableEq, Repr

namespace FiniteFloat

instance : Inhabited FiniteFloat where
  default := ⟨false, 0, 0⟩

/-- Pack fields into an IEEE binary64 bit pattern. -/
def toUInt64 (value : FiniteFloat) : UInt64 :=
  UInt64.ofNat
    ((if value.negative then 2 ^ 63 else 0) +
      value.exponent.val * 2 ^ 52 +
      value.fraction.val)

/-- Unpack bits; `none` when the biased exponent is `2047`. -/
def ofUInt64? (bits : UInt64) : Option FiniteFloat :=
  let n := bits.toNat
  let exp := n / 2 ^ 52 % 2048
  if h : exp < 2047 then
    some ⟨n / 2 ^ 63 != 0, ⟨exp, h⟩, ⟨n % 2 ^ 52, Nat.mod_lt _ (by decide)⟩⟩
  else
    none

/-- Logical IEEE model used for arithmetic and ordering. -/
def toModel (value : FiniteFloat) : Float.Model :=
  Float.Model.ofBits value.toUInt64

/-- Finite projection of a model; `none` on inf/NaN. -/
def ofModel (value : Float.Model) : Option FiniteFloat :=
  ofUInt64? value.toBits

/-- Round `mantissa * 10 ^ exponent` to binary64; `none` on overflow. -/
def ofScientific (negative : Bool) (mantissa : Nat) (exponent : Int) : Option FiniteFloat :=
  let model := Float.Model.ofScientific mantissa exponent
  ofModel (if negative then -model else model)

/-- Convert an integer; `none` if the magnitude overflows binary64. -/
def ofInt (value : Int) : Option FiniteFloat :=
  ofModel (Float.Model.ofInt value)

def add (left right : FiniteFloat) : Option FiniteFloat :=
  ofModel (left.toModel + right.toModel)

def sub (left right : FiniteFloat) : Option FiniteFloat :=
  ofModel (left.toModel - right.toModel)

def mul (left right : FiniteFloat) : Option FiniteFloat :=
  ofModel (left.toModel * right.toModel)

def div (left right : FiniteFloat) : Option FiniteFloat :=
  ofModel (left.toModel / right.toModel)

/-- IEEE order on finite values (`NaN` excluded by construction). -/
def lt (left right : FiniteFloat) : Bool :=
  Float.Model.lt left.toModel right.toModel

/-- IEEE equality (so `+0` equals `-0`). -/
def beq (left right : FiniteFloat) : Bool :=
  Float.Model.beq left.toModel right.toModel

/-- Nonnegative mathematical magnitude. -/
def magnitude (value : FiniteFloat) : Rat :=
  if value.exponent.val = 0 then
    if value.fraction.val = 0 then 0
    else (value.fraction.val : Rat) * (2 : Rat) ^ (-1074 : Int)
  else
    ((2 ^ 52 + value.fraction.val : Nat) : Rat) *
      (2 : Rat) ^ (Int.ofNat value.exponent.val - 1075)

/-- Exact rational value; `+0` and `-0` share magnitude `0` but remain distinct. -/
def toRat (value : FiniteFloat) : Rat :=
  if value.negative then -value.magnitude else value.magnitude

protected def toString (value : FiniteFloat) : String :=
  toString (Float.ofBits value.toUInt64)

instance : ToString FiniteFloat where
  toString := FiniteFloat.toString

/-- Reconstruct from exact field components (JSON / IR). -/
def ofFields? (negative : Bool) (exponent fraction : Nat) : Option FiniteFloat :=
  if hExp : exponent < 2047 then
    if hFrac : fraction < 2 ^ 52 then
      some ⟨negative, ⟨exponent, hExp⟩, ⟨fraction, hFrac⟩⟩
    else none
  else none

end FiniteFloat
end Autumn.Term
