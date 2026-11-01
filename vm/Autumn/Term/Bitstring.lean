/-!
Clean-room Erlang-style bitstrings (MIT).

`trailingBits = 0` is an aligned **binary** (byte-multiple size). `1…7` means the
last byte contributes only its high `(8 - trailingBits)` bits; unused low bits
must be zero when `Valid`. No Lynx Bitstring text.
-/

namespace Autumn.Term

/-- A bitstring: packed bytes with optional unused low bits in the last byte. -/
structure Bitstring where
  bytes : ByteArray
  /-- Unused low bits in the last byte (`0` ⇒ aligned binary). Empty ⇒ `0`. -/
  trailingBits : Nat

namespace Bitstring

instance : Inhabited Bitstring where
  default := ⟨ByteArray.empty, 0⟩

instance : Repr Bitstring where
  reprPrec b _ :=
    let body :=
      String.intercalate ", "
        ((List.range b.bytes.size).map fun i =>
          Nat.repr (b.bytes.get! i).toNat)
    if b.trailingBits = 0 then
      s!"<<{body}>>"
    else
      s!"<<{body}:{b.trailingBits}>>"

/-- Canonical packing: `trailingBits < 8`, empty ⇒ aligned, unused low bits cleared. -/
def Valid (b : Bitstring) : Prop :=
  b.trailingBits < 8 ∧
    (b.bytes.size = 0 → b.trailingBits = 0) ∧
    (b.trailingBits = 0 ∨
      (0 < b.bytes.size ∧
        (b.bytes.get! (b.bytes.size - 1)).toNat % (2 ^ b.trailingBits) = 0))

/-- Aligned binary from raw bytes. -/
def ofBytes (bytes : ByteArray) : Bitstring :=
  ⟨bytes, 0⟩

@[simp] theorem ofBytes_valid (bytes : ByteArray) : Valid (ofBytes bytes) :=
  ⟨Nat.zero_lt_succ 7, fun _ => rfl, Or.inl rfl⟩

/-- Bit size (Erlang `bit_size`). -/
def bitSize (b : Bitstring) : Nat :=
  b.bytes.size * 8 - b.trailingBits

/-- True when size is a multiple of 8 (`is_binary`). -/
def isBinary (b : Bitstring) : Bool :=
  decide (b.trailingBits = 0)

/-- Append two aligned binaries; `none` if either is partial. -/
def appendAligned (a b : Bitstring) : Option Bitstring :=
  if a.trailingBits != 0 || b.trailingBits != 0 then none
  else some ⟨a.bytes ++ b.bytes, 0⟩

/-- Byte-wise equality (including trailingBits). -/
def beq (a b : Bitstring) : Bool :=
  a.trailingBits == b.trailingBits && a.bytes == b.bytes

instance : BEq Bitstring where
  beq := beq

/-- Lexicographic order: trailingBits, then bytes. -/
def lt (a b : Bitstring) : Bool :=
  if a.trailingBits != b.trailingBits then decide (a.trailingBits < b.trailingBits)
  else
    Id.run do
      let mut i := 0
      while i < a.bytes.size && i < b.bytes.size do
        let x := a.bytes.get! i
        let y := b.bytes.get! i
        if x != y then return decide (x.toNat < y.toNat)
        i := i + 1
      pure (decide (a.bytes.size < b.bytes.size))

def toString (b : Bitstring) : String :=
  reprStr b

/-- Nat bytes of a `ByteArray` (encode helper). -/
def toNatBytes (b : ByteArray) : Array Nat :=
  (List.range b.size).toArray.map fun i => (b.get! i).toNat

/-- Build from a JSON-style list of byte values (`0…255`); `none` on range error. -/
def ofNatBytes? (ns : Array Nat) : Option Bitstring :=
  Id.run do
    let mut out := ByteArray.empty
    for n in ns do
      if n ≥ 256 then return none
      out := out.push (UInt8.ofNat n)
    return some (ofBytes out)

/-- Pack a partial bitstring; clears unused low bits. `none` if `trailing ≥ 8`
or empty with nonzero trailing. -/
def ofBytesTrailing? (bytes : ByteArray) (trailing : Nat) : Option Bitstring :=
  if trailing ≥ 8 then none
  else if bytes.size = 0 then
    if trailing = 0 then some (ofBytes bytes) else none
  else if trailing = 0 then
    some (ofBytes bytes)
  else
    let last := bytes.get! (bytes.size - 1)
    let cleared := UInt8.ofNat ((last.toNat / (2 ^ trailing)) * (2 ^ trailing))
    some ⟨bytes.set! (bytes.size - 1) cleared, trailing⟩

/-- MSB-first bit list of length `bitSize b` (each entry `0` or `1`). -/
def toBits (b : Bitstring) : Array Nat :=
  Id.run do
    let total := bitSize b
    let mut bits : Array Nat := Array.empty
    let mut i := 0
    while i < total do
      let byteIdx := i / 8
      let bitInByte := 7 - i % 8
      let byte := (b.bytes.get! byteIdx).toNat
      bits := bits.push ((byte >>> bitInByte) % 2)
      i := i + 1
    return bits

/-- Pack MSB-first `0`/`1` bits into a `Valid` bitstring (`none` on bad bits). -/
def ofBits? (bits : Array Nat) : Option Bitstring :=
  Id.run do
    for b in bits do
      if b ≠ 0 && b ≠ 1 then return none
    if bits.size = 0 then
      return some (ofBytes ByteArray.empty)
    let trailing := (8 - bits.size % 8) % 8
    let mut padded := bits
    let mut t := 0
    while t < trailing do
      padded := padded.push 0
      t := t + 1
    let mut out := ByteArray.empty
    let mut i := 0
    while i < padded.size do
      let mut acc := 0
      let mut j := 0
      while j < 8 do
        acc := acc * 2 + padded[i + j]!
        j := j + 1
      out := out.push (UInt8.ofNat acc)
      i := i + 8
    return ofBytesTrailing? out trailing

/-- Take the high `n` bits as an integer (MSB-first). `none` if `n > bitSize`. -/
def getInteger? (b : Bitstring) (n : Nat) : Option Int :=
  if n > bitSize b then none
  else
    let bits := (toBits b).extract 0 n
    some (Int.ofNat (bits.foldl (fun acc bit => acc * 2 + bit) 0))

/-- Drop the high `n` bits; remainder repacked `Valid`. `none` if `n > bitSize`. -/
def drop? (b : Bitstring) (n : Nat) : Option Bitstring :=
  if n > bitSize b then none
  else ofBits? ((toBits b).extract n (bitSize b))

/-- Append bitstrings at bit granularity (teaching `<>/2` of partials). -/
def append (a b : Bitstring) : Option Bitstring :=
  ofBits? (toBits a ++ toBits b)

/-- Decode one UTF-8 codepoint from a **byte-aligned** bitstring.
Returns `(codepoint, rest)`. `none` if unaligned, empty, or invalid UTF-8. -/
def getUtf8? (b : Bitstring) : Option (Nat × Bitstring) :=
  if b.trailingBits ≠ 0 then none
  else if b.bytes.size = 0 then none
  else
    let b0 := (b.bytes.get! 0).toNat
    if b0 < 0x80 then
      match drop? b 8 with
      | some rest => some (b0, rest)
      | none => none
    else if b0 < 0xC0 then none
    else if b0 < 0xE0 then
      if b.bytes.size < 2 then none
      else
        let b1 := (b.bytes.get! 1).toNat
        if b1 &&& 0xC0 ≠ 0x80 then none
        else
          let cp := ((b0 &&& 0x1F) <<< 6) ||| (b1 &&& 0x3F)
          if cp < 0x80 then none
          else match drop? b 16 with
            | some rest => some (cp, rest)
            | none => none
    else if b0 < 0xF0 then
      if b.bytes.size < 3 then none
      else
        let b1 := (b.bytes.get! 1).toNat
        let b2 := (b.bytes.get! 2).toNat
        if b1 &&& 0xC0 ≠ 0x80 || b2 &&& 0xC0 ≠ 0x80 then none
        else
          let cp :=
            ((b0 &&& 0x0F) <<< 12) ||| ((b1 &&& 0x3F) <<< 6) ||| (b2 &&& 0x3F)
          if cp < 0x800 then none
          else match drop? b 24 with
            | some rest => some (cp, rest)
            | none => none
    else if b0 < 0xF8 then
      if b.bytes.size < 4 then none
      else
        let b1 := (b.bytes.get! 1).toNat
        let b2 := (b.bytes.get! 2).toNat
        let b3 := (b.bytes.get! 3).toNat
        if b1 &&& 0xC0 ≠ 0x80 || b2 &&& 0xC0 ≠ 0x80 || b3 &&& 0xC0 ≠ 0x80 then none
        else
          let cp :=
            ((b0 &&& 0x07) <<< 18) ||| ((b1 &&& 0x3F) <<< 12) |||
              ((b2 &&& 0x3F) <<< 6) ||| (b3 &&& 0x3F)
          if cp < 0x10000 || cp > 0x10FFFF then none
          else match drop? b 32 with
            | some rest => some (cp, rest)
            | none => none
    else none

/-! ## Pure laws for append / UTF-8 decode (teaching subset) -/

/-- `3`-bit `0b101` `<>` `5`-bit `0b11000` packs to aligned `0xB8`. -/
theorem append_partial_observes_0xb8 :
    (match (do
        let a ← ofBits? #[1, 0, 1]
        let b ← ofBits? #[1, 1, 0, 0, 0]
        append a b) with
      | some c => c.beq (ofBytes (ByteArray.mk #[0xB8])) && isBinary c
      | none => false) =
      true := by
  native_decide

/-- Aligned ASCII `A` decodes as codepoint `65` with empty rest. -/
theorem getUtf8_ascii_A :
    (match getUtf8? (ofBytes (ByteArray.mk #[65])) with
      | some (65, rest) => decide (bitSize rest = 0)
      | _ => false) =
      true := by
  native_decide

/-- Two-byte UTF-8 `U+00E9` (é) decodes with empty rest. -/
theorem getUtf8_e_acute :
    (match getUtf8? (ofBytes (ByteArray.mk #[0xC3, 0xA9])) with
      | some (0xE9, rest) => decide (bitSize rest = 0)
      | _ => false) =
      true := by
  native_decide

/-- Empty / invalid lead byte soft-fails. -/
theorem getUtf8_empty_none :
    getUtf8? (ofBytes ByteArray.empty) = none := by
  native_decide

theorem getUtf8_invalid_cont_none :
    getUtf8? (ofBytes (ByteArray.mk #[0x80])) = none := by
  native_decide

end Bitstring
end Autumn.Term
