namespace X86Registers

/-- External memory operations of the upstream Sail model. -/
class MemoryPrimitives where
  read : (kind : read_kind) → (addressWidth : Nat) → BitVec addressWidth →
    (count : Nat) → SailM (BitVec (8 * count))
  writeAddress : (kind : write_kind) → (addressWidth : Nat) → BitVec addressWidth →
    (count : Nat) → SailM Unit
  writeValue : (kind : write_kind) → (addressWidth : Nat) → BitVec addressWidth →
    (count : Nat) → BitVec (8 * count) → SailM Bool

abbrev read_mem [MemoryPrimitives] (kind : read_kind) (addressWidth : Nat)
    (address : BitVec addressWidth) (count : Nat) : SailM (BitVec (8 * count)) :=
  MemoryPrimitives.read kind addressWidth address count

abbrev write_mem_ea [MemoryPrimitives] (kind : write_kind) (addressWidth : Nat)
    (address : BitVec addressWidth) (count : Nat) : SailM Unit :=
  MemoryPrimitives.writeAddress kind addressWidth address count

abbrev write_mem [MemoryPrimitives] (kind : write_kind) (addressWidth : Nat)
    (address : BitVec addressWidth) (count : Nat) (value : BitVec (8 * count)) : SailM Bool :=
  MemoryPrimitives.writeValue kind addressWidth address count value

end X86Registers
