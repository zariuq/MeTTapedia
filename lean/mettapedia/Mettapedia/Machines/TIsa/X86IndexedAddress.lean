import Mettapedia.Machines.TIsa.X86PlacedFrameAddress

/-!
# Indexed region addresses checked against the region length

The narrow indexed-address form computes `r15 := index * 2^scale + extent` with
LEA, compares it with the region's length field in the ABI frame, rejects when
it is above, and forms the address with a second LEA from the base register and
the scaled index. Both LEAs use a mod-00 SIB operand of the same generated Sail
model as the other handlers; LEA neither reads data memory nor writes flags.
Index and base are low registers. The scaled index plus extent must not wrap,
which the emitter guarantees by the index's width. Success takes four fetches
and rejection three. The p1 adapter's store guards instantiate this check.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Mettapedia.Machines.TIsa.X86IndexedAddress

open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution
open X86PreparedLea (Index)
local instance : MemoryPrimitives := X86Memory.ordinary

/-- A low base register; `rbp` is excluded because mod-00 SIB base 5 means no base. -/
abbrev Base := { reg : Fin 8 // reg.val ≠ 5 }

def Base.register (base : Base) : Fin 16 := ⟨base.val.val, base.val.isLt.trans (by decide)⟩

/-- SIB byte selecting `index * 2^scale` and no base (a disp32 follows). -/
def scaledSib (index : Index) (scale : Fin 4) : BitVec 8 := .ofNat 8 (64 * scale.val + 8 * index.val.val + 5)

/-- SIB byte selecting `base + index * 2^scale`. -/
def basedSib (index : Index) (scale : Fin 4) (base : Base) : BitVec 8 :=
  .ofNat 8 (64 * scale.val + 8 * index.val.val + base.val.val)

/-- ModRM byte of a mod-00 SIB operand with `destination` in the reg field. -/
def sibModRM (destination : Fin 16) : BitVec 8 := .ofNat 8 (8 * (destination.val % 8) + 4)

private theorem scaled_fields (destination : Fin 16) (index : Index) (scale : Fin 4) :
    Functions._get_sib_base (scaledSib index scale) = (5#3) ∧
      Functions.eq_bits_nat (Functions.reg_index (Functions._get_sib_index (scaledSib index scale))
        (rex true destination 0) (1#2)) 4 = false ∧
      Sail.BitVec.toNatInt (Functions.reg_index (Functions._get_sib_index (scaledSib index scale))
        (rex true destination 0) (1#2)) = (index.register.val : Int) ∧
      Sail.BitVec.toNatInt (Functions._get_sib_scale (scaledSib index scale)) = (scale.val : Int) := by
  have all : ∀ destination : Fin 16, ∀ i : Fin 8, ∀ distinct : i.val ≠ 4, ∀ scale : Fin 4,
      let index : Index := ⟨i, distinct⟩
      Functions._get_sib_base (scaledSib index scale) = (5#3) ∧
        Functions.eq_bits_nat (Functions.reg_index (Functions._get_sib_index (scaledSib index scale))
          (rex true destination 0) (1#2)) 4 = false ∧
        Sail.BitVec.toNatInt (Functions.reg_index (Functions._get_sib_index (scaledSib index scale))
          (rex true destination 0) (1#2)) = (index.register.val : Int) ∧
        Sail.BitVec.toNatInt (Functions._get_sib_scale (scaledSib index scale)) = (scale.val : Int) := by
    decide +kernel
  exact all destination index.val index.property scale

private theorem based_fields (destination : Fin 16) (index : Index) (scale : Fin 4) (base : Base) :
    (Functions._get_sib_base (basedSib index scale base) == (5#3)) = false ∧
      Sail.BitVec.toNatInt (Functions.reg_index (Functions._get_sib_base (basedSib index scale base))
        (rex true destination 0) (0#2)) = (base.register.val : Int) ∧
      Functions.eq_bits_nat (Functions.reg_index (Functions._get_sib_index (basedSib index scale base))
        (rex true destination 0) (1#2)) 4 = false ∧
      Sail.BitVec.toNatInt (Functions.reg_index (Functions._get_sib_index (basedSib index scale base))
        (rex true destination 0) (1#2)) = (index.register.val : Int) ∧
      Sail.BitVec.toNatInt (Functions._get_sib_scale (basedSib index scale base)) = (scale.val : Int) := by
  have all : ∀ destination : Fin 16, ∀ i : Fin 8, ∀ distinct : i.val ≠ 4, ∀ scale : Fin 4,
      ∀ b : Fin 8, ∀ notFive : b.val ≠ 5,
      let index : Index := ⟨i, distinct⟩
      let base : Base := ⟨b, notFive⟩
      (Functions._get_sib_base (basedSib index scale base) == (5#3)) = false ∧
        Sail.BitVec.toNatInt (Functions.reg_index (Functions._get_sib_base (basedSib index scale base))
          (rex true destination 0) (0#2)) = (base.register.val : Int) ∧
        Functions.eq_bits_nat (Functions.reg_index (Functions._get_sib_index (basedSib index scale base))
          (rex true destination 0) (1#2)) 4 = false ∧
        Sail.BitVec.toNatInt (Functions.reg_index (Functions._get_sib_index (basedSib index scale base))
          (rex true destination 0) (1#2)) = (index.register.val : Int) ∧
        Sail.BitVec.toNatInt (Functions._get_sib_scale (basedSib index scale base)) = (scale.val : Int) := by
    decide +kernel
  exact all destination index.val index.property scale base.val base.property

private theorem scaled_word (offset : Word) (scale : Fin 4) :
    BitVec.ofInt 64 (Functions.ash_left_int offset.toInt (scale.val : Int).toNat) =
      offset * BitVec.ofNat 64 (2 ^ scale.val) := by
  rw [Functions.ash_left_int]
  change BitVec.ofInt 64 (offset.toInt * (2 : Int) ^ scale.val) = _
  rw [BitVec.ofInt_mul, BitVec.ofInt_toInt]
  congr 1

theorem effective_scaled (state : State) (destination : Fin 16) (index : Index) (scale : Fin 4)
    (atDisp : BitVec 48) (pointer offset : Word) (displacement : BitVec 32)
    (attributes : Vector (BitVec 16) 6) (prefixes : BitVec 52)
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (upper : atDisp.toInt + 4 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (ip : state.regs.get? .rip = some pointer)
    (present : ∀ i < 4, state.mem.get? ((address atDisp.toInt i).signExtend 52).toNat =
      some (displacement.extractLsb' (8 * i) 8))
    (offsetKnown : lookup state index.register = some offset) :
    (Functions.x86_effective_addr .Mode_64bit prefixes atDisp (rex true destination 0) (4#3) (0#2)
      (scaledSib index scale) (0#3)).run state =
      .ok (offset * BitVec.ofNat 64 (2 ^ scale.val) + displacement.signExtend 64, (4 : Int)) state := by
  have fields := scaled_fields destination index scale
  unfold Functions.x86_effective_addr
  rw [addressOverride]
  simp only [show Functions.select_address_size .Mode_64bit (some prefixes) = (pure 8 : SailM Int) by
    simp [Functions.select_address_size, Functions.in_64bit_mode, addressOverride],
    pure_bind, show ((2 : Int) == 8) = false from rfl, Bool.false_eq_true, ite_false]
  unfold Functions.x86_effective_addr_32_64 Functions.x86_effective_addr_from_sib
  simp only [show Functions.eq_bits_nat (0#2) 0 = true from rfl,
    show Functions.eq_bits_nat (4#3) 4 = true from rfl, fields.1,
    show ((5#3) == (0b101#3)) = true from rfl,
    show Functions.select_address_size .Mode_64bit none = (pure 8 : SailM Int) from rfl,
    show Int.toNat (8 : Int) = 8 from rfl, ite_true, pure_bind, bind_assoc]
  rw [show Sail.BitVec.signExtend atDisp 64 = atDisp.signExtend 64 from rfl, run_bind,
    X86ReadWords.signed_displacement_exact state atDisp attributes pointer displacement upper segments application ip
      present]
  dsimp only
  simp only [fields.2.1, Bool.false_eq_true, ite_false, Functions.in_64bit_mode, ite_true, fields.2.2.1, run_bind]
  rw [rgfi_exact state index.register offset offsetKnown]
  dsimp only
  rw [fields.2.2.2, if_neg (by decide : ¬ ((103#8) == (0#8)) = true)]
  simp only [run_pure, X86Alu.bits_of_int_eq, BitVec.ofInt_add, BitVec.ofInt_toInt, scaled_word]
  rw [BitVec.zero_add]

theorem effective_based (state : State) (destination : Fin 16) (index : Index) (scale : Fin 4) (base : Base)
    (atDisp : BitVec 48) (baseValue offset : Word) (prefixes : BitVec 52)
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (baseKnown : lookup state base.register = some baseValue)
    (offsetKnown : lookup state index.register = some offset) :
    (Functions.x86_effective_addr .Mode_64bit prefixes atDisp (rex true destination 0) (4#3) (0#2)
      (basedSib index scale base) (0#3)).run state =
      .ok (baseValue + offset * BitVec.ofNat 64 (2 ^ scale.val), (0 : Int)) state := by
  have fields := based_fields destination index scale base
  unfold Functions.x86_effective_addr
  rw [addressOverride]
  simp only [show Functions.select_address_size .Mode_64bit (some prefixes) = (pure 8 : SailM Int) by
    simp [Functions.select_address_size, Functions.in_64bit_mode, addressOverride],
    pure_bind, show ((2 : Int) == 8) = false from rfl, Bool.false_eq_true, ite_false]
  unfold Functions.x86_effective_addr_32_64 Functions.x86_effective_addr_from_sib
  simp only [show Functions.eq_bits_nat (0#2) 0 = true from rfl,
    show Functions.eq_bits_nat (4#3) 4 = true from rfl, fields.1, Bool.false_eq_true,
    Functions.in_64bit_mode, ite_true, ite_false, pure_bind, bind_assoc, fields.2.1, run_bind]
  rw [rgfi_exact state base.register baseValue baseKnown]
  dsimp only
  simp only [fields.2.2.1, Bool.false_eq_true, ite_false, fields.2.2.2.1]
  rw [rgfi_exact state index.register offset offsetKnown]
  dsimp only
  rw [fields.2.2.2.2, if_neg (by decide : ¬ ((103#8) == (0#8)) = true)]
  simp only [run_pure, X86Alu.bits_of_int_eq, BitVec.ofInt_add, BitVec.ofInt_toInt, scaled_word]
  rw [BitVec.add_zero]

private theorem sib_modrm_fields (destination : Fin 16) :
    Functions._get_modr_m_r_m (sibModRM destination) = (4#3) ∧ Functions._get_modr_m_mod (sibModRM destination) = (0#2) ∧
      Functions.reg_index (Functions._get_modr_m_reg (sibModRM destination)) (rex true destination 0) (2#2) =
        BitVec.ofNat 4 destination.val ∧
      Functions.x86_decode_sib_p (sibModRM destination) false = true := by
  revert destination
  decide +kernel

private theorem consumed_bits (consumed : Fin 8) :
    Sail.BitVec.zeroExtend (Functions.bits_of_int (consumed.val : Int) 3) 48 = BitVec.ofNat 48 consumed.val ∧
      (BitVec.ofNat 48 consumed.val).toInt = consumed.val := by
  revert consumed
  decide +kernel

/-- LEA of a mod-00 SIB operand into `destination`, given its effective address. -/
theorem handler (state : State) (destination : Fin 16) (sib : BitVec 8) (start atByte next : BitVec 48)
    (prefixes : BitVec 52) (value : Word) (consumed : Fin 8)
    (effective : (Functions.x86_effective_addr .Mode_64bit prefixes atByte (rex true destination 0) (4#3) (0#2) sib
      (0#3)).run state = .ok (value, (consumed.val : Int)) state)
    (advance : atByte.toInt + consumed.val = next.toInt)
    (length : Functions.check_instruction_length start next (0#3) = none)
    (quiet : state.regs.get? .log_register_writes = some false) :
    (Functions.x86_lea .Mode_64bit start atByte prefixes (rex true destination 0) (0x8d#8) (sibModRM destination) sib).run state =
      .ok () (X86Move.putPointer (put state destination value) next) := by
  have fields := sib_modrm_fields destination
  have bits := consumed_bits consumed
  unfold Functions.x86_lea
  rw [X86Move.operand_size64 destination 0 prefixes]
  simp only [pure_bind, show Functions.check_range 2 8 8 = (pure 8 : SailM Int) from rfl]
  rw [fields.1, fields.2.1, run_bind, effective]
  dsimp only
  rw [bits.1, run_bind, X86PrefixRead.add_pointer_checked state atByte _ next (by rw [bits.2]; exact advance)]
  dsimp only
  rw [length, if_neg (by decide : ¬Functions.is_some (none : Option Int) = true)]
  have roundtrip : Functions.sail_mask 64 (Functions.trunc_signed 8 value) = value := by
    unfold Functions.trunc_signed Functions.sail_mask Functions.sail_mask_signed
    simp [Sail.BitVec.truncate]
  rw [show Int.toNat (8 : Int) = 8 from rfl, roundtrip, show Functions.bits_of_int 8 4 = (8#4) from rfl,
    fields.2.2.1, run_bind, X86QwordLoad.write_destination64 state destination 0 value quiet]
  apply X86Move.write_pointer64
  simpa only [diagnostic_put] using quiet

theorem dispatch (other : OtherOpcodeHandlers) (rexByte modrm sib : BitVec 8) (start temp : BitVec 48)
    (memoryOperand : Functions._get_modr_m_mod modrm = (0#2)) :
    letI : OtherOpcodeHandlers := X86PreparedLea.linked other
    Functions.one_byte_opcode_execute .Mode_64bit start temp (X86LegacyFetch.packet (0x8d#8)) rexByte (0x8d#8) modrm sib =
      Functions.x86_lea .Mode_64bit start temp (X86LegacyFetch.packet (0x8d#8)) rexByte (0x8d#8) modrm sib := by
  let : OtherOpcodeHandlers := X86PreparedLea.linked other
  have step : Functions.one_byte_opcode_execute .Mode_64bit start temp (X86LegacyFetch.packet (0x8d#8)) rexByte
      (0x8d#8) modrm sib =
      (do
        if ((Functions._get_modr_m_mod modrm == 0b11#2) ||
            (0xF0#8 == Functions._get_prefixes_lck (X86LegacyFetch.packet (0x8d#8))))
        then Functions.x86_fault "(:UD)" else pure ()
        Functions.x86_lea .Mode_64bit start temp (X86LegacyFetch.packet (0x8d#8)) rexByte (0x8d#8) modrm sib) := rfl
  rw [step, memoryOperand]
  simp only [show ((0#2 : BitVec 2) == 0b11#2) = false from rfl,
    show (0xF0#8 == Functions._get_prefixes_lck (X86LegacyFetch.packet (0x8d#8))) = false from by decide,
    Bool.false_or, Bool.false_eq_true, ite_false]

/-- The fetched LEA: REX.W with `destination`'s R bit, `8d`, the SIB ModRM, the SIB byte, then
`consumed` displacement bytes. -/
theorem fetched (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) (state : State)
    (destination : Fin 16) (sib : BitVec 8) (origin : X86LegacyFetch.Basis state) (atByte next : BitVec 48)
    (value : Word) (consumed : Fin 8)
    (beforeByte : origin.next.toInt + 1 = atByte.toInt) (advance : atByte.toInt + consumed.val = next.toInt)
    (effective : (Functions.x86_effective_addr .Mode_64bit (X86LegacyFetch.packet (0x8d#8)) atByte
      (rex true destination 0) (4#3) (0#2) sib (0#3)).run state = .ok (value, (consumed.val : Int)) state)
    (quiet : state.regs.get? .log_register_writes = some false)
    (rexByte : state.mem.get? (origin.address.signExtend 52).toNat = some (rex true destination 0))
    (opcodeByte : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0x8d#8))
    (modrmByte : state.mem.get? (origin.modrmAddress.signExtend 52).toNat = some (sibModRM destination))
    (sibByte : state.mem.get? (origin.next.signExtend 52).toNat = some sib) :
    letI : OtherOpcodeHandlers := X86PreparedLea.linked other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer (put state destination value) next) := by
  let : OtherOpcodeHandlers := X86PreparedLea.linked other
  let : VectorOpcodeHandlers := vector
  have shape : X86LegacyFetch.RegularOpcode (0x8d#8) := (X86LegacyFetch.checkOpcode_iff _).mp (by decide +kernel)
  rw [X86SibStore.fetch_to_dispatch_sib (0x8d#8) shape true state origin atByte destination 0
    (sibModRM destination) sib (sib_modrm_fields destination).2.2.2 beforeByte rexByte opcodeByte modrmByte sibByte]
  rw [dispatch other _ _ _ _ _ (sib_modrm_fields destination).2.1]
  have length : Functions.check_instruction_length origin.address next (0#3) = none := by
    apply X86FrameLoad.length_from_distance _ _ (4 + consumed.val) (by omega)
    have := origin.step3
    have := origin.step2
    omega
  exact handler state destination sib origin.address atByte next (X86LegacyFetch.packet (0x8d#8)) value consumed
    effective advance length quiet

/-! ## The placed check -/

open X86PlacedInstruction (At)
open X86PlacedScalar (Code)
open X86PlacedMemory (Cell Controls Reads)

noncomputable abbrev handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :=
  X86PlacedFrameAddress.handlers other extra

/-- `lea r15, [index * 2^scale + extent]`. -/
def extentCode (index : Index) (scale : Fin 4) (extent : BitVec 32) : List Nat :=
  [(rex true 15 0).toNat, 0x8d, (sibModRM 15).toNat, (scaledSib index scale).toNat] ++ X86Bounds.little32 extent

/-- `cmp r15, [rdi + field]`. -/
def compareCode (field : BitVec 32) : List Nat := [0x4c, 0x3b, 0xbf] ++ X86Bounds.little32 field

/-- `lea destination, [base + index * 2^scale]`. -/
def addressCode (destination : Fin 16) (index : Index) (scale : Fin 4) (base : Base) : List Nat :=
  [(rex true destination 0).toNat, 0x8d, (sibModRM destination).toNat, (basedSib index scale base).toNat]

def delta (start target : Nat) : BitVec 32 := .ofInt 32 ((target : Int) - start)

/-- The operands of one narrow indexed-address check. `field` is the frame displacement of the
region's length; `extent` is the room the address's accesses use. -/
structure Shape where
  destination : Fin 16
  index : Index
  scale : Fin 4
  base : Base
  extent : BitVec 32
  field : BitVec 32

def code (shape : Shape) (start reject : Nat) : List Nat :=
  extentCode shape.index shape.scale shape.extent ++ compareCode shape.field ++
    X86NativeJcc.code (.ordinary .above) (delta (start + 21) reject) ++
    addressCode shape.destination shape.index shape.scale shape.base

def Checked (image : NativeImage.View) (start reject : Nat) (shape : Shape) : Prop :=
  start + 25 ≤ image.size ∧ reject ≤ image.size ∧
  (reject : Int) = start + 21 + (delta (start + 21) reject).toInt ∧
  Code image start (extentCode shape.index shape.scale shape.extent) ∧
  Code image (start + 8) (compareCode shape.field) ∧
  Code image (start + 15) (X86NativeJcc.code (.ordinary .above) (delta (start + 21) reject)) ∧
  Code image (start + 21) (addressCode shape.destination shape.index shape.scale shape.base)

instance (image : NativeImage.View) (start reject : Nat) (shape : Shape) :
    Decidable (Checked image start reject shape) := inferInstanceAs (Decidable (_ ∧ _))

private theorem codeByte {image : NativeImage.View} {state : State} {base : BitVec 48} {start : Nat}
    (point : At image state base start) (inside : start ≤ image.size) {bytes : List Nat}
    (code : Code image start bytes) (offset value : Nat) (found : bytes[offset]? = some value) :
    state.mem.get? ((address base.toInt (start + offset)).signExtend 52).toNat = some (.ofNat 8 value) := by
  have byte := point.bytes _ inside bytes code offset value found
  rwa [point.relative_address start offset inside] at byte

private theorem loads_word {image : NativeImage.View} {state : State} {base : BitVec 48} {start : Nat}
    (point : At image state base start) (at4 : Nat) (inside : start + at4 + 4 ≤ image.size) {bytes : List Nat}
    (code : Code image start bytes) (immediate : BitVec 32)
    (encoded : ∀ i : Fin 4, bytes[at4 + i.val]? = some (immediate.extractLsb' (8 * i.val) 8).toNat) :
    ∀ offset < 4, state.mem.get?
      ((address (address base.toInt (start + at4)).toInt offset).signExtend 52).toNat =
      some (immediate.extractLsb' (8 * offset) 8) := by
  intro offset fits
  rw [point.relative_address (start + at4) offset (by omega), Nat.add_assoc]
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
    codeByte point (by omega) code _ _ (encoded ⟨offset, fits⟩)

private theorem extent_word (offset : Word) (scale : Fin 4) (extent : BitVec 32)
    (small : extent.toNat < 2 ^ 31) (noWrap : offset.toNat * 2 ^ scale.val + extent.toNat < 2 ^ 64) :
    (offset * BitVec.ofNat 64 (2 ^ scale.val) + extent.signExtend 64).toNat = offset.toNat * 2 ^ scale.val + extent.toNat := by
  have positive : extent.msb = false := by
    apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
    omega
  have widened : (extent.signExtend 64).toNat = extent.toNat := by
    rw [BitVec.signExtend_eq_setWidth_of_msb_false positive, BitVec.toNat_setWidth_of_le (by decide)]
  have power : (BitVec.ofNat 64 (2 ^ scale.val)).toNat = 2 ^ scale.val := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))
  have product : (offset * BitVec.ofNat 64 (2 ^ scale.val)).toNat = offset.toNat * 2 ^ scale.val := by
    rw [BitVec.toNat_mul, power]
    exact Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_add, product, widened]
  exact Nat.mod_eq_of_lt noWrap

private theorem forms_extent (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {state : State}
    {base : BitVec 48} {start : Nat} (point : At image state base start) (inside : start + 8 ≤ image.size)
    (index : Index) (scale : Fin 4) (extent : BitVec 32) (code : Code image start (extentCode index scale extent))
    (offset : Word) (offsetKnown : lookup state index.register = some offset) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run state = .ok () after ∧
      RegisterFrame {.r15, .rip} state after ∧
      lookup after 15 = some (offset * BitVec.ofNat 64 (2 ^ scale.val) + extent.signExtend 64) ∧
      Nonempty (At image after base (start + 8)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let origin := point.basis (by omega)
  let atDisp := address base.toInt (start + 4)
  let next := address base.toInt (start + 8)
  have beforeDisp : origin.next.toInt + 1 = atDisp.toInt := by
    change (address base.toInt (start + 3)).toInt + 1 = (address base.toInt (start + 4)).toInt
    rw [point.location _ (by omega), point.location _ (by omega)]
    omega
  have advance : atDisp.toInt + (4 : Fin 8).val = next.toInt := by
    change (address base.toInt (start + 4)).toInt + 4 = (address base.toInt (start + 8)).toInt
    rw [point.location _ (by omega), point.location _ inside]
    omega
  have present := loads_word point 4 inside code extent (by intro i; fin_cases i <;> rfl)
  have effective := effective_scaled state 15 index scale atDisp (address base.toInt start |>.signExtend 64) offset
    extent point.mode.attributes (X86LegacyFetch.packet (0x8d#8)) (X86LegacyFetch.packet_address _)
    (by
      change (address base.toInt (start + 4)).toInt + 4 ≤ (2 ^ 47 : Int)
      rw [point.location _ (by omega)]
      have := point.upper
      omega)
    point.mode.segments point.mode.application point.rip present offsetKnown
  have ran := fetched (handlers other extra) vector state 15 (scaledSib index scale) origin atDisp next
    (offset * BitVec.ofNat 64 (2 ^ scale.val) + extent.signExtend 64) 4 beforeDisp advance effective point.quiet
    (by simpa only [origin, X86PlacedInstruction.At.basis, Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      codeByte point (by omega) code 0 _ rfl)
    (codeByte point (by omega) code 1 0x8d rfl)
    (by
      have byte := codeByte point (by omega) code 2 _ rfl
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at byte
      exact byte)
    (by
      have byte := codeByte point (by omega) code 3 _ rfl
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at byte
      exact byte)
  let value := offset * BitVec.ofNat 64 (2 ^ scale.val) + extent.signExtend 64
  let after := X86Move.putPointer (put state 15 value) next
  have kept : RegisterFrame {.r15, .rip} state after :=
    ((put_frame _ _ _).trans (pointer_frame _ _)).mono (by decide)
  exact ⟨after, X86FuelPrefix.fetches_one _ _ ran, kept,
    by rw [show after = X86Move.putPointer _ _ from rfl, X86Move.lookup_putPointer, lookup_put_same],
    ⟨point.advance kept (by decide) (X86FuelPrefix.pointer_rip _ _) point.flags
      ((kept.registers .rflags (by decide)).trans point.knownFlags)⟩⟩

private theorem compares_extent (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {state : State}
    {base : BitVec 48} {start : Nat} (point : At image state base start) (inside : start + 7 ≤ image.size)
    (field : BitVec 32) (code : Code image start (compareCode field)) (controls : Controls state)
    (frame ending length : Word) (cell : Cell frame field) (frameKnown : lookup state 7 = some frame)
    (endKnown : lookup state 15 = some ending) (lengthRead : Reads state cell.address length) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run state = .ok () after ∧ RegisterFrame {.rflags, .rip} state after ∧
      ∃ next : At image after base (start + 7),
        X86BranchCondition.value .above next.flags = decide (length.toNat < ending.toNat) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let origin := point.basis (by omega)
  let next := address base.toInt (start + 7)
  have extent : origin.next.toInt + 4 = next.toInt := by
    change (address base.toInt (start + 3)).toInt + 4 = (address base.toInt (start + 7)).toInt
    rw [point.location _ (by omega), point.location _ inside]
    omega
  obtain ⟨output, ran, calculated⟩ := X86FrameCompare.fetched 15 (handlers other extra) vector state
    origin next cell.address controls.visible controls.controls frame ending length point.flags field extent cell.upper
    frameKnown endKnown controls.controlsKnown point.knownFlags controls.visibleKnown point.quiet cell.effective
    cell.aligned (by
      change state.mem.get? ((address base.toInt start).signExtend 52).toNat = some (0x4c#8)
      simpa only [Nat.add_zero] using codeByte point (by omega) code 0 0x4c rfl)
    (codeByte point (by omega) code 1 0x3b rfl) (codeByte point (by omega) code 2 0xbf rfl)
    (loads_word point 3 inside code field (by intro i; fin_cases i <;> rfl)) lengthRead
  let flags := X86Flags.mergeFlags point.flags output
  let after := X86Move.putPointer (X86Flags.putFlags state flags) next
  have kept : RegisterFrame {.rflags, .rip} state after := (flags_frame _ _).trans (pointer_frame _ _)
  have flagKnown : after.regs.get? .rflags = some flags := by
    rw [(pointer_frame _ _).registers .rflags (by decide)]
    simp [X86Flags.putFlags]
  exact ⟨after, X86FuelPrefix.fetches_one _ _ ran, kept,
    point.advance kept (by decide) (X86FuelPrefix.pointer_rip _ _) flags flagKnown,
    X86P1LoadBounds.above_sense ending length flags calculated.carry calculated.zero⟩

private theorem forms_address (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {state : State}
    {base : BitVec 48} {start : Nat} (point : At image state base start) (inside : start + 4 ≤ image.size)
    (destination : Fin 16) (index : Index) (scale : Fin 4) (baseRegister : Base)
    (code : Code image start (addressCode destination index scale baseRegister)) (baseValue offset : Word)
    (baseKnown : lookup state baseRegister.register = some baseValue)
    (offsetKnown : lookup state index.register = some offset) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run state = .ok () after ∧
      RegisterFrame {key destination, .rip} state after ∧
      lookup after destination = some (baseValue + offset * BitVec.ofNat 64 (2 ^ scale.val)) ∧
      Nonempty (At image after base (start + 4)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let origin := point.basis (by omega)
  let next := address base.toInt (start + 4)
  have beforeNext : origin.next.toInt + 1 = next.toInt := by
    change (address base.toInt (start + 3)).toInt + 1 = (address base.toInt (start + 4)).toInt
    rw [point.location _ (by omega), point.location _ inside]
    omega
  have advance : next.toInt + (0 : Fin 8).val = next.toInt := by simp
  have effective := effective_based state destination index scale baseRegister next baseValue offset
    (X86LegacyFetch.packet (0x8d#8)) (X86LegacyFetch.packet_address _) baseKnown offsetKnown
  have ran := fetched (handlers other extra) vector state destination (basedSib index scale baseRegister) origin next next
    (baseValue + offset * BitVec.ofNat 64 (2 ^ scale.val)) 0 beforeNext advance effective point.quiet
    (by
      have byte := codeByte point (by omega) code 0 _ rfl
      rw [Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] at byte
      exact byte)
    (codeByte point (by omega) code 1 0x8d rfl)
    (by
      have byte := codeByte point (by omega) code 2 _ rfl
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at byte
      exact byte)
    (by
      have byte := codeByte point (by omega) code 3 _ rfl
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at byte
      exact byte)
  let value := baseValue + offset * BitVec.ofNat 64 (2 ^ scale.val)
  let after := X86Move.putPointer (put state destination value) next
  have kept : RegisterFrame {key destination, .rip} state after :=
    ((put_frame _ _ _).trans (pointer_frame _ _)).mono (by intro register; simp)
  exact ⟨after, X86FuelPrefix.fetches_one _ _ ran, kept,
    by rw [show after = X86Move.putPointer _ _ from rfl, X86Move.lookup_putPointer, lookup_put_same],
    ⟨point.advance kept (by
      intro register member
      simp only [Finset.mem_insert, Finset.mem_singleton] at member
      rcases member with rfl | rfl
      · fin_cases destination <;> decide
      · decide) (X86FuelPrefix.pointer_rip _ _) point.flags
      ((kept.registers .rflags (by fin_cases destination <;> decide)).trans point.knownFlags)⟩⟩

abbrev writes (destination : Fin 16) : Finset Register := {key destination, .r15, .rflags, .rip}

private theorem low_kept (base : Base) : key base.register ∉ ({.r15, .rflags, .rip} : Finset Register) := by
  have all : ∀ b : Fin 8, ∀ notFive : b.val ≠ 5,
      key (Base.register ⟨b, notFive⟩) ∉ ({.r15, .rflags, .rip} : Finset Register) := by decide +kernel
  exact all base.val base.property

private theorem index_kept (index : Index) : key index.register ∉ ({.r15, .rflags, .rip} : Finset Register) := by
  have all : ∀ i : Fin 8, ∀ distinct : i.val ≠ 4,
      key (Index.register ⟨i, distinct⟩) ∉ ({.r15, .rflags, .rip} : Finset Register) := by decide +kernel
  exact all index.val index.property

/-- The check up to its conditional jump: `r15` holds the scaled index plus extent and the jump is
taken exactly when that exceeds the region length. -/
private theorem checks (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {state : State} {base : BitVec 48}
    {start reject : Nat} (point : At image state base start) (shape : Shape)
    (code : Checked image start reject shape) (controls : Controls state)
    (frame offset length : Word) (cell : Cell frame shape.field)
    (frameKnown : lookup state 7 = some frame) (offsetKnown : lookup state shape.index.register = some offset)
    (lengthRead : Reads state cell.address length) (small : shape.extent.toNat < 2 ^ 31)
    (noWrap : offset.toNat * 2 ^ shape.scale.val + shape.extent.toNat < 2 ^ 64) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 3).run state = .ok () after ∧ RegisterFrame {.r15, .rflags, .rip} state after ∧
      Nonempty (At image after base
        (if length.toNat < offset.toNat * 2 ^ shape.scale.val + shape.extent.toNat then reject else start + 21)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨span, target, relative, extentBytes, compareBytes, jumpBytes, _addressBytes⟩ := code
  obtain ⟨formed, formedRun, formedFrame, ending, ⟨atCompare⟩⟩ :=
    forms_extent other extra vector point (by omega) shape.index shape.scale shape.extent extentBytes offset offsetKnown
  let compareControls := controls.transport (X86StateFrame.registerOnly formedFrame) (by decide)
  obtain ⟨compared, comparedRun, compareFrame, atJump, condition⟩ :=
    compares_extent other extra vector atCompare (by omega) shape.field compareBytes compareControls frame _ length cell
      ((formedFrame.lookup 7 (by decide)).trans frameKnown) ending
      (lengthRead.preserved (X86StateFrame.registerOnly formedFrame) (by simp))
  obtain ⟨jumped, jumpedRun, jumpFrame, ⟨atNext⟩⟩ :=
    X86PlacedJcc.executes (X86PlacedFrameAddress.nativeBase other) extra vector atJump (by omega) target
      (.ordinary .above) _ (by push_cast at relative ⊢; omega) jumpBytes
  have selects : X86NativeJcc.selects (.ordinary .above) atJump.flags =
      decide (length.toNat < offset.toNat * 2 ^ shape.scale.val + shape.extent.toNat) := by
    change X86BranchCondition.value .above atJump.flags = _
    rw [condition, extent_word offset shape.scale shape.extent small noWrap]
  have arrival : (if X86NativeJcc.selects (.ordinary .above) atJump.flags then reject else start + 8 + 7 + 6) =
      (if length.toNat < offset.toNat * 2 ^ shape.scale.val + shape.extent.toNat then reject else start + 21) := by
    rw [selects]
    by_cases above : length.toNat < offset.toNat * 2 ^ shape.scale.val + shape.extent.toNat
    · simp only [above, decide_true, if_true]
    · simp only [above, decide_false, Bool.false_eq_true, if_false]
  rw [arrival] at atNext
  let h := handlers other extra
  have first := @X86FuelPrefix.fetches_then h vector 1 1 state formed compared formedRun comparedRun
  exact ⟨jumped, @X86FuelPrefix.fetches_then h vector 2 1 state compared jumped first jumpedRun,
    ((formedFrame.trans compareFrame).trans jumpFrame).mono (by decide), ⟨atNext⟩⟩

/-- In range: four fetches form `base + index * 2^scale` in the destination. -/
theorem succeeds (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {state : State} {base : BitVec 48}
    {start reject : Nat} (point : At image state base start) (shape : Shape)
    (code : Checked image start reject shape) (controls : Controls state)
    (frame baseValue offset length : Word) (cell : Cell frame shape.field)
    (frameKnown : lookup state 7 = some frame) (baseKnown : lookup state shape.base.register = some baseValue)
    (offsetKnown : lookup state shape.index.register = some offset)
    (lengthRead : Reads state cell.address length) (small : shape.extent.toNat < 2 ^ 31)
    (fits : offset.toNat * 2 ^ shape.scale.val + shape.extent.toNat ≤ length.toNat) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 4).run state = .ok () after ∧ RegisterFrame (writes shape.destination) state after ∧
      lookup after shape.destination = some (baseValue + offset * BitVec.ofNat 64 (2 ^ shape.scale.val)) ∧
      Nonempty (At image after base (start + 25)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have noWrap : offset.toNat * 2 ^ shape.scale.val + shape.extent.toNat < 2 ^ 64 := by
    have := length.isLt
    omega
  obtain ⟨checked, checkedRun, checkedFrame, ⟨atAddress⟩⟩ := checks other extra vector point shape code controls
    frame offset length cell frameKnown offsetKnown lengthRead small noWrap
  rw [if_neg (by omega)] at atAddress
  obtain ⟨span, _target, _relative, _extentBytes, _compareBytes, _jumpBytes, addressBytes⟩ := code
  obtain ⟨after, formedRun, formedFrame, value, next⟩ := forms_address other extra vector atAddress (by omega)
    shape.destination shape.index shape.scale shape.base addressBytes baseValue offset
    ((checkedFrame.lookup _ (low_kept shape.base)).trans baseKnown)
    ((checkedFrame.lookup _ (index_kept shape.index)).trans offsetKnown)
  let h := handlers other extra
  refine ⟨after, @X86FuelPrefix.fetches_then h vector 3 1 state checked after checkedRun formedRun,
    (checkedFrame.trans formedFrame).mono ?_, value, next⟩
  intro register member
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at member ⊢
  tauto

/-- Out of range: three fetches reach the rejection target, writing only `r15` and the flags. -/
theorem rejects (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {state : State} {base : BitVec 48}
    {start reject : Nat} (point : At image state base start) (shape : Shape)
    (code : Checked image start reject shape) (controls : Controls state)
    (frame offset length : Word) (cell : Cell frame shape.field)
    (frameKnown : lookup state 7 = some frame) (offsetKnown : lookup state shape.index.register = some offset)
    (lengthRead : Reads state cell.address length) (small : shape.extent.toNat < 2 ^ 31)
    (noWrap : offset.toNat * 2 ^ shape.scale.val + shape.extent.toNat < 2 ^ 64)
    (above : length.toNat < offset.toNat * 2 ^ shape.scale.val + shape.extent.toNat) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 3).run state = .ok () after ∧ RegisterFrame {.r15, .rflags, .rip} state after ∧
      Nonempty (At image after base reject) := by
  obtain ⟨after, run, frameKept, ⟨arrived⟩⟩ := checks other extra vector point shape code controls
    frame offset length cell frameKnown offsetKnown lengthRead small noWrap
  rw [if_pos above] at arrived
  exact ⟨after, run, frameKept, ⟨arrived⟩⟩

end Mettapedia.Machines.TIsa.X86IndexedAddress
