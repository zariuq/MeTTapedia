import Mettapedia.Machines.TIsa.X86PlacedFrameAddress

/-! # Placed scale-one indexed addresses

A zero-displacement SIB address adds the two operand words and touches
no data memory. The base and index encodings that mean "absent" are
excluded. Capability and initialization facts belong to the consuming
load or store.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Mettapedia.Machines.TIsa.X86PlacedIndexedAddress

open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution
open X86PlacedInstruction (At)
open X86PlacedScalar (Code)
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev Base := { reg : Fin 8 // reg.val ≠ 5 }
abbrev Index := X86PreparedLea.Index

def physical (reg : Fin 8) : Fin 16 := ⟨reg.val, by have := reg.isLt; omega⟩

def modrm (destination : Fin 8) : BitVec 8 := .ofNat 8 (8 * destination.val + 4)

def sib (base : Base) (index : Index) : BitVec 8 := .ofNat 8 (8 * index.val.val + base.val.val)

def bytes (destination : Fin 8) (base : Base) (index : Index) : List Nat :=
  [0x48, 0x8d, (modrm destination).toNat, (sib base index).toNat]

private theorem ModRM.fields (destination : Fin 8) :
    Functions._get_modr_m_mod (modrm destination) = (0#2) ∧
      Functions._get_modr_m_r_m (modrm destination) = (4#3) ∧
      Functions.reg_index (Functions._get_modr_m_reg (modrm destination)) (0x48#8) (2#2) =
        .ofNat 4 destination.val ∧
      Functions.x86_decode_sib_p (modrm destination) false = true := by
  revert destination
  decide +kernel

private theorem SIB.fields (base : Base) (index : Index) :
    (Functions._get_sib_base (sib base index) == (5#3)) = false ∧
      Sail.BitVec.toNatInt (Functions.reg_index (Functions._get_sib_base (sib base index)) (0x48#8) (0#2)) =
        (base.val.val : Int) ∧
      Functions.eq_bits_nat (Functions.reg_index (Functions._get_sib_index (sib base index)) (0x48#8) (1#2)) 4 =
        false ∧
      Sail.BitVec.toNatInt (Functions.reg_index (Functions._get_sib_index (sib base index)) (0x48#8) (1#2)) =
        (index.val.val : Int) ∧
      Sail.BitVec.toNatInt (Functions._get_sib_scale (sib base index)) = 0 := by
  have all : ∀ b i : Fin 8, ∀ hb : b.val ≠ 5, ∀ hi : i.val ≠ 4,
      let byte := sib ⟨b, hb⟩ ⟨i, hi⟩
      (Functions._get_sib_base byte == (5#3)) = false ∧
        Sail.BitVec.toNatInt (Functions.reg_index (Functions._get_sib_base byte) (0x48#8) (0#2)) = (b.val : Int) ∧
        Functions.eq_bits_nat (Functions.reg_index (Functions._get_sib_index byte) (0x48#8) (1#2)) 4 = false ∧
        Sail.BitVec.toNatInt (Functions.reg_index (Functions._get_sib_index byte) (0x48#8) (1#2)) = (i.val : Int) ∧
        Sail.BitVec.toNatInt (Functions._get_sib_scale byte) = 0 := by decide +kernel
  exact all base.val index.val base.property index.property

private theorem rex_low (destination base : Fin 8) : rex true (physical destination) (physical base) = 0x48#8 := by
  have left : destination.val / 8 = 0 := Nat.div_eq_of_lt destination.isLt
  have right : base.val / 8 = 0 := Nat.div_eq_of_lt base.isLt
  simp [rex, physical, left, right]

private theorem data_rex_low (destination base : Fin 8) :
    X86DwordLoad.loadRex true (physical destination) (physical base) = 0x48#8 :=
  rex_low destination base

private theorem effective (before : State) (pointer : BitVec 48) (prefixes : BitVec 52)
    (addressMode : Functions._get_prefixes_adr prefixes = (0#8))
    (base : Base) (index : Index) (left right : Word)
    (baseRead : lookup before (physical base.val) = some left)
    (indexRead : lookup before (physical index.val) = some right) :
    (Functions.x86_effective_addr .Mode_64bit prefixes pointer (0x48#8) (4#3) (0#2)
      (sib base index) (0#3)).run before = .ok (left + right, (0 : Int)) before := by
  have ⟨present, baseNumber, indexPresent, indexNumber, scale⟩ := SIB.fields base index
  unfold Functions.x86_effective_addr
  rw [addressMode]
  simp only [show Functions.select_address_size .Mode_64bit (some prefixes) = (pure 8 : SailM Int) by
    simp [Functions.select_address_size, Functions.in_64bit_mode, addressMode],
    pure_bind, show ((2 : Int) == 8) = false from rfl, Bool.false_eq_true, ite_false]
  unfold Functions.x86_effective_addr_32_64 Functions.x86_effective_addr_from_sib
  simp only [show Functions.eq_bits_nat (0#2) 0 = true from rfl, ite_true, present, Bool.false_eq_true,
    ite_false, show Functions.eq_bits_nat (4#3) 4 = true from rfl, Functions.in_64bit_mode, bind_assoc,
    pure_bind, baseNumber, indexPresent, indexNumber, scale, run_bind]
  rw [show (Functions.rgfi (base.val.val : Int)).run before = .ok left before from
    rgfi_exact before (physical base.val) left baseRead]
  dsimp only
  rw [show (Functions.rgfi (index.val.val : Int)).run before = .ok right before from
    rgfi_exact before (physical index.val) right indexRead]
  dsimp only
  rw [if_neg (by decide : ¬ ((103#8) == (0#8)) = true)]
  have scaled : Functions.ash_left_int right.toInt (Int.toNat 0) = right.toInt := by
    change right.toInt * (1 : Int) = right.toInt
    exact Int.mul_one _
  simp only [scaled, BitVec.toInt_zero, add_zero, X86Alu.bits_of_int_eq, BitVec.ofInt_add,
    BitVec.ofInt_toInt, run_pure]

private theorem handler (before : State) (start next : BitVec 48) (prefixes : BitVec 52)
    (addressMode : Functions._get_prefixes_adr prefixes = (0#8))
    (base : Base) (index : Index) (destination : Fin 8) (left right : Word)
    (baseRead : lookup before (physical base.val) = some left)
    (indexRead : lookup before (physical index.val) = some right)
    (quiet : before.regs.get? .log_register_writes = some false)
    (length : Functions.check_instruction_length start next (0#3) = none) :
    (Functions.x86_lea .Mode_64bit start next prefixes (0x48#8) (0x8d#8) (modrm destination) (sib base index)).run
      before = .ok () (X86Move.putPointer (put before (physical destination) (left + right)) next) := by
  have ⟨mode, rm, dst, _⟩ := ModRM.fields destination
  unfold Functions.x86_lea
  rw [← rex_low destination base.val, X86Move.operand_size64, rex_low]
  simp only [pure_bind, show Functions.check_range 2 8 8 = (pure 8 : SailM Int) from rfl, mode, rm, run_bind,
    effective before next prefixes addressMode base index left right baseRead indexRead]
  have zeroStep : (Functions.add_to_iptr .Mode_64bit next (0#48)).run before = .ok next before :=
    X86PrefixRead.add_pointer_checked before next (0#48) next (by simp)
  rw [show Sail.BitVec.zeroExtend (Functions.bits_of_int 0 3) 48 = (0#48) from rfl, zeroStep]
  dsimp only
  rw [length, if_neg (by decide : ¬ Functions.is_some (none : Option Int) = true)]
  have roundtrip : Functions.sail_mask 64 (Functions.trunc_signed (Int.toNat 8) (left + right)) = left + right := by
    unfold Functions.trunc_signed Functions.sail_mask Functions.sail_mask_signed
    simp [Sail.BitVec.truncate]
  rw [show Functions.bits_of_int 8 4 = (8#4) from rfl, dst, roundtrip, run_bind]
  rw [← data_rex_low destination base.val]
  have write := X86QwordLoad.write_destination64 before (physical destination) (physical base.val) (left + right) quiet
  change (Functions.write_rgfi_size (8#4) (BitVec.ofNat 4 destination.val) (left + right)
    (X86DwordLoad.loadRex true (physical destination) (physical base.val))).run before =
      .ok () (put before (physical destination) (left + right)) at write
  rw [write]
  apply X86Move.write_pointer64
  simpa only [diagnostic_put] using quiet

theorem forms (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {before : State} {codeBase : BitVec 48} {start : Nat}
    (point : At image before codeBase start) (inside : start + 4 ≤ image.size)
    (base : Base) (index : Index) (destination : Fin 8) (left right : Word)
    (baseRead : lookup before (physical base.val) = some left)
    (indexRead : lookup before (physical index.val) = some right)
    (code : Code image start (bytes destination base index)) :
    letI : OtherOpcodeHandlers := X86PreparedLea.linked other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run before = .ok () after ∧
      RegisterFrame {key (physical destination), .rip} before after ∧
      lookup after (physical destination) = some (left + right) ∧
      Nonempty (At image after codeBase (start + 4)) := by
  let : OtherOpcodeHandlers := X86PreparedLea.linked other
  let : VectorOpcodeHandlers := vector
  let origin := point.basis (by omega)
  let next := address codeBase.toInt (start + 4)
  have nextExact : origin.next.toInt + 1 = next.toInt := by
    change (address codeBase.toInt (start + 3)).toInt + 1 = (address codeBase.toInt (start + 4)).toInt
    rw [point.location _ (by omega), point.location _ inside]
    omega
  have byte (i value : Nat) (encoded : (bytes destination base index)[i]? = some value) :
      before.mem.get? ((address (address codeBase.toInt start).toInt i).signExtend 52).toNat =
        some (.ofNat 8 value) := point.bytes _ (by omega) _ code i value encoded
  have rexByte : before.mem.get? (origin.address.signExtend 52).toNat =
      some (rex true (physical destination) (physical base.val)) := by
    rw [rex_low]
    rw [show origin.address = address codeBase.toInt start from rfl,
      ← Nat.add_zero start, ← point.relative_address start 0 (by omega)]
    exact byte 0 0x48 rfl
  have opcodeByte : before.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0x8d#8) := by
    rw [show origin.opcodeAddress = address codeBase.toInt (start + 1) from rfl, ← point.relative_address start 1 (by omega)]
    exact byte 1 0x8d rfl
  have modrmByte : before.mem.get? (origin.modrmAddress.signExtend 52).toNat = some (modrm destination) := by
    rw [show origin.modrmAddress = address codeBase.toInt (start + 2) from rfl, ← point.relative_address start 2 (by omega)]
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using byte 2 (modrm destination).toNat rfl
  have sibByte : before.mem.get? (origin.next.signExtend 52).toNat = some (sib base index) := by
    rw [show origin.next = address codeBase.toInt (start + 3) from rfl, ← point.relative_address start 3 (by omega)]
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using byte 3 (sib base index).toNat rfl
  have shape : X86LegacyFetch.RegularOpcode 0x8d := (X86LegacyFetch.checkOpcode_iff _).mp (by decide)
  have length : Functions.check_instruction_length origin.address next (0#3) = none := by
    apply X86FrameLoad.length_from_distance _ _ 4 (by decide)
    have := origin.step1
    have := origin.step2
    have := origin.step3
    omega
  let after := X86Move.putPointer (put before (physical destination) (left + right)) next
  have dispatch : Functions.one_byte_opcode_execute .Mode_64bit origin.address next (X86LegacyFetch.packet 0x8d)
      (0x48#8) 0x8d (modrm destination) (sib base index) =
      Functions.x86_lea .Mode_64bit origin.address next (X86LegacyFetch.packet 0x8d) (0x48#8) 0x8d (modrm destination)
        (sib base index) := by
    fin_cases destination <;> rfl
  have executed : (Functions.x86_fetch_decode_execute ()).run before = .ok () after := by
    rw [X86SibStore.fetch_to_dispatch_sib 0x8d shape true before origin next
      (physical destination) (physical base.val) (modrm destination) (sib base index) (ModRM.fields destination).2.2.2
      nextExact rexByte opcodeByte modrmByte sibByte, rex_low, dispatch]
    exact handler before origin.address next _ (X86LegacyFetch.packet_address _) base index destination
      left right baseRead indexRead point.quiet length
  have frame : RegisterFrame {key (physical destination), .rip} before after :=
    ((put_frame _ _ _).trans (pointer_frame _ _)).mono (by simp)
  have fixed : ∀ reg : Fin 16, Register.rflags ∉ ({key reg, .rip} : Finset Register) := by decide
  have writes : ({key (physical destination), .rip} : Finset Register) ⊆ dataRegisters := by
    intro register member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact data_key _
    · decide
  exact ⟨after, X86FuelPrefix.fetches_one _ _ executed, frame, by
    change lookup (X86Move.putPointer _ _) _ = _
    rw [X86Move.lookup_putPointer, lookup_put_same], ⟨point.advance frame writes
    (X86FuelPrefix.pointer_rip _ _) point.flags ((frame.registers .rflags (fixed _)).trans point.knownFlags)⟩⟩

end Mettapedia.Machines.TIsa.X86PlacedIndexedAddress
