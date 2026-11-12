import Mettapedia.Machines.TIsa.X86RegisterEncoding
import Mettapedia.Machines.TIsa.X86Memory

/-!
# Register MOV obligations in the imported Sail handler

The register case is independent of the external memory primitives. These
lemmas expose the handler's actual width, segment, pointer and register effects.
Fetching and dispatching the instruction remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86Move

open _root_.X86Registers
open X86RegisterRefinement X86RegisterEncoding

theorem operand_size64 (source destination : Fin 16) (prefixes : BitVec 52) :
    Functions.select_operand_size .Mode_64bit false (rex true source destination)
      false prefixes false false false = (pure 8 : SailM Int) := by
  simp [Functions.select_operand_size, Functions.in_64bit_mode, operand_width]

theorem segment64 (register : BitVec 3) (sib : BitVec 8) :
    Functions.select_segment_register .Mode_64bit (0#52) (3#2) register sib = (pure 3 : SailM Nat) := by
  simp [Functions.select_segment_register, Functions.select_address_size, Functions.in_64bit_mode,
    Functions._get_prefixes_seg, Functions._get_prefixes_adr, Functions.eq_bits_nat,
    Sail.BitVec.extractLsb, Sail.BitVec.toNatInt]

theorem bits_of_int49 (pointer : BitVec 48) :
    Functions.bits_of_int pointer.toInt 49 = pointer.signExtend 49 := by
  have widened : BitVec.ofInt 50 pointer.toInt = pointer.signExtend 50 := by
    rw [← BitVec.toInt_signExtend_of_le (x := pointer) (by decide : 48 ≤ 50)]
    simp
  change (BitVec.ofInt 50 pointer.toInt).extractLsb' 0 49 = pointer.signExtend 49
  rw [widened]
  apply BitVec.eq_of_getLsbD_eq
  intro index bound
  have wideBound : index < 50 := by omega
  simp [bound, wideBound, BitVec.getElem_signExtend]

theorem bits_of_int48 (pointer : BitVec 48) :
    Functions.bits_of_int pointer.toInt 48 = pointer := by
  have widened : BitVec.ofInt 49 pointer.toInt = pointer.signExtend 49 := by
    rw [← BitVec.toInt_signExtend_of_le (x := pointer) (by decide : 48 ≤ 49)]
    simp
  change (BitVec.ofInt 49 pointer.toInt).extractLsb' 0 48 = pointer
  rw [widened]
  apply BitVec.eq_of_getLsbD_eq
  intro index bound
  have wideBound : index < 49 := by omega
  simp [bound, wideBound, BitVec.getElem_signExtend]

theorem instruction_length_three (address : Int)
    (lower : -(2 ^ 47 : Int) ≤ address) (upper : address + 3 < (2 ^ 47 : Int)) :
    Functions.check_instruction_length (BitVec.ofInt 48 address)
      (BitVec.ofInt 48 (address + 3)) (0#3) = none := by
  have start : (BitVec.ofInt 48 address).toInt = address :=
    BitVec.toInt_ofInt_eq_self (by decide) lower (by omega)
  have next : (BitVec.ofInt 48 (address + 3)).toInt = address + 3 :=
    BitVec.toInt_ofInt_eq_self (by decide) (by omega) upper
  have startBits : Functions.bits_of_int address 48 = BitVec.ofInt 48 address := by
    simpa only [start] using bits_of_int48 (BitVec.ofInt 48 address)
  have nextBits : Functions.bits_of_int (address + 3) 48 = BitVec.ofInt 48 (address + 3) := by
    simpa only [next] using bits_of_int48 (BitVec.ofInt 48 (address + 3))
  have endBits : (Functions.bits_of_int (address + 3) 49).toInt = address + 3 := by
    have representation := bits_of_int49 (BitVec.ofInt 48 (address + 3))
    rw [next] at representation
    rw [representation, BitVec.toInt_signExtend_of_le (by decide : 48 ≤ 49), next]
  have zero : Functions.bits_of_int 0 3 = (0#3) := by decide
  simpa [Functions.check_instruction_length, Sail.BitVec.toNatInt, start, next,
    startBits, nextBits, zero, endBits] using
    (by decide : (Functions.bits_of_int 3 50).toInt ≤ 15)

theorem canonical48 (state : State) (pointer : BitVec 48) :
    (Functions.canonical_address_p pointer.toInt).run state = .ok true state := by
  have lower : -(2 ^ 47 : Int) ≤ pointer.toInt := by simpa using BitVec.le_toInt pointer
  have upper : pointer.toInt < (2 ^ 47 : Int) := by simpa using (BitVec.toInt_lt (x := pointer))
  unfold Functions.canonical_address_p Functions.signed_byte_p_int
  rw [run_bind, run_assert]
  simp
  exact ⟨lower, upper⟩

theorem widen_truncate (value : Word) :
    Sail.BitVec.truncate (Sail.BitVec.zeroExtend value 128) 64 = value := by
  simp [Sail.BitVec.truncate, Sail.BitVec.zeroExtend]

theorem truncate_pointer49 (pointer : BitVec 48) :
    Sail.BitVec.truncate (pointer.signExtend 49) 48 = pointer := by
  apply BitVec.eq_of_getLsbD_eq
  intro index bound
  have wideBound : index < 49 := by omega
  simp [Sail.BitVec.truncate, bound, wideBound, BitVec.getElem_signExtend]

theorem add_pointer_zero (state : State) (pointer : BitVec 48) :
    (Functions.add_to_iptr .Mode_64bit pointer (0#48)).run state = .ok pointer state := by
  have canonical : (Functions.canonical_address_p (pointer.signExtend 49).toInt).run state =
      .ok true state := by
    simpa only [BitVec.toInt_signExtend_of_le (by decide : 48 ≤ 49)] using canonical48 state pointer
  unfold Functions.add_to_iptr
  simp only [Functions.in_64bit_mode, ite_true]
  rw [run_bind]
  rw [BitVec.toInt_zero, Int.add_zero, bits_of_int49]
  rw [canonical]
  change (pure (Sail.BitVec.truncate (pointer.signExtend 49) 48) : SailM (BitVec 48)).run state = _
  rw [truncate_pointer49]
  rfl

def putPointer (state : State) (pointer : BitVec 48) : State :=
  { state with regs := state.regs.insert .rip (pointer.signExtend 64) }

theorem lookup_putPointer (state : State) (pointer : BitVec 48) (index : Fin 16) :
    lookup (putPointer state pointer) index = lookup state index := by
  have apart : (Register.rip : Register) ≠ key index := by fin_cases index <;> decide
  simp [lookup, putPointer, Std.ExtDHashMap.get?_insert, apart]

theorem write_pointer64 (state : State) (pointer : BitVec 48)
    (quiet : state.regs.get? .log_register_writes = some false) :
    (Functions.write_iptr .Mode_64bit pointer).run state = .ok () (putPointer state pointer) := by
  have quietAfter : (putPointer state pointer).regs.get? .log_register_writes = some false := by
    simpa [putPointer, Std.ExtDHashMap.get?_insert] using quiet
  unfold Functions.write_iptr
  simp only [Functions.in_64bit_mode, ite_true]
  unfold Functions.write_rip
  rw [run_bind, writeRegister_exact]
  change (do
    let diagnostic ← _root_.X86Registers.readReg .log_register_writes
    if diagnostic then Functions.log_rip_write () else pure ()).run (putPointer state pointer) = _
  rw [run_bind, readRegister_exact, quietAfter]
  rfl

theorem read_register64 (state : State) (index : Fin 16) (rexByte : BitVec 8) (value : Word)
    (known : lookup state index = some value) :
    (Functions.rgfi_size (8#4) (BitVec.ofNat 4 index.val) rexByte).run state = .ok value state := by
  have action : Functions.rgfi_size (8#4) (BitVec.ofNat 4 index.val) rexByte =
      Functions.rgfi (Sail.BitVec.toNatInt (BitVec.ofNat 4 index.val)) := rfl
  rw [action]
  have bound : index.val < 2 ^ 4 := index.isLt
  simpa [Sail.BitVec.toNatInt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] using
    rgfi_exact state index value known

theorem write_operand_register64 [MemoryPrimitives] (state : State) (source destination : Fin 16)
    (value : Word) (quiet : state.regs.get? .log_register_writes = some false) :
    (Functions.x86_operand_to_reg_mem .Mode_64bit 8 true false (Sail.BitVec.zeroExtend value 128)
      3 (0#64) (0#52) (rex true source destination) (Functions._get_modr_m_r_m (modRM source destination))
        (3#2) (0#8)).run state =
        .ok () (put state destination value) := by
  unfold Functions.x86_operand_to_reg_mem
  rw [widen_truncate, destination_register]
  have bound : destination.val < 2 ^ 4 := destination.isLt
  simpa [Functions.write_rgfi_size, Functions.eq_bits_nat, Functions.bits_of_int, Sail.get_slice_int,
    Functions.wr64, Sail.BitVec.toNatInt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] using
    write_rgfi_exact state destination value quiet

/-- The imported register MOV handler reads the source, writes the destination,
and advances RIP. It is uniform over the external memory implementation. -/
theorem register64 [MemoryPrimitives] (state : State) (source destination : Fin 16)
    (value : Word) (start next : BitVec 48)
    (known : lookup state source = some value)
    (quiet : state.regs.get? .log_register_writes = some false)
    (length : Functions.check_instruction_length start next (0#3) = none) :
    (Functions.x86_mov_op_en_mr .Mode_64bit start next (0#52) (rex true source destination) (137#8)
      (modRM source destination) (0#8)).run state =
        .ok () (putPointer (put state destination value) next) := by
  have byteOperand : ((137#8) == (136#8)) = false := by decide
  have registerMode : ((3#2) == (3#2)) = true := by decide
  have eightBits : Functions.bits_of_int 8 4 = (8#4) := by decide
  have sizeNat : Int.toNat (8 : Int) = 8 := by decide
  have zeroDelta : Sail.BitVec.zeroExtend (Functions.bits_of_int 0 3) 48 = (0#48) := by decide
  unfold Functions.x86_mov_op_en_mr
  dsimp only
  rw [byteOperand, operand_size64, run_bind, run_pure]
  dsimp only
  rw [source_register, eightBits, run_bind, read_register64 state source _ value known]
  dsimp only
  rw [register_mode, if_pos registerMode, run_bind, run_pure]
  dsimp only
  rw [segment64, run_bind, run_pure]
  dsimp only
  rw [zeroDelta, run_bind, add_pointer_zero]
  dsimp only
  rw [length]
  rw [if_neg (by decide : ¬Functions.is_some (none : Option Int) = true)]
  rw [run_bind, sizeNat, write_operand_register64 state source destination value quiet]
  change (Functions.write_iptr .Mode_64bit next).run (put state destination value) = _
  apply write_pointer64
  simpa only [diagnostic_put] using quiet

theorem register64_three_bytes [MemoryPrimitives] (state : State) (source destination : Fin 16)
    (value : Word) (address : Int)
    (lower : -(2 ^ 47 : Int) ≤ address) (upper : address + 3 < (2 ^ 47 : Int))
    (known : lookup state source = some value)
    (quiet : state.regs.get? .log_register_writes = some false) :
    (Functions.x86_mov_op_en_mr .Mode_64bit (BitVec.ofInt 48 address)
      (BitVec.ofInt 48 (address + 3)) (0#52) (rex true source destination) (137#8)
      (modRM source destination) (0#8)).run state =
        .ok () (putPointer (put state destination value) (BitVec.ofInt 48 (address + 3))) :=
  register64 state source destination value _ _ known quiet (instruction_length_three address lower upper)

namespace Controls

local instance : MemoryPrimitives := X86Memory.ordinary

private def initial : State :=
  ⟨(((∅ : Std.ExtDHashMap Register RegisterType).insert .log_register_writes false).insert .rax 99).insert .r8 7,
    (), ∅, (), 0, #[]⟩

private theorem known : lookup initial 8 = some 7 := by
  have present : initial.regs.get? .r8 = some (7#64) := by simp [initial]
  change (initial.regs.get? .r8).map (fun value : Word => value) = some (7#64)
  rw [present]
  rfl
private theorem quiet : initial.regs.get? .log_register_writes = some false := by
  simp [initial, Std.ExtDHashMap.get?_insert]

private theorem ambient : lookup initial 0 = some 99 := by
  have present : initial.regs.get? .rax = some (99#64) := by
    simp [initial, Std.ExtDHashMap.get?_insert]
  change (initial.regs.get? .rax).map (fun value : Word => value) = some (99#64)
  rw [present]
  rfl

example :
    (Functions.x86_mov_op_en_mr .Mode_64bit (0#48) (3#48) (0#52) (rex true 8 9) (137#8)
      (modRM 8 9) (0#8)).run initial = .ok () (putPointer (put initial 9 7) (3#48)) :=
  register64_three_bytes initial 8 9 7 0 (by decide) (by decide) known quiet

example : ¬∃ after,
    (Functions.x86_mov_op_en_mr .Mode_64bit (0#48) (3#48) (0#52) (rex true 8 9) (137#8)
      (modRM 8 9) (0#8)).run initial = .ok () after ∧ lookup after 9 = some 8 := by
  rintro ⟨after, executed, wrong⟩
  have correct := register64 initial 8 9 7 (0#48) (3#48) known quiet (by decide)
  have same := (EStateM.Result.ok.inj (correct.symm.trans executed)).2
  rw [← same, lookup_putPointer, lookup_put_same] at wrong
  contradiction

theorem altered_rex_refuses_original_answer : ¬∃ after,
    (Functions.x86_mov_op_en_mr .Mode_64bit (0#48) (3#48) (0#52) (rex true 0 9) (137#8)
      (modRM 8 9) (0#8)).run initial = .ok () after ∧ lookup after 9 = some 7 := by
  rintro ⟨after, executed, wrong⟩
  have sameFields : modRM 0 9 = modRM 8 9 := by decide
  have correct := register64 initial 0 9 99 (0#48) (3#48) ambient quiet (by decide)
  rw [sameFields] at correct
  have same := (EStateM.Result.ok.inj (correct.symm.trans executed)).2
  rw [← same, lookup_putPointer, lookup_put_same] at wrong
  contradiction

end Controls

end Mettapedia.Machines.TIsa.X86Move
