import Mettapedia.Machines.TIsa.X86Move

/-!
# Register MOV with scanner-carried prefix metadata

The register case allows the opcode and prefix-count fields produced by
the scanner. Segment and address overrides have explicit preconditions;
the REX.W width, register effects and instruction-length check use the
imported Sail handler. External memory implementations remain arbitrary.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86MovePrefix

open _root_.X86Registers X86Move X86RegisterRefinement X86RegisterEncoding

theorem segment64 (prefixes : BitVec 52) (register : BitVec 3) (sib : BitVec 8)
    (segment : Functions._get_prefixes_seg prefixes = (0#8))
    (addressSize : Functions._get_prefixes_adr prefixes = (0#8)) :
    Functions.select_segment_register .Mode_64bit prefixes (3#2) register sib =
      (pure 3 : SailM Nat) := by
  simp [Functions.select_segment_register, Functions.select_address_size,
    Functions.in_64bit_mode, segment, addressSize, Functions.eq_bits_nat,
    Sail.BitVec.toNatInt]

theorem write_operand_register64 [MemoryPrimitives] (state : State) (source destination : Fin 16)
    (value : Word) (prefixes : BitVec 52)
    (quiet : state.regs.get? .log_register_writes = some false) :
    (Functions.x86_operand_to_reg_mem .Mode_64bit 8 true false (Sail.BitVec.zeroExtend value 128)
      3 (0#64) prefixes (rex true source destination) (Functions._get_modr_m_r_m (modRM source destination))
        (3#2) (0#8)).run state = .ok () (put state destination value) := by
  unfold Functions.x86_operand_to_reg_mem
  rw [widen_truncate, destination_register]
  have bound : destination.val < 2 ^ 4 := destination.isLt
  simpa [Functions.write_rgfi_size, Functions.eq_bits_nat, Functions.bits_of_int, Sail.get_slice_int,
    Functions.wr64, Sail.BitVec.toNatInt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] using
    write_rgfi_exact state destination value quiet

theorem register64 [MemoryPrimitives] (state : State) (source destination : Fin 16)
    (value : Word) (start next : BitVec 48) (prefixes : BitVec 52)
    (segment : Functions._get_prefixes_seg prefixes = (0#8))
    (addressSize : Functions._get_prefixes_adr prefixes = (0#8))
    (known : lookup state source = some value)
    (quiet : state.regs.get? .log_register_writes = some false)
    (length : Functions.check_instruction_length start next (0#3) = none) :
    (Functions.x86_mov_op_en_mr .Mode_64bit start next prefixes (rex true source destination) (137#8)
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
  rw [segment64 prefixes _ _ segment addressSize, run_bind, run_pure]
  dsimp only
  rw [zeroDelta, run_bind, add_pointer_zero]
  dsimp only
  rw [length]
  rw [if_neg (by decide : ¬Functions.is_some (none : Option Int) = true)]
  rw [run_bind, sizeNat, write_operand_register64 state source destination value prefixes quiet]
  change (Functions.write_iptr .Mode_64bit next).run (put state destination value) = _
  apply write_pointer64
  simpa only [diagnostic_put] using quiet


end Mettapedia.Machines.TIsa.X86MovePrefix
