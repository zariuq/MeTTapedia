import Mettapedia.Machines.TIsa.X86ControlFlags
import Mettapedia.Machines.TIsa.X86Arithmetic
import Mettapedia.Machines.TIsa.X86LogicalFlags
import Mettapedia.Machines.TIsa.X86FuelPrefix
import Mettapedia.Machines.TIsa.X86DwordLoad

/-!
# Fetched XOR of a register with itself at dword width

The original x86 handler reads both encoded operands at width 32 and zeroes
the full 64-bit destination. The proof retains flag computation and the
model's original undefined auxiliary-flag provider; no zero-width or hidden
64-bit arithmetic replacement is used. The three-byte form includes a REX
prefix, as in the native loop's R10 initialization.

Only the destination, arithmetic flags and RIP may change. Concrete controls
cover arbitrary dirty old counter values, retained bound/stack/memory, and
an altered destination. Whole-loop entry and public ABI are separate joins.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86Zero32
open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

def low (value : Word) : Word := (value.extractLsb' 0 32).zeroExtend 64

theorem read32 (state : State) (index : Fin 16) (rexByte : BitVec 8) (value : Word)
    (known : lookup state index = some value) :
    (Functions.rgfi_size (4#4) (BitVec.ofNat 4 index.val) rexByte).run state = .ok (low value) state := by
  have register : Sail.BitVec.toNatInt (BitVec.ofNat 4 index.val) = index.val := by
    simp [Sail.BitVec.toNatInt]
  have read : (Functions.rr32 (BitVec.ofNat 4 index.val)).run state = .ok (Sail.BitVec.truncate value 32) state := by
    unfold Functions.rr32
    rw [register,run_bind,rgfi_exact state index value known]
    rfl
  unfold Functions.rgfi_size
  simp only [show Functions.eq_bits_nat (4#4) 1 = false from rfl,
    show Functions.eq_bits_nat (4#4) 2 = false from rfl,
    show Functions.eq_bits_nat (4#4) 4 = true from rfl,Bool.false_eq_true,ite_false,ite_true]
  rw [run_bind,read]
  rfl

theorem operand32 (state : State) (destination : Fin 16) (value : Word) (prefixes : BitVec 52) (pointer : BitVec 48)
    (known : lookup state destination = some value) :
    (Functions.x86_operand_from_modr_m_and_sib_bytes .Mode_64bit (0#1) 4 true false 3 prefixes pointer
      (rex false destination destination) (Functions._get_modr_m_r_m (modRM destination destination)) (3#2) (0#8) (0#3)).run state =
        .ok (Sail.BitVec.zeroExtend (low value) 128,(0 : Int),(0#64)) state := by
  unfold Functions.x86_operand_from_modr_m_and_sib_bytes
  simp only [show ((3#2) == (3#2)) = true from rfl,
    show ((0#1) == (0#1)) = true from rfl,ite_true,pure_bind]
  rw [show Functions.bits_of_int ((4 : Nat) : Int) 4 = (4#4) from rfl,destination_register]
  rw [run_bind,run_bind,read32 state destination _ value known]
  rfl

def output (flags : BitVec 32) : BitVec 32 :=
  Functions._update_rflagsbits_of (Functions._update_rflagsbits_sf (Functions._update_rflagsbits_zf
    (Functions._update_rflagsbits_pf (Functions._update_rflagsbits_cf flags (0#1)) (1#1)) (1#1)) (0#1)) (0#1)

theorem parity_zero (state : State) : (Functions.pf_spec32 (0#32)).run state = .ok (1#1) state := by
  unfold Functions.pf_spec32
  have count : Functions.logcount_int 0 = 0 := by rw [Functions.logcount_int.eq_def]; rfl
  change (do
    let bit ← Functions.logbitp_int 0 (Functions.logcount_int 0)
    pure (Functions.bool_to_bits (!bit))).run state = _
  rw [count]
  rfl

theorem xor_self (state : State) (value : Word) (flags : BitVec 32) :
    (Functions.gpr_arith_logic_spec 4 5 value value flags).run state = .ok (0#64,output flags,16#32) state := by
  unfold Functions.gpr_arith_logic_spec Functions.gpr_arith_logic_spec_4 Functions.gpr_xor_spec_4 Functions.logxor
  simp only [BitVec.xor_self]
  change (do
    let pf ← Functions.pf_spec32 (0#32)
    pure (0#64,Functions._update_rflagsbits_of (Functions._update_rflagsbits_sf (Functions._update_rflagsbits_zf
      (Functions._update_rflagsbits_pf (Functions._update_rflagsbits_cf flags (0#1)) pf) (1#1)) (0#1)) (0#1),16#32)).run state = _
  rw [run_bind,parity_zero]
  rfl

theorem write_operand32 (state : State) (destination : Fin 16) (prefixes : BitVec 52)
    (quiet : state.regs.get? .log_register_writes = some false) :
    (Functions.x86_operand_to_reg_mem .Mode_64bit 4 true false (0#128) 3 (0#64) prefixes
      (rex false destination destination) (Functions._get_modr_m_r_m (modRM destination destination))
      (3#2) (0#8)).run state = .ok () (put state destination (0#64)) := by
  unfold Functions.x86_operand_to_reg_mem
  simp only [show ((3#2) == (3#2)) = true from rfl, ite_true]
  rw [destination_register]
  change (Functions.wr32 (BitVec.ofNat 4 destination.val) (0#32)).run state = _
  exact wr32_exact state destination (0#32) quiet

theorem handler (state : State) (destination : Fin 16) (value : Word)
    (start next : BitVec 48) (prefixes : BitVec 52) (flags : BitVec 32)
    (segment : Functions._get_prefixes_seg prefixes = (0#8))
    (addressSize : Functions._get_prefixes_adr prefixes = (0#8))
    (operandSize : Functions._get_prefixes_opr prefixes = (0#8))
    (known : lookup state destination = some value)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false)
    (length : Functions.check_instruction_length start next (0#3) = none) :
    (Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_g 5 .Mode_64bit start next prefixes
      (rex false destination destination) (0x31#8) (modRM destination destination) (0#8)).run state =
        .ok () (X86Move.putPointer (X86Flags.putFlags (put state destination (0#64))
          (X86LogicalFlags.merged flags (output flags) (0#1))) next) := by
  have size : Functions.select_operand_size .Mode_64bit false (rex false destination destination)
      false prefixes false false false = (pure 4 : SailM Int) := by
    have same : X86DwordLoad.loadRex false destination destination = rex false destination destination := by
      fin_cases destination <;> rfl
    simpa only [same] using X86DwordLoad.operand_size32 destination destination prefixes operandSize
  unfold Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_g
  dsimp only
  rw [show ((0#1) == Sail.BitVec.truncate ((0x01#8) &&& (0x31#8)) 1) = false from rfl,
    size,run_bind,run_pure]
  dsimp only
  rw [show Functions.bits_of_int 4 4 = (4#4) from rfl,source_register,run_bind,
    read32 state destination _ value known]
  dsimp only
  rw [register_mode,X86MovePrefix.segment64 prefixes _ _ segment addressSize,run_bind,run_pure]
  dsimp only
  rw [show Int.toNat (4 : Int) = 4 from rfl,run_bind,operand32 state destination value prefixes next known]
  dsimp only
  rw [show Sail.BitVec.zeroExtend (Functions.bits_of_int 0 3) 48 = (0#48) from rfl,
    run_bind,X86Move.add_pointer_zero]
  dsimp only
  rw [length]
  simp only [show Functions.is_some (none : Option Int) = false from rfl,Bool.false_eq_true,ite_false]
  rw [run_bind,readRegister_exact,flagsKnown]
  dsimp only
  rw [X86Move.widen_truncate]
  rw [run_bind,xor_self state (low value) flags]
  dsimp only
  simp only [show ((5 : Nat) == 8 || (5 : Nat) == 7) = false from rfl,Bool.false_eq_true,ite_false]
  rw [show Sail.BitVec.zeroExtend (0#64) 128 = (0#128) from rfl,
    run_bind,write_operand32 state destination prefixes quiet]
  dsimp only
  rw [run_bind,X86LogicalFlags.write_logical_flags _ flags (output flags)
    (by simpa only [put_flags] using flagsKnown) (by simpa only [diagnostic_put] using quiet)]
  change (Functions.write_iptr .Mode_64bit next).run _ = _
  apply X86Move.write_pointer64
  rw [X86Flags.putFlags_other _ _ .log_register_writes (by decide),diagnostic_put]
  exact quiet

theorem fetched (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (destination : Fin 16) (value : Word) (flags : BitVec 32)
    (site : X86LegacyFetch.Window state (0x31#8) false destination destination)
    (known : lookup state destination = some value)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    Step state (X86Move.putPointer (X86Flags.putFlags (put state destination (0#64))
      (X86LogicalFlags.merged flags (output flags) (0#1))) site.next) := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  unfold Step
  rw [X86LegacyFetch.Window.dispatches (0x31#8) ((X86LegacyFetch.checkOpcode_iff _).mp (by decide))
    false state destination destination site,X86OpcodeDispatch.xor_register_guarded]
  have ordinary : Functions._get_prefixes_lck (X86LegacyFetch.packet (0x31#8)) = (0#8) := by decide
  rw [ordinary]
  simp only [show ((0xf0#8) == (0#8)) = false from rfl,Bool.and_false,Bool.false_eq_true,ite_false]
  apply handler state destination value site.address site.next (X86LegacyFetch.packet (0x31#8)) flags
    (by decide) (by decide) (by decide) known flagsKnown quiet
  exact X86InstructionFetch.length_from_geometry _ _ (by have := site.step2; have := site.step3; omega)

def code (destination : Fin 16) : List Nat :=
  [(rex false destination destination).toNat,0x31,(modRM destination destination).toNat]

def writes (destination : Fin 16) : Finset Register := {key destination,.rflags,.rip}

theorem writes_data (destination : Fin 16) : writes destination ⊆ dataRegisters := by
  intro register member
  simp only [writes,Finset.mem_insert,Finset.mem_singleton] at member
  rcases member with rfl | rfl | rfl
  · exact data_key destination
  · decide
  · decide

theorem result_frame (state : State) (destination : Fin 16) (flags : BitVec 32) (next : BitVec 48) :
    RegisterFrame (writes destination) state (X86Move.putPointer (X86Flags.putFlags (put state destination (0#64)) flags) next) :=
  (((put_frame state destination (0#64)).trans (flags_frame _ flags)).trans (pointer_frame _ next)).mono (by simp [writes])

structure Inputs (state : State) (destination : Fin 16) extends X86LegacyFetch.Basis state where
  value : Word
  flags : BitVec 32
  valueKnown : lookup state destination = some value
  flagsKnown : state.regs.get? .rflags = some flags
  quiet : state.regs.get? .log_register_writes = some false
  upper : address.toInt + 3 < (2 ^ 47 : Int)
  loaded : codeLoaded state address.toInt (code destination)

theorem executes_control (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (destination : Fin 16) (input : Inputs state destination) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 1).run state = .ok () after ∧
      RegisterFrame (writes destination) state after ∧ lookup after destination = some (0#64) ∧
      after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some ((address input.address.toInt 3).signExtend 64) ∧
      X86ControlFlags.Preserved state after := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  let origin := rebase state state input.toBasis (RegisterFrame.refl dataRegisters state)
    input.upper 0 (by decide) (by simpa [address] using input.rip)
  let site : X86LegacyFetch.Window state (0x31#8) false destination destination :=
    { toBasis := origin
      prefixByte := by
        simpa only [origin,rebase,BitVec.ofNat_toNat,BitVec.setWidth_eq] using
          input.loaded 0 (rex false destination destination).toNat (by rfl)
      opcodeByte := by exact input.loaded 1 0x31 (by rfl)
      modrmByte := by
        simpa only [origin,rebase,BitVec.ofNat_toNat,BitVec.setWidth_eq] using
          input.loaded 2 (modRM destination destination).toNat (by rfl) }
  have run := fetched other vector state destination input.value input.flags site input.valueKnown input.flagsKnown input.quiet
  let flags := X86LogicalFlags.merged input.flags (output input.flags) (0#1)
  let after := X86Move.putPointer (X86Flags.putFlags (put state destination (0#64)) flags) site.next
  refine ⟨after,flags,X86FuelPrefix.fetches_one state after run,result_frame _ _ _ _,?_,?_,?_,?_⟩
  · rw [X86Move.lookup_putPointer,X86Flags.putFlags_gpr,lookup_put_same]
  · rw [(pointer_frame _ site.next).registers .rflags (by decide)]
    simp only [X86Flags.putFlags,Std.ExtDHashMap.get?_insert_self]
  · simp only [after,X86Move.putPointer,Std.ExtDHashMap.get?_insert_self]
    rfl
  · unfold X86ControlFlags.Preserved
    have seen : after.regs.get? .rflags = some flags := by
      rw [(pointer_frame _ site.next).registers .rflags (by decide)]
      simp only [X86Flags.putFlags,Std.ExtDHashMap.get?_insert_self]
    rw [seen,input.flagsKnown]
    simp only [Option.map_some,flags,X86ControlFlags.logical_mask]


theorem executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (destination : Fin 16) (input : Inputs state destination) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 1).run state = .ok () after ∧
      RegisterFrame (writes destination) state after ∧ lookup after destination = some (0#64) ∧
      after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some ((address input.address.toInt 3).signExtend 64) := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,flags,run,frame,value,read,rip,_control⟩ := executes_control other vector state destination input
  exact ⟨after,flags,run,frame,value,read,rip⟩


namespace Controls
private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def cells : List (Nat × BitVec 8) :=
  [(4096,0x45#8),(4097,0x31#8),(4098,0xd2#8),(8192,42#8)]
private def before (old : Word) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (4096#64)
  let registers := registers.insert .r10 old
  let registers := registers.insert .r9 (10#64)
  let registers := registers.insert .rsp (8192#64)
  let registers := registers.insert .rflags (0x246#32)
  let registers := registers.insert .log_register_writes false
  ⟨registers,(),Std.ExtHashMap.ofList cells,(),0,#[]⟩

private theorem cell (old : Word) (key : Nat) (byte : BitVec 8) (present : (key,byte) ∈ cells) :
    (before old).mem.get? key = some byte :=
  Std.ExtHashMap.getElem?_ofList_of_mem (by simp) (by decide) present

private def input (old : Word) : Inputs (before old) 10 where
  address := 4096#48
  opcodeAddress := 4097#48
  modrmAddress := 4098#48
  next := 4099#48
  control := modeControl
  attributes := attributes
  step1 := by decide
  step2 := by decide
  step3 := by decide
  status := by simp [before,Std.ExtDHashMap.get?_insert]
  fault := by simp [before,Std.ExtDHashMap.get?_insert]
  msrs := by simp [before,Std.ExtDHashMap.get?_insert]
  segments := by simp [before,Std.ExtDHashMap.get?_insert]
  longMode := by decide
  codeMode := by decide
  application := by simp [before,Std.ExtDHashMap.get?_insert]
  rip := by simp [before,Std.ExtDHashMap.get?_insert]
  value := old
  flags := 0x246#32
  valueKnown := by simp [lookup,before,key,Std.ExtDHashMap.get?_insert]; rfl
  flagsKnown := by simp [before,Std.ExtDHashMap.get?_insert]
  quiet := by simp [before]
  upper := by decide
  loaded := by
    intro index byte present
    have within : index < 3 := (List.getElem?_eq_some_iff.mp present).1
    interval_cases index
    · have same : byte = 0x45 := by simpa [code,rex] using present.symm
      subst byte
      exact cell old 4096 (0x45#8) (by decide)
    · have same : byte = 0x31 := by simpa [code] using present.symm
      subst byte
      exact cell old 4097 (0x31#8) (by decide)
    · have same : byte = 0xd2 := by simpa [code,modRM] using present.symm
      subst byte
      exact cell old 4098 (0xd2#8) (by decide)

theorem resets_counter (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) (old : Word) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 1).run (before old) = .ok () after ∧
      RegisterFrame (writes 10) (before old) after ∧ lookup after 10 = some (0#64) ∧
      after.regs.get? .rflags = some flags ∧ after.regs.get? .rip = some (4099#64) ∧
      lookup after 9 = some (10#64) ∧ lookup after 4 = some (8192#64) ∧ after.mem = (before old).mem := by
  obtain ⟨after,flags,run,frame,result,flagsKnown,rip⟩ := executes other vector (before old) 10 (input old)
  refine ⟨after,flags,run,frame,result,flagsKnown,rip,?_,?_,frame.memory⟩
  · rw [(X86StateFrame.registerOnly frame).lookup 9 (by decide)]
    simp [lookup,before,key,Std.ExtDHashMap.get?_insert]
    rfl
  · rw [(X86StateFrame.registerOnly frame).lookup 4 (by decide)]
    simp [lookup,before,key,Std.ExtDHashMap.get?_insert]
    rfl

theorem changed_register_rejected (old : Word) : ¬codeLoaded (before old) 4096 (code 11) := by
  intro loaded
  have changed := loaded 2 0xdb (by decide)
  have actual := cell old 4098 (0xd2#8) (by decide)
  change (before old).mem.get? 4098 = some (0xdb#8) at changed
  rw [actual] at changed
  contradiction

end Controls

end Mettapedia.Machines.TIsa.X86Zero32
