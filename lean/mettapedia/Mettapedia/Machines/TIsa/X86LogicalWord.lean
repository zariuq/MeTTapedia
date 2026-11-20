import Mettapedia.Machines.TIsa.X86LogicalFlags
import Mettapedia.Machines.TIsa.X86Execution
import Mettapedia.Machines.TIsa.X86FuelPrefix

/-!
# Fetched U64 register logic with byte and frame contracts

OR, AND and XOR use the original arithmetic calculation, prefix scanner,
opcode decoder and register handler. Loaded REX/opcode/ModRM bytes determine
the operation and operands. Both register operands may alias. Only the
destination, arithmetic flags and RIP change; memory is preserved.

The original model chooses an auxiliary flag for the undefined AF bit.
Defined-bit observation uses X86LogicalFlags; no hardware value for AF is
asserted. Logical-register admission, component composition and public ABI
are separate contracts.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86LogicalWord
open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

inductive Kind where | or | and | xor deriving DecidableEq
def number : Kind → Nat | .or => 1 | .and => 3 | .xor => 5
def opcode : Kind → BitVec 8 | .or => 0x09 | .and => 0x21 | .xor => 0x31
def result : Kind → Word → Word → Word
  | .or,left,right => left ||| right
  | .and,left,right => left &&& right
  | .xor,left,right => left ^^^ right
def action : Kind → Word → Word → BitVec 32 → SailM (Word × BitVec 32 × BitVec 32)
  | .or,left,right,flags => Functions.gpr_or_spec_8 left right flags
  | .and,left,right,flags => Functions.gpr_and_spec_8 left right flags
  | .xor,left,right,flags => Functions.gpr_xor_spec_8 left right flags

theorem projected (operation : Kind) (state : State) (left right : Word) (flags : BitVec 32) :
    ((fun output : Word × BitVec 32 × BitVec 32 => output.1) <$> action operation left right flags).run state =
      .ok (result operation left right) state := by
  cases operation with
  | or => exact X86Alu.or_value state left right flags
  | and => exact X86Alu.and_value state left right flags
  | xor => exact X86Alu.xor_value state left right flags

theorem undefined_mask (operation : Kind) (state : State) (left right : Word) (flags : BitVec 32) :
    ((fun output : Word × BitVec 32 × BitVec 32 => output.2.2) <$> action operation left right flags).run state =
      .ok (16#32) state := by
  cases operation
  all_goals
    dsimp only [action,Functions.gpr_or_spec_8,Functions.gpr_and_spec_8,Functions.gpr_xor_spec_8,
      Functions.pf_spec64,Functions.logbitp_int]
    simp only [map_eq_pure_bind,run_bind,run_pure,run_assert]
    rfl

theorem calculate (operation : Kind) (state : State) (left right : Word) (flags : BitVec 32) :
    ∃ output, (Functions.gpr_arith_logic_spec 8 (number operation) left right flags).run state =
      .ok (result operation left right,output,16#32) state := by
  have selected : Functions.gpr_arith_logic_spec 8 (number operation) left right flags = action operation left right flags := by
    cases operation <;> rfl
  rw [selected]
  obtain ⟨output,undefined,executed⟩ := X86Alu.project_result_reflects _ state state _ (projected operation state left right flags)
  have mask := undefined_mask operation state left right flags
  simp only [map_eq_pure_bind,run_bind,executed,run_pure] at mask
  have actual := (EStateM.Result.ok.inj mask).1
  change undefined = (16#32) at actual
  subst undefined
  exact ⟨output,executed⟩

theorem handler (operation : Kind) (state : State) (source destination : Fin 16) (left right : Word)
    (start next : BitVec 48) (prefixes : BitVec 52) (flags : BitVec 32)
    (segment : Functions._get_prefixes_seg prefixes = (0#8))
    (addressSize : Functions._get_prefixes_adr prefixes = (0#8))
    (sourceKnown : lookup state source = some right) (destinationKnown : lookup state destination = some left)
    (flagsKnown : state.regs.get? .rflags = some flags) (quiet : state.regs.get? .log_register_writes = some false)
    (length : Functions.check_instruction_length start next (0#3) = none) :
    ∃ output, (Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_g (number operation) .Mode_64bit start next prefixes
      (rex true source destination) (opcode operation) (modRM source destination) (0#8)).run state =
        .ok () (X86Move.putPointer (X86Flags.putFlags (put state destination (result operation left right))
          (X86LogicalFlags.merged flags output (0#1))) next) := by
  obtain ⟨output,calculated⟩ := calculate operation state left right flags
  refine ⟨output,?_⟩
  have byteOperand : ((0#1) == Sail.BitVec.truncate ((0x01#8) &&& opcode operation) 1) = false := by cases operation <;> decide
  have compare : ((number operation == 8) || (number operation == 7)) = false := by cases operation <;> decide
  unfold Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_g
  dsimp only
  rw [byteOperand,X86Move.operand_size64,run_bind,run_pure]
  dsimp only
  rw [show Functions.bits_of_int 8 4 = (8#4) from rfl,source_register,run_bind,
    X86Move.read_register64 state source _ right sourceKnown]
  dsimp only
  rw [register_mode,X86MovePrefix.segment64 prefixes _ _ segment addressSize,run_bind,run_pure]
  dsimp only
  rw [show Int.toNat (8 : Int) = 8 from rfl,run_bind,
    X86Arithmetic.operand_register64 state source destination left prefixes next destinationKnown]
  dsimp only
  rw [show Sail.BitVec.zeroExtend (Functions.bits_of_int 0 3) 48 = (0#48) from rfl,
    run_bind,X86Move.add_pointer_zero]
  dsimp only
  rw [length]
  simp only [show Functions.is_some (none : Option Int) = false from rfl,Bool.false_eq_true,ite_false]
  rw [run_bind,readRegister_exact,flagsKnown]
  dsimp only
  rw [X86Move.widen_truncate,run_bind,calculated]
  dsimp only
  rw [compare]
  simp only [Bool.false_eq_true,ite_false]
  rw [run_bind,X86MovePrefix.write_operand_register64 state source destination (result operation left right) prefixes quiet]
  dsimp only
  rw [run_bind,X86LogicalFlags.write_logical_flags _ flags output
    (by simpa only [put_flags] using flagsKnown) (by simpa only [diagnostic_put] using quiet)]
  change (Functions.write_iptr .Mode_64bit next).run _ = _
  apply X86Move.write_pointer64
  rw [X86Flags.putFlags_other _ _ .log_register_writes (by decide),diagnostic_put]
  exact quiet

theorem opcode_regular (operation : Kind) : X86LegacyFetch.RegularOpcode (opcode operation) := by
  apply (X86LegacyFetch.checkOpcode_iff _).mp
  cases operation <;> decide

theorem guarded_dispatch [OtherOpcodeHandlers] (operation : Kind) (mode : proc_mode)
    (start next : BitVec 48) (prefixes : BitVec 52) (rexByte modrm sib : BitVec 8) :
    Functions.one_byte_opcode_execute mode start next prefixes rexByte (opcode operation) modrm sib =
      (do
        if ((Functions._get_modr_m_mod modrm == (3#2)) && ((0xf0#8) == Functions._get_prefixes_lck prefixes)) then
          Functions.x86_fault "(:UD)" else pure ()
        OtherOpcodeHandlers.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_g (number operation) mode start next prefixes
          rexByte (opcode operation) modrm sib) := by
  cases operation <;> rfl

theorem dispatch_linked (other : OtherOpcodeHandlers) (operation : Kind) (mode : proc_mode)
    (start next : BitVec 48) (rexByte modrm sib : BitVec 8) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    Functions.one_byte_opcode_execute mode start next (X86LegacyFetch.packet (opcode operation))
      rexByte (opcode operation) modrm sib =
      Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_g (number operation) mode start next
        (X86LegacyFetch.packet (opcode operation)) rexByte (opcode operation) modrm sib := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  rw [guarded_dispatch operation]
  simp only [X86LegacyFetch.packet_lock,show ((0xf0#8) == (0#8)) = false from rfl,
    Bool.and_false,Bool.false_eq_true,ite_false]
  rfl

theorem fetched (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) (operation : Kind)
    (state : State) (source destination : Fin 16)
    (window : X86LegacyFetch.Window state (opcode operation) true source destination)
    (left right : Word) (flags : BitVec 32)
    (sourceKnown : lookup state source = some right) (destinationKnown : lookup state destination = some left)
    (flagsKnown : state.regs.get? .rflags = some flags) (quiet : state.regs.get? .log_register_writes = some false) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ output, (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer (X86Flags.putFlags (put state destination (result operation left right))
        (X86LogicalFlags.merged flags output (0#1))) window.next) := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  rw [X86LegacyFetch.Window.dispatches (opcode operation) (opcode_regular operation) true state source destination window]
  rw [dispatch_linked other operation]
  apply handler operation state source destination left right window.address window.next (X86LegacyFetch.packet (opcode operation)) flags
    (by cases operation <;> decide) (X86LegacyFetch.packet_address _) sourceKnown destinationKnown flagsKnown quiet
  exact X86InstructionFetch.length_from_geometry _ _ (by have := window.step2; have := window.step3; omega)

theorem result_frame (operation : Kind) (state : State) (destination : Fin 16) (left right : Word)
    (flags output : BitVec 32) (next : BitVec 48) :
    RegisterFrame {key destination,.rflags,.rip} state
      (X86Move.putPointer (X86Flags.putFlags (put state destination (result operation left right))
        (X86LogicalFlags.merged flags output (0#1))) next) :=
  (((put_frame state destination _).trans (flags_frame _ _)).trans (pointer_frame _ _)).mono (by simp)

def code (operation : Kind) (source destination : Fin 16) : List Nat :=
  [(rex true source destination).toNat,(opcode operation).toNat,(modRM source destination).toNat]

theorem code_length (operation : Kind) (source destination : Fin 16) :
    (code operation source destination).length = 3 := rfl

def writes (destination : Fin 16) : Finset Register := {key destination,.rflags,.rip}

theorem writes_data (destination : Fin 16) : writes destination ⊆ dataRegisters := by
  intro register member
  simp only [writes,Finset.mem_insert,Finset.mem_singleton] at member
  rcases member with rfl | rfl | rfl
  · exact data_key destination
  · decide
  · decide

structure Inputs (state : State) (operation : Kind) (source destination : Fin 16)
    extends X86LegacyFetch.Basis state where
  left : Word
  right : Word
  flags : BitVec 32
  sourceKnown : lookup state source = some right
  destinationKnown : lookup state destination = some left
  flagsKnown : state.regs.get? .rflags = some flags
  quiet : state.regs.get? .log_register_writes = some false
  upper : address.toInt + 3 < (2 ^ 47 : Int)
  loaded : codeLoaded state address.toInt (code operation source destination)

theorem executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (operation : Kind) (state : State) (source destination : Fin 16)
    (input : Inputs state operation source destination) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 1).run state = .ok () after ∧
      RegisterFrame (writes destination) state after ∧
      lookup after destination = some (result operation input.left input.right) ∧
      after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some ((address input.address.toInt 3).signExtend 64) := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  let origin := rebase state state input.toBasis (RegisterFrame.refl dataRegisters state)
    input.upper 0 (by decide) (by simpa [address] using input.rip)
  let site : X86LegacyFetch.Window state (opcode operation) true source destination :=
    { toBasis := origin
      prefixByte := by
        simpa only [origin,rebase,BitVec.ofNat_toNat,BitVec.setWidth_eq] using
          input.loaded 0 (rex true source destination).toNat (by rfl)
      opcodeByte := by
        simpa only [origin,rebase,BitVec.ofNat_toNat,BitVec.setWidth_eq] using
          input.loaded 1 (opcode operation).toNat (by rfl)
      modrmByte := by
        simpa only [origin,rebase,BitVec.ofNat_toNat,BitVec.setWidth_eq] using
          input.loaded 2 (modRM source destination).toNat (by rfl) }
  obtain ⟨output,run⟩ := fetched other vector operation state source destination site input.left input.right
    input.flags input.sourceKnown input.destinationKnown input.flagsKnown input.quiet
  let flags := X86LogicalFlags.merged input.flags output (0#1)
  let after := X86Move.putPointer (X86Flags.putFlags (put state destination
    (result operation input.left input.right)) flags) site.next
  refine ⟨after,flags,X86FuelPrefix.fetches_one state after run,result_frame _ _ _ _ _ _ _ _,?_,?_,?_⟩
  · rw [X86Move.lookup_putPointer,X86Flags.putFlags_gpr,lookup_put_same]
  · rw [(pointer_frame _ site.next).registers .rflags (by decide)]
    simp only [X86Flags.putFlags,Std.ExtDHashMap.get?_insert_self]
  · simp only [after,X86Move.putPointer,Std.ExtDHashMap.get?_insert_self]
    rfl

namespace Controls
private def source (same : Bool) : Fin 16 := if same then 10 else 9
private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def cells (operation : Kind) (same : Bool) : List (Nat × BitVec 8) :=
  [(4096,rex true (source same) 10),(4097,opcode operation),
    (4098,modRM (source same) 10),(8192,42#8)]
def before (operation : Kind) (same : Bool) (left right : Word) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (4096#64)
  let registers := registers.insert .rdi (0#64)
  let registers := registers.insert .rsi (0#64)
  let registers := registers.insert .rdx (0#64)
  let registers := registers.insert .rcx (0#64)
  let registers := registers.insert .r8 (0#64)
  let registers := registers.insert .r11 (0#64)
  let registers := registers.insert .rax (0#64)
  let registers := registers.insert .rbx (0#64)
  let registers := registers.insert .r12 (0#64)
  let registers := registers.insert .r13 (0#64)
  let registers := registers.insert .r10 left
  let registers := registers.insert .r9 right
  let registers := registers.insert .rsp (8192#64)
  let registers := registers.insert .rflags (0x246#32)
  let registers := registers.insert .log_register_writes false
  ⟨registers,(),Std.ExtHashMap.ofList (cells operation same),(),0,#[]⟩

private theorem cell (operation : Kind) (same : Bool) (left right : Word)
    (key : Nat) (byte : BitVec 8) (present : (key,byte) ∈ cells operation same) :
    (before operation same left right).mem.get? key = some byte :=
  Std.ExtHashMap.getElem?_ofList_of_mem (by simp) (by simp [cells]) present

def input (operation : Kind) (same : Bool) (left right : Word) :
    Inputs (before operation same left right) operation (source same) 10 where
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
  left := left
  right := if same then left else right
  flags := 0x246#32
  sourceKnown := by cases same <;> simp [lookup,before,source,key,Std.ExtDHashMap.get?_insert] <;> rfl
  destinationKnown := by simp [lookup,before,key,Std.ExtDHashMap.get?_insert]; rfl
  flagsKnown := by simp [before,Std.ExtDHashMap.get?_insert]
  quiet := by simp [before]
  upper := by decide
  loaded := by
    intro index byte present
    have within : index < 3 := (List.getElem?_eq_some_iff.mp present).1
    interval_cases index
    · have sameByte : byte = (rex true (source same) 10).toNat := by simpa [code] using present.symm
      subst byte
      change (before operation same left right).mem.get? 4096 = some (BitVec.ofNat 8 (rex true (source same) 10).toNat)
      simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using
        cell operation same left right 4096 _ (by simp [cells])
    · have sameByte : byte = (opcode operation).toNat := by simpa [code] using present.symm
      subst byte
      change (before operation same left right).mem.get? 4097 = some (BitVec.ofNat 8 (opcode operation).toNat)
      simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using
        cell operation same left right 4097 _ (by simp [cells])
    · have sameByte : byte = (modRM (source same) 10).toNat := by simpa [code] using present.symm
      subst byte
      change (before operation same left right).mem.get? 4098 = some (BitVec.ofNat 8 (modRM (source same) 10).toNat)
      simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using
        cell operation same left right 4098 _ (by simp [cells])

theorem runs (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (operation : Kind) (same : Bool) (left right : Word) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 1).run (before operation same left right) = .ok () after ∧
      RegisterFrame (writes 10) (before operation same left right) after ∧
      lookup after 10 = some (result operation left (if same then left else right)) ∧
      after.regs.get? .rflags = some flags ∧ after.regs.get? .rip = some (4099#64) ∧
      lookup after 9 = some right ∧ lookup after 4 = some (8192#64) ∧
      after.mem = (before operation same left right).mem := by
  obtain ⟨after,flags,run,frame,value,flagsKnown,rip⟩ :=
    executes other vector operation (before operation same left right) (source same) 10 (input operation same left right)
  refine ⟨after,flags,run,frame,value,flagsKnown,rip,?_,?_,frame.memory⟩
  · rw [frame.lookup 9 (by decide)]
    simp [lookup,before,key,Std.ExtDHashMap.get?_insert]
    rfl
  · rw [frame.lookup 4 (by decide)]
    simp [lookup,before,key,Std.ExtDHashMap.get?_insert]
    rfl

theorem xor_alias (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) (old : Word) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 1).run (before .xor true old 0) = .ok () after ∧
      RegisterFrame (writes 10) (before .xor true old 0) after ∧ lookup after 10 = some (0#64) ∧
      after.regs.get? .rflags = some flags ∧ after.regs.get? .rip = some (4099#64) ∧
      lookup after 9 = some (0#64) ∧ lookup after 4 = some (8192#64) ∧
      after.mem = (before .xor true old 0).mem := by
  simpa [result] using runs other vector .xor true old (0#64)

theorem and_keeps_high_bits (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 1).run
        (before .and false (0x80000001000000ff#64) (0xffffffff000000f0#64)) = .ok () after ∧
      RegisterFrame (writes 10) (before .and false (0x80000001000000ff#64) (0xffffffff000000f0#64)) after ∧
      lookup after 10 = some (0x80000001000000f0#64) ∧
      after.regs.get? .rflags = some flags ∧ after.regs.get? .rip = some (4099#64) ∧
      lookup after 9 = some (0xffffffff000000f0#64) ∧ lookup after 4 = some (8192#64) ∧
      after.mem = (before .and false (0x80000001000000ff#64) (0xffffffff000000f0#64)).mem := by
  exact runs other vector .and false _ _

theorem wrong_opcode_refused (left right : Word) :
    ¬codeLoaded (before .and false left right) 4096 (code .or 9 10) := by
  intro loaded
  have changed := loaded 1 0x09 (by decide)
  have actual := cell .and false left right 4097 (0x21#8) (by decide)
  change (before .and false left right).mem.get? 4097 = some (0x09#8) at changed
  rw [actual] at changed
  contradiction

theorem wrong_destination_refused (left right : Word) :
    ¬codeLoaded (before .and false left right) 4096 (code .and 9 11) := by
  intro loaded
  have changed := loaded 2 0xcb (by decide)
  have actual := cell .and false left right 4098 (0xca#8) (by decide)
  change (before .and false left right).mem.get? 4098 = some (0xcb#8) at changed
  rw [actual] at changed
  contradiction
end Controls

#print axioms calculate
#print axioms handler
#print axioms fetched
#print axioms result_frame
#print axioms executes
#print axioms Controls.runs
#print axioms Controls.xor_alias
#print axioms Controls.and_keeps_high_bits
#print axioms Controls.wrong_opcode_refused
#print axioms Controls.wrong_destination_refused
end Mettapedia.Machines.TIsa.X86LogicalWord
