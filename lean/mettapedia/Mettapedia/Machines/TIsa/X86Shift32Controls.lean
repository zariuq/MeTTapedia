import Mettapedia.Machines.TIsa.X86Shift32Instruction

/-! Fetched bare and REX dword-shift controls, including count and extension boundaries. -/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86Shift32Instruction.Controls
open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution X86MaskedFlags
local instance : MemoryPrimitives := X86Memory.ordinary

private def control : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))

def before (high : Bool) (operation : Shift) (value : Word) (count : BitVec 8) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs control
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (0x1000#64)
  let registers := registers.insert .log_register_writes false
  let registers := registers.insert .rflags (0x200#32)
  let registers := registers.insert .rax value
  let registers := registers.insert .r11 value
  let memory := if high then
      ((((∅ : Std.ExtHashMap Nat (BitVec 8)).insert 4096 (rex false (extension operation) 11)).insert 4097
        (0xc1#8)).insert 4098 (modRM (extension operation) 11)).insert 4099 count
    else (((∅ : Std.ExtHashMap Nat (BitVec 8)).insert 4096 (0xc1#8)).insert 4097
      (modRM (extension operation) 0)).insert 4098 count
  ⟨registers,(),memory,(),0,#[]⟩

private def bare (operation : Shift) (value : Word) (count : BitVec 8) :
    X86BareFetch.Window (before false operation value count) (0xc1#8) (modRM (extension operation) 0) where
  address := 0x1000#48
  modrmAddress := 0x1001#48
  next := 0x1002#48
  step1 := by decide
  step2 := by decide
  control := control
  attributes := attributes
  status := by simp [before,Std.ExtDHashMap.get?_insert]
  fault := by simp [before,Std.ExtDHashMap.get?_insert]
  msrs := by simp [before,Std.ExtDHashMap.get?_insert]
  segments := by simp [before,Std.ExtDHashMap.get?_insert]
  longMode := by decide
  codeMode := by decide
  application := by simp [before,Std.ExtDHashMap.get?_insert]
  rip := by simp [before,Std.ExtDHashMap.get?_insert]
  opcodeByte := by simp [before,Std.ExtHashMap.getElem_insert]
  modrmByte := by simp [before,Std.ExtHashMap.getElem_insert]

private def extended (operation : Shift) (value : Word) (count : BitVec 8) :
    X86LegacyFetch.Window (before true operation value count) (0xc1#8) false (extension operation) 11 where
  address := 0x1000#48
  opcodeAddress := 0x1001#48
  modrmAddress := 0x1002#48
  next := 0x1003#48
  step1 := by decide
  step2 := by decide
  step3 := by decide
  control := control
  attributes := attributes
  status := by simp [before,Std.ExtDHashMap.get?_insert]
  fault := by simp [before,Std.ExtDHashMap.get?_insert]
  msrs := by simp [before,Std.ExtDHashMap.get?_insert]
  segments := by simp [before,Std.ExtDHashMap.get?_insert]
  longMode := by decide
  codeMode := by decide
  application := by simp [before,Std.ExtDHashMap.get?_insert]
  rip := by simp [before,Std.ExtDHashMap.get?_insert]
  prefixByte := by simp [before,Std.ExtHashMap.getElem_insert]
  opcodeByte := by simp [before,Std.ExtHashMap.getElem_insert]
  modrmByte := by simp [before,Std.ExtHashMap.getElem_insert]

theorem executes_bare (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (operation : Shift) (value : Word) (count : BitVec 8) :
    letI : OtherOpcodeHandlers := X86Shift.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (Functions.x86_fetch_decode_execute ()).run (before false operation value count) = .ok () after ∧
      lookup after 0 = some (evaluate operation value count) ∧
      after.regs.get? .rip = some (0x1003#64) ∧
      RegisterFrame {.rax,.rflags,.rip} (before false operation value count) after := by
  let : OtherOpcodeHandlers := X86Shift.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have known : lookup (before false operation value count) 0 = some value := by
    change ((before false operation value count).regs.get? .rax).map (fun x : Word => x) = _
    simp [before,Std.ExtDHashMap.get?_insert]
  obtain ⟨output,mask,run⟩ := fetched_bare other vector operation (before false operation value count) 0
    (by decide) (bare operation value count) (0x1003#48) value (0x200#32) count (by rfl) known
    (by simp [before,Std.ExtDHashMap.get?_insert])
    (by simp [before,Std.ExtDHashMap.get?_insert])
    (by simp [before,bare])
  refine ⟨_,run,?_,?_,?_⟩
  · rw [X86Move.lookup_putPointer,lookup_put_same]
  · simp [X86Move.putPointer]
  · exact result_frame operation _ 0 value count (0x200#32) output mask (0x1003#48)

theorem executes_rex (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (operation : Shift) (value : Word) (count : BitVec 8) :
    letI : OtherOpcodeHandlers := X86Shift.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (Functions.x86_fetch_decode_execute ()).run (before true operation value count) = .ok () after ∧
      lookup after 11 = some (evaluate operation value count) ∧
      after.regs.get? .rip = some (0x1004#64) ∧
      RegisterFrame {.r11,.rflags,.rip} (before true operation value count) after := by
  let : OtherOpcodeHandlers := X86Shift.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have known : lookup (before true operation value count) 11 = some value := by
    change ((before true operation value count).regs.get? .r11).map (fun x : Word => x) = _
    simp [before]
  obtain ⟨output,mask,run⟩ := fetched_rex other vector operation (before true operation value count) 11
    (by decide) (extended operation value count) (0x1004#48) value (0x200#32) count (by rfl) known
    (by simp [before,Std.ExtDHashMap.get?_insert])
    (by simp [before,Std.ExtDHashMap.get?_insert])
    (by simp [before,extended])
  refine ⟨_,run,?_,?_,?_⟩
  · rw [X86Move.lookup_putPointer,lookup_put_same]
  · simp [X86Move.putPointer]
  · exact result_frame operation _ 11 value count (0x200#32) output mask (0x1004#48)

theorem zero_count_clears_upper (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (operation : Shift) (value : Word) :
    letI : OtherOpcodeHandlers := X86Shift.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (Functions.x86_fetch_decode_execute ()).run (before false operation value (0#8)) = .ok () after ∧
      lookup after 0 = some ((low32 value).zeroExtend 64) ∧
      after.regs.get? .rip = some (0x1003#64) ∧
      RegisterFrame {.rax,.rflags,.rip} (before false operation value (0#8)) after := by
  have unchanged : evaluate operation value (0#8) = (low32 value).zeroExtend 64 := by
    cases operation <;> simp [evaluate,Shift.evaluate]
  simpa only [unchanged] using executes_bare other vector operation value (0#8)

theorem count32_masks_to_zero (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (operation : Shift) (value : Word) :
    letI : OtherOpcodeHandlers := X86Shift.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (Functions.x86_fetch_decode_execute ()).run (before true operation value (32#8)) = .ok () after ∧
      lookup after 11 = some ((low32 value).zeroExtend 64) ∧
      after.regs.get? .rip = some (0x1004#64) ∧
      RegisterFrame {.r11,.rflags,.rip} (before true operation value (32#8)) after := by
  have unchanged : evaluate operation value (32#8) = (low32 value).zeroExtend 64 := by
    cases operation <;> simp [evaluate,Shift.evaluate]
  simpa only [unchanged] using executes_rex other vector operation value (32#8)

theorem signed_high_bit (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Shift.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (Functions.x86_fetch_decode_execute ()).run
        (before false .rightSigned (0xdeadbeef80000000#64) (31#8)) = .ok () after ∧
      lookup after 0 = some (0xffffffff#64) ∧
      after.regs.get? .rip = some (0x1003#64) ∧
      RegisterFrame {.rax,.rflags,.rip} (before false .rightSigned (0xdeadbeef80000000#64) (31#8)) after := by
  exact executes_bare other vector .rightSigned (0xdeadbeef80000000#64) (31#8)

theorem unsigned_high_bit (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Shift.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (Functions.x86_fetch_decode_execute ()).run
        (before true .rightUnsigned (0xdeadbeef80000000#64) (31#8)) = .ok () after ∧
      lookup after 11 = some (1#64) ∧
      after.regs.get? .rip = some (0x1004#64) ∧
      RegisterFrame {.r11,.rflags,.rip} (before true .rightUnsigned (0xdeadbeef80000000#64) (31#8)) after := by
  exact executes_rex other vector .rightUnsigned (0xdeadbeef80000000#64) (31#8)

theorem implicit_sign_extension_refused (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (after : State) :
    letI : OtherOpcodeHandlers := X86Shift.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run
        (before false .rightSigned (0xdeadbeef80000000#64) (31#8)) = .ok () after →
      lookup after 0 ≠ some (0xffffffffffffffff#64) := by
  obtain ⟨correct,run,value,_,_⟩ := signed_high_bit other vector
  intro given
  have same := (EStateM.Result.ok.inj (given.symm.trans run)).2
  subst after
  rw [value]
  decide

theorem wrong_direction_refused (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (after : State) :
    letI : OtherOpcodeHandlers := X86Shift.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run (before true .rightUnsigned (8#64) (1#8)) = .ok () after →
      lookup after 11 ≠ some (16#64) := by
  obtain ⟨correct,run,value,_,_⟩ := executes_rex other vector .rightUnsigned (8#64) (1#8)
  intro given
  have same := (EStateM.Result.ok.inj (given.symm.trans run)).2
  subst after
  rw [value]
  decide

theorem source_refuses_count32 (operation : Shift) (value : Word) (destination : Fin 12) :
    P1Scalar.evaluate (.shift operation .u32z destination destination 32) [value] = none := by rfl

theorem signed_source_needs_normalization :
    P1Scalar.evaluate (.shift .rightSigned .i32s 0 0 31) [0x80000000] = some 0xffffffffffffffff ∧
      evaluate .rightSigned (0x80000000#64) (31#8) ≠ (0xffffffffffffffff#64) := by decide

#print axioms executes_bare
#print axioms executes_rex
#print axioms zero_count_clears_upper
#print axioms count32_masks_to_zero
#print axioms signed_high_bit
#print axioms unsigned_high_bit
#print axioms implicit_sign_extension_refused
#print axioms wrong_direction_refused
#print axioms source_refuses_count32
#print axioms signed_source_needs_normalization
end Mettapedia.Machines.TIsa.X86Shift32Instruction.Controls
