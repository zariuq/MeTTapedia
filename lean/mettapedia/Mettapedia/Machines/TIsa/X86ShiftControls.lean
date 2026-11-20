import Mettapedia.Machines.TIsa.X86Shift

/-! Concrete fetched-shift controls over a four-byte image and a partial register map. -/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86Shift.Controls
open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution X86MaskedFlags
local instance : MemoryPrimitives := X86Memory.ordinary

private def control : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))

def before (operation : Shift) (value : Word) (count : BitVec 8) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs control
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (0x1000#64)
  let registers := registers.insert .log_register_writes false
  let registers := registers.insert .rflags (0x200#32)
  let registers := registers.insert .r11 value
  ⟨registers,(),
    ((((∅ : Std.ExtHashMap Nat (BitVec 8)).insert 4096 (rex true (extension operation) 11)).insert 4097
      (0xc1#8)).insert 4098 (modRM (extension operation) 11)).insert 4099 count,(),0,#[]⟩

private def window (operation : Shift) (value : Word) (count : BitVec 8) :
    X86LegacyFetch.Window (before operation value count) (0xc1#8) true (extension operation) 11 where
  address := 0x1000#48
  opcodeAddress := 0x1001#48
  modrmAddress := 0x1002#48
  next := 0x1003#48
  control := control
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
  prefixByte := by simp [before,Std.ExtHashMap.getElem_insert]
  opcodeByte := by simp [before,Std.ExtHashMap.getElem_insert]
  modrmByte := by simp [before,Std.ExtHashMap.getElem_insert]

def origin (operation : Shift) (value : Word) (count : BitVec 8) :
    X86LegacyFetch.Basis (before operation value count) := (window operation value count).toBasis

theorem executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (operation : Shift) (value : Word) (count : BitVec 8) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (Functions.x86_fetch_decode_execute ()).run (before operation value count) = .ok () after ∧
      lookup after 11 = some (evaluate operation value (count.setWidth 6)) ∧
      after.regs.get? .rip = some (0x1004#64) ∧
      RegisterFrame {.r11,.rflags,.rip} (before operation value count) after := by
  let : OtherOpcodeHandlers := linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have known : lookup (before operation value count) 11 = some value := by
    change ((before operation value count).regs.get? .r11).map (fun x : Word => x) = _
    simp [before]
  obtain ⟨output,mask,run⟩ := fetched other vector operation (before operation value count) 11
    (window operation value count) (0x1004#48) value (0x200#32) count (by rfl) known
    (by simp [before,Std.ExtDHashMap.get?_insert])
    (by simp [before,Std.ExtDHashMap.get?_insert])
    (by simp [before,window])
  refine ⟨_,run,?_,?_,?_⟩
  · rw [X86Move.lookup_putPointer,lookup_put_same]
  · simp [X86Move.putPointer]
  · exact result_frame _ 11 _ (0x200#32) output mask (0x1004#48)

theorem shift_left_high_bit (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (Functions.x86_fetch_decode_execute ()).run (before .left (1#64) (63#8)) = .ok () after ∧
      lookup after 11 = some (0x8000000000000000#64) ∧
      after.regs.get? .rip = some (0x1004#64) ∧
      RegisterFrame {.r11,.rflags,.rip} (before .left (1#64) (63#8)) after := by
  simpa only [show evaluate .left (1#64) ((63#8).setWidth 6) = (0x8000000000000000#64) from rfl] using
    executes other vector .left (1#64) (63#8)

theorem shift_right_high_bit (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (Functions.x86_fetch_decode_execute ()).run (before .rightUnsigned (0x8000000000000000#64) (63#8)) = .ok () after ∧
      lookup after 11 = some (1#64) ∧
      after.regs.get? .rip = some (0x1004#64) ∧
      RegisterFrame {.r11,.rflags,.rip} (before .rightUnsigned (0x8000000000000000#64) (63#8)) after := by
  simpa only [show evaluate .rightUnsigned (0x8000000000000000#64) ((63#8).setWidth 6) = (1#64) from rfl] using
    executes other vector .rightUnsigned (0x8000000000000000#64) (63#8)

theorem shift_signed_high_bit (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (Functions.x86_fetch_decode_execute ()).run (before .rightSigned (0x8000000000000000#64) (63#8)) = .ok () after ∧
      lookup after 11 = some (0xffffffffffffffff#64) ∧
      after.regs.get? .rip = some (0x1004#64) ∧
      RegisterFrame {.r11,.rflags,.rip} (before .rightSigned (0x8000000000000000#64) (63#8)) after := by
  simpa only [show evaluate .rightSigned (0x8000000000000000#64) ((63#8).setWidth 6) = (0xffffffffffffffff#64) from rfl] using
    executes other vector .rightSigned (0x8000000000000000#64) (63#8)

theorem unsigned_answer_refused (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (after : State) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run (before .rightSigned (0x8000000000000000#64) (63#8)) = .ok () after →
      lookup after 11 ≠ some (1#64) := by
  obtain ⟨correct,run,value,_,_⟩ := shift_signed_high_bit other vector
  intro given
  have same := (EStateM.Result.ok.inj (given.symm.trans run)).2
  subst after
  rw [value]
  decide

theorem wrong_direction_refused (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (after : State) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run (before .rightUnsigned (8#64) (1#8)) = .ok () after →
      lookup after 11 ≠ some (16#64) := by
  obtain ⟨correct,run,value,_,_⟩ := executes other vector .rightUnsigned (8#64) (1#8)
  intro given
  have same := (EStateM.Result.ok.inj (given.symm.trans run)).2
  subst after
  rw [value]
  decide

theorem oversized_count_executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (operation : Shift) (value : Word) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (Functions.x86_fetch_decode_execute ()).run (before operation value (64#8)) = .ok () after ∧
      lookup after 11 = some value ∧
      after.regs.get? .rip = some (0x1004#64) ∧
      RegisterFrame {.r11,.rflags,.rip} (before operation value (64#8)) after := by
  simpa only [native_masks64] using executes other vector operation value (64#8)

#print axioms executes
#print axioms shift_left_high_bit
#print axioms shift_right_high_bit
#print axioms shift_signed_high_bit
#print axioms unsigned_answer_refused
#print axioms wrong_direction_refused
#print axioms oversized_count_executes
end Mettapedia.Machines.TIsa.X86Shift.Controls
