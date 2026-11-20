import Mettapedia.Machines.TIsa.X86ShiftBlock
import Mettapedia.Machines.TIsa.X86ShiftControls

/-! In-place compilation uses the single encoded shift and retains explicit range refusals. -/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86ShiftBlock.Controls
open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

def instruction : Instruction := ⟨.rightSigned,7,7,63,by decide⟩
theorem compiled_bytes : bytes instruction = [0x49,0xc1,0xfb,63] := by decide
theorem one_instruction : count instruction = 1 := by decide
theorem positive_lowering : (lower? (p1 instruction)).isSome = true := by rw [lower?_roundtrip]; rfl
theorem count64_refused : lower? (.shift .rightSigned .u64 7 7 64) = none :=
  lower?_large_refused _ _ _ _ (by decide)
theorem frame_pointer_refused : lower? (.shift .left .u64 0 7 1) = none := lower?_protected_refused _ _ _

def before (value : Word) : State := X86Shift.Controls.before .rightSigned value (63#8)

private theorem loaded (value : Word) : codeLoaded (before value) 4096 (bytes instruction) := by
  rw [compiled_bytes]
  intro index byte found
  have within : index < 4 := (List.getElem?_eq_some_iff.mp found).1
  interval_cases index <;> simp only [List.getElem?_cons_zero,List.getElem?_cons_succ] at found <;>
    cases found <;> simp [before,X86Shift.Controls.before,address,Std.ExtHashMap.getElem_insert] <;> rfl

theorem in_place (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (value : Word) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run (before value) = .ok () after ∧
      lookup after 11 = some (value.sshiftRight 63) ∧
      after.regs.get? .rip = some (0x1004#64) ∧
      RegisterFrame (writes instruction) (before value) after ∧
      ∀ prefixCount ≤ 1, ∀ observed,
        (X86FuelPrefix.fetches prefixCount).run (before value) = .ok () observed →
          RegisterFrame (writes instruction) (before value) observed := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let values : Fin 12 → Word := fun _ => value
  have known : lookup (before value) 11 = some value := by
    change ((before value).regs.get? .r11).map (fun x : Word => x) = _
    simp [before,X86Shift.Controls.before]
  obtain ⟨after,nextFlags,run,frame,result,pointer,_flags,_quiet,_control,prefixes⟩ :=
    executes_block other extra vector instruction values (before value)
      (X86Shift.Controls.origin .rightSigned value (63#8)) known (0x200#32)
      (by simp [before,X86Shift.Controls.before,Std.ExtDHashMap.get?_insert])
      (by simp [before,X86Shift.Controls.before,Std.ExtDHashMap.get?_insert])
      (by change (4096 : Int) + 4 + 3 < 2 ^ 47; decide) (loaded value)
  refine ⟨after,?_,?_,?_,frame,?_⟩
  · simpa only [one_instruction] using run
  · exact result
  · exact pointer
  · simpa only [one_instruction] using prefixes

#print axioms in_place
#print axioms count64_refused
#print axioms frame_pointer_refused
end Mettapedia.Machines.TIsa.X86ShiftBlock.Controls
