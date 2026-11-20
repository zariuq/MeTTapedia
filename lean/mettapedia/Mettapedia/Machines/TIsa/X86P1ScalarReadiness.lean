import Mettapedia.Machines.TIsa.X86P1ScalarLibrary
import Mettapedia.Machines.TIsa.X86Readiness

/-!
# CPU entry profiles through the preferred p1 scalar library

The existing optimized ADD/SUB and typed shift executions retain their actual
control-flag observations. These facts strengthen the established component
compiler with the same segment, control-register and alignment profile used
by memory operations. Bytes, counts, source actions and frames are retained.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86P1ScalarReadiness
open _root_.X86Registers X86RegisterRefinement X86Execution
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open X86Readiness
local instance : MemoryPrimitives := X86Memory.ordinary

theorem arithmetic_stable (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (profile : Profile) :
    letI : OtherOpcodeHandlers := X86P1Arithmetic.handlers other extra
    letI : VectorOpcodeHandlers := vector
    Stable X86P1ArithmeticLibrary.spec profile.Holds := by
  let : OtherOpcodeHandlers := X86P1Arithmetic.handlers other extra
  let : VectorOpcodeHandlers := vector
  intro instruction source _following native origin _safe _step represented prepared holds upper loaded
    _outside after candidate
  obtain ⟨values,_sourceEq,known⟩ := represented
  obtain ⟨flags,flagsKnown,quiet⟩ := prepared
  have registers (register : Fin 12) :
      lookup native (X86P1Arithmetic.physical register) = some (values register) := by
    change lookup native (X86P1ArithmeticLibrary.physical register) = some (values register)
    rw [X86P1ArithmeticLibrary.physical_copy]
    exact known register (Finset.mem_univ _)
  obtain ⟨target,nextFlags,run,frame,_result,_rip,nextKnown,_quiet,control,_prefixes⟩ :=
    X86P1Arithmetic.executes other extra vector instruction values native origin
      (registers instruction.core.left) (registers instruction.core.right) flags flagsKnown quiet
      (by simpa [X86P1ArithmeticLibrary.spec,Int.add_assoc] using upper) loaded
  have same := X86FuelPrefix.fetches_deterministic _ native after target candidate run
  rw [same]
  exact profile.after_control native target _ _ (X86StateFrame.registerOnly frame)
    (X86P1Arithmetic.writes_data instruction) control ⟨nextFlags,nextKnown⟩ holds

theorem shifts_stable (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (profile : Profile) :
    letI : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
    letI : VectorOpcodeHandlers := vector
    Stable X86ShiftLibrary.spec profile.Holds := by
  let : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
  let : VectorOpcodeHandlers := vector
  intro instruction source _following native origin _safe _step represented prepared holds upper loaded
    _outside after candidate
  obtain ⟨values,_sourceEq,known⟩ := represented
  obtain ⟨flags,flagsKnown,quiet⟩ := prepared
  have register : lookup native (X86ShiftLibrary.physical (X86ShiftLibrary.sourceRegister instruction)) =
      some (values (X86ShiftLibrary.sourceRegister instruction)) := by
    rw [X86ShiftLibrary.physical_copy]
    exact known _ (Finset.mem_univ _)
  have bounded : origin.address.toInt + (X86ShiftLibrary.bytes instruction).length + 3 < 2 ^ 47 := by
    simpa [X86ShiftLibrary.spec,Int.add_assoc] using upper
  have actual : ∃ target nextFlags,
      (X86FuelPrefix.fetches (X86ShiftLibrary.count instruction)).run native = .ok () target ∧
      RegisterFrame (X86ShiftLibrary.writes instruction) native target ∧
      target.regs.get? .rflags = some nextFlags ∧ X86ControlFlags.Preserved native target := by
    cases instruction with
    | inl instruction =>
      have proof := X86ShiftBlock.executes_block (X86Extend32.linkedHandlers other) extra vector
        instruction values native origin register flags flagsKnown quiet bounded loaded
      rw [X86ShiftLibrary.old_handlers_agree] at proof
      obtain ⟨target,nextFlags,run,frame,_value,_rip,nextKnown,_quiet,control,_prefixes⟩ := proof
      exact ⟨target,nextFlags,run,frame,nextKnown,control⟩
    | inr instruction =>
      obtain ⟨target,nextFlags,run,frame,_value,_rip,nextKnown,_quiet,control,_prefixes⟩ :=
        X86TypedShiftBlock.executes_block other extra vector instruction values native origin
          register flags flagsKnown quiet (by
            change origin.address.toInt + (X86TypedShiftBlock.bytes instruction).length + 3 < _ at bounded
            omega) loaded
      exact ⟨target,nextFlags,run,frame,nextKnown,control⟩
  obtain ⟨target,nextFlags,run,frame,nextKnown,control⟩ := actual
  have same := X86FuelPrefix.fetches_deterministic _ native after target candidate run
  rw [same]
  have dataOnly : X86ShiftLibrary.writes instruction ⊆ dataRegisters :=
    (X86ShiftLibrary.writes_included instruction).trans X86WordLibrary.data_only
  exact profile.after_control native target _ _ (X86StateFrame.registerOnly frame)
    dataOnly control ⟨nextFlags,nextKnown⟩ holds

theorem typed_stable (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (profile : Profile) :
    letI : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
    letI : VectorOpcodeHandlers := vector
    Stable X86TypedScalarLibrary.spec profile.Holds := by
  let : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
  let : VectorOpcodeHandlers := vector
  have scalar := X86Readiness.scalar_stable
    (X86Extend32.linkedHandlers (X86Shift.linkedHandlers (X86EscapeFetch.linked other extra))) vector profile
  rw [X86TypedScalarLibrary.scalar_handlers_agree] at scalar
  exact X86Readiness.sum_stable X86ScalarLibrary.spec X86ShiftLibrary.spec profile.Holds
    scalar (shifts_stable other extra vector profile) rfl rfl

theorem stable (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (profile : Profile) :
    letI : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
    letI : VectorOpcodeHandlers := vector
    Stable X86P1ScalarLibrary.spec profile.Holds := by
  let : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
  let : VectorOpcodeHandlers := vector
  have arithmetic := arithmetic_stable (X86Shift.linkedHandlers other) extra vector profile
  rw [X86P1ScalarLibrary.arithmetic_handlers_agree] at arithmetic
  exact X86Readiness.sum_stable X86P1ArithmeticLibrary.spec X86TypedScalarLibrary.spec profile.Holds
    arithmetic (typed_stable other extra vector profile) rfl rfl

theorem correct (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (profile : Profile) :
    letI : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
    letI : VectorOpcodeHandlers := vector
    X86BlockCompiler.Correct (strengthen X86P1ScalarLibrary.spec profile.Holds) := by
  let : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
  let : VectorOpcodeHandlers := vector
  exact X86Readiness.correct X86P1ScalarLibrary.spec profile.Holds
    (X86P1ScalarLibrary.correct other extra vector) (stable other extra vector profile)

theorem compile_wp (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (profile : Profile) (stop : Int)
    (program : X86P1ScalarLibrary.Program) (source : X86P1ScalarLibrary.World) (native : State)
    (input : X86BlockCompiler.At (strengthen X86P1ScalarLibrary.spec profile.Holds) stop program source native)
    (post : Unit → X86P1ScalarLibrary.World → Prop)
    (wp : program.wp X86P1ScalarLibrary.spec.action post source) :
    letI : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ following after, program.Runs X86P1ScalarLibrary.spec.action source () following ∧ post () following ∧
      (X86FuelPrefix.fetches (X86BlockCompiler.steps X86P1ScalarLibrary.spec program)).run native = .ok () after ∧
      X86StateFrame.Frame X86P1ScalarLibrary.spec.registerWrites X86P1ScalarLibrary.spec.byteWrites native after ∧
      X86BlockCompiler.Observed (strengthen X86P1ScalarLibrary.spec profile.Holds) stop () following after := by
  let : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
  let : VectorOpcodeHandlers := vector
  have proof := X86BlockCompiler.compile_wp (strengthen X86P1ScalarLibrary.spec profile.Holds)
    (correct other extra vector profile) X86P1ScalarLibrary.progress stop program source native input post wp
  rw [X86Readiness.steps_strengthen] at proof
  simpa only [X86Readiness.strengthen] using proof

#print axioms arithmetic_stable
#print axioms shifts_stable
#print axioms stable
#print axioms correct
#print axioms compile_wp
end Mettapedia.Machines.TIsa.X86P1ScalarReadiness
