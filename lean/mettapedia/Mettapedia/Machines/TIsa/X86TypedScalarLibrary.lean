import Mettapedia.Machines.TIsa.X86ShiftLibrary
import Mettapedia.Machines.TIsa.X86ScalarLibrary

/-!
# Mixed captured word operations and typed shifts

The existing arithmetic/logical library and the U64/U32Z/I32S shift library
share a representation and readiness contract. Their concrete certificates
combine through the established block compiler and source/WP semantics.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86TypedScalarLibrary
open _root_.X86Registers X86RegisterRefinement X86Execution
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev Instruction := Sum X86ScalarLibrary.Instruction X86ShiftLibrary.Instruction
abbrev World := X86WordLibrary.World
abbrev Program := X86BlockCompiler.Program Instruction

noncomputable def spec : X86BlockCompiler.Spec Instruction World :=
  X86LibrarySum.combine X86ScalarLibrary.spec X86ShiftLibrary.spec

def p1 : Instruction → P1Source.Instr
  | .inl instruction => X86ScalarLibrary.p1 instruction
  | .inr instruction => X86ShiftLibrary.p1 instruction

def destination : Instruction → Fin 12
  | .inl instruction => (X86ScalarLibrary.effect instruction).destination
  | .inr instruction => X86ShiftLibrary.destination instruction

theorem progress (instruction : Instruction) : (spec.action instruction).Progress :=
  X86LibrarySum.progress X86ScalarLibrary.spec X86ShiftLibrary.spec
    X86ScalarLibrary.progress X86ShiftLibrary.progress instruction

theorem scalar_handlers_agree (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :
    X86Arithmetic.linkedHandlers
      (X86Extend32.linkedHandlers (X86Shift.linkedHandlers (X86EscapeFetch.linked other extra))) =
      X86TypedShiftBlock.handlers other extra := rfl

theorem correct (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
    letI : VectorOpcodeHandlers := vector
    X86BlockCompiler.Correct spec := by
  let : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
  let : VectorOpcodeHandlers := vector
  have arithmetic := X86ScalarLibrary.correct
    (X86Extend32.linkedHandlers (X86Shift.linkedHandlers (X86EscapeFetch.linked other extra))) vector
  rw [scalar_handlers_agree] at arithmetic
  exact X86LibrarySum.correct X86ScalarLibrary.spec X86ShiftLibrary.spec arithmetic
    (X86ShiftLibrary.correct other extra vector) rfl rfl

theorem source_wp_step (instruction : Instruction) (values : Fin 12 → Word) (result : Word)
    (computed : P1Scalar.evaluate (p1 instruction) ((p1 instruction).reads.map values) = some result)
    (post : Unit → World → Prop)
    (expected : post () (Cells.encode Finset.univ (Function.update values (destination instruction) result))) :
    (Prog.prim instruction).wp spec.action post (Cells.encode Finset.univ values) := by
  cases instruction with
  | inl instruction =>
    apply X86ScalarLibrary.source_wp_step instruction values result _ post expected
    rw [X86ScalarLibrary.source_evaluate_p1]
    exact computed
  | inr instruction =>
    have same : X86ShiftLibrary.evaluate instruction values = result :=
      Option.some.inj ((X86ShiftLibrary.computes instruction values).symm.trans computed)
    apply X86ShiftLibrary.source_wp_step instruction values post
    simpa only [destination,same] using expected

theorem stack_readonly : Register.rsp ∉ spec.registerWrites := by
  intro member
  rcases Finset.mem_union.mp member with left | right
  · exact X86ScalarLibrary.stack_readonly left
  · exact X86WordLibrary.stack_readonly right

theorem frame_readonly : Register.rdi ∉ spec.registerWrites := by
  intro member
  rcases Finset.mem_union.mp member with left | right
  · exact X86ScalarLibrary.frame_readonly left
  · exact X86WordLibrary.frame_readonly right

theorem compile_wp (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (stop : Int) (program : Program) (source : World) (native : State)
    (input : X86BlockCompiler.At spec stop program source native)
    (post : Unit → World → Prop) (wp : program.wp spec.action post source) :
    letI : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ following after, program.Runs spec.action source () following ∧ post () following ∧
      (X86FuelPrefix.fetches (X86BlockCompiler.steps spec program)).run native = .ok () after ∧
      X86StateFrame.Frame spec.registerWrites spec.byteWrites native after ∧
      X86BlockCompiler.Observed spec stop () following after := by
  let : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
  let : VectorOpcodeHandlers := vector
  exact X86BlockCompiler.compile_wp spec (correct other extra vector) progress stop program source native input post wp

#print axioms correct
#print axioms source_wp_step
#print axioms compile_wp
end Mettapedia.Machines.TIsa.X86TypedScalarLibrary
