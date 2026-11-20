import Mettapedia.Machines.TIsa.X86P1ArithmeticLibrary
import Mettapedia.Machines.TIsa.X86TypedScalarLibrary

/-!
# Preferred p1 arithmetic and existing certified scalar components

Optimized ADD/SUB certificates compose with the established copy, logical and
shift library. Checked instruction lowering chooses the p1 arithmetic or shift
component. The common compiler retains each source recipe and local frame.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86P1ScalarLibrary
open _root_.X86Registers X86RegisterRefinement X86Execution
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev Instruction := Sum X86P1Arithmetic.Instruction X86TypedScalarLibrary.Instruction
abbrev World := X86WordLibrary.World
abbrev Program := X86BlockCompiler.Program Instruction

noncomputable def spec : X86BlockCompiler.Spec Instruction World :=
  X86LibrarySum.combine X86P1ArithmeticLibrary.spec X86TypedScalarLibrary.spec

def p1 : Instruction → P1Source.Instr
  | .inl instruction => X86P1Arithmetic.p1 instruction
  | .inr instruction => X86TypedScalarLibrary.p1 instruction

def destination : Instruction → Fin 12
  | .inl instruction => instruction.core.destination
  | .inr instruction => X86TypedScalarLibrary.destination instruction

def lower? (source : P1Source.Instr) : Option Instruction :=
  match X86P1Arithmetic.lower? source with
  | some instruction => some (.inl instruction)
  | none => (X86ShiftLibrary.lower? source).map (fun instruction => .inr (.inr instruction))

theorem arithmetic_lower?_roundtrip (instruction : X86P1Arithmetic.Instruction) :
    lower? (X86P1Arithmetic.p1 instruction) = some (.inl instruction) := by
  simp only [lower?,X86P1Arithmetic.lower?_roundtrip]

theorem lower?_source {source : P1Source.Instr} {instruction : Instruction}
    (accepted : lower? source = some instruction) : p1 instruction = source := by
  cases arithmetic : X86P1Arithmetic.lower? source with
  | some actual =>
    simp only [lower?,arithmetic,Option.some.injEq] at accepted
    subst instruction
    exact X86P1Arithmetic.lower?_source arithmetic
  | none =>
    cases shift : X86ShiftLibrary.lower? source with
    | none => simp [lower?,arithmetic,shift] at accepted
    | some actual =>
      simp only [lower?,arithmetic,shift,Option.map_some,Option.some.injEq] at accepted
      subst instruction
      exact X86ShiftLibrary.lower?_source shift

theorem progress (instruction : Instruction) : (spec.action instruction).Progress :=
  X86LibrarySum.progress X86P1ArithmeticLibrary.spec X86TypedScalarLibrary.spec
    X86P1ArithmeticLibrary.progress X86TypedScalarLibrary.progress instruction

theorem arithmetic_handlers_agree (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :
    X86P1Arithmetic.handlers (X86Shift.linkedHandlers other) extra = X86TypedShiftBlock.handlers other extra := rfl

theorem correct (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
    letI : VectorOpcodeHandlers := vector
    X86BlockCompiler.Correct spec := by
  let : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
  let : VectorOpcodeHandlers := vector
  have arithmetic := X86P1ArithmeticLibrary.correct (X86Shift.linkedHandlers other) extra vector
  rw [arithmetic_handlers_agree] at arithmetic
  exact X86LibrarySum.correct X86P1ArithmeticLibrary.spec X86TypedScalarLibrary.spec arithmetic
    (X86TypedScalarLibrary.correct other extra vector) rfl rfl

theorem source_wp_step (instruction : Instruction) (values : Fin 12 → Word) (result : Word)
    (computed : P1Scalar.evaluate (p1 instruction) ((p1 instruction).reads.map values) = some result)
    (post : Unit → World → Prop)
    (expected : post () (Cells.encode Finset.univ (Function.update values (destination instruction) result))) :
    (Prog.prim instruction).wp spec.action post (Cells.encode Finset.univ values) := by
  cases instruction with
  | inl instruction =>
    have same : X86P1Arithmetic.evaluate instruction values = result :=
      Option.some.inj ((X86P1Arithmetic.computes instruction values).symm.trans computed)
    apply X86P1ArithmeticLibrary.source_wp_step instruction values post
    simpa only [destination,same] using expected
  | inr instruction => exact X86TypedScalarLibrary.source_wp_step instruction values result computed post expected

theorem stack_readonly : Register.rsp ∉ spec.registerWrites := by
  intro member
  rcases Finset.mem_union.mp member with left | right
  · exact X86WordLibrary.stack_readonly left
  · exact X86TypedScalarLibrary.stack_readonly right

theorem frame_readonly : Register.rdi ∉ spec.registerWrites := by
  intro member
  rcases Finset.mem_union.mp member with left | right
  · exact X86WordLibrary.frame_readonly left
  · exact X86TypedScalarLibrary.frame_readonly right

theorem compile_wp (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (stop : Int) (program : Program) (source : World) (native : State)
    (input : X86BlockCompiler.At spec stop program source native) (post : Unit → World → Prop)
    (wp : program.wp spec.action post source) :
    letI : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ following after, program.Runs spec.action source () following ∧ post () following ∧
      (X86FuelPrefix.fetches (X86BlockCompiler.steps spec program)).run native = .ok () after ∧
      X86StateFrame.Frame spec.registerWrites spec.byteWrites native after ∧
      X86BlockCompiler.Observed spec stop () following after := by
  let : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
  let : VectorOpcodeHandlers := vector
  exact X86BlockCompiler.compile_wp spec (correct other extra vector) progress stop program source native input post wp

#print axioms lower?_source
#print axioms arithmetic_lower?_roundtrip
#print axioms correct
#print axioms source_wp_step
#print axioms compile_wp
end Mettapedia.Machines.TIsa.X86P1ScalarLibrary
