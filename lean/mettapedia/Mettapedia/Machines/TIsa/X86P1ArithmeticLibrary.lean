import Mettapedia.Machines.TIsa.X86P1Arithmetic
import Mettapedia.Machines.TIsa.X86BlockCompiler

/-!
# Optimized p1 ADD/SUB in the common source/WP compiler

The actual aliasing-directed template certificate is joined to the existing
p1 resource recipe and canonical register representation. The shared compiler
supplies layout, sequencing, source/WP realization and every-prefix frames.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86P1ArithmeticLibrary
open _root_.X86Registers X86RegisterRefinement X86Execution
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev Instruction := X86P1Arithmetic.Instruction
abbrev World := X86WordLibrary.World
abbrev physical := X86P1Arithmetic.physical
abbrev p1 := X86P1Arithmetic.p1
abbrev bytes := X86P1Arithmetic.bytes
abbrev count := X86P1Arithmetic.count
abbrev evaluate := X86P1Arithmetic.evaluate
abbrev writes := X86P1Arithmetic.writes
abbrev effect := X86P1Arithmetic.effect

def action (instruction : Instruction) : Mettapedia.GSLT.Logic.AbstractSeparationLogic.Action World Unit where
  Safe world := ∃ invocation : CellEffects.Invocation (effect instruction), CellEffects.system.Enables world invocation
  Step world _ after := (CellEffects.profile [effect instruction]).theory.rewrites world after

theorem progress (instruction : Instruction) : (action instruction).Progress := by
  rintro world ⟨invocation,enabled⟩
  exact ⟨(),CellEffects.system.fire world invocation,ULift.up (0 : Fin 1),invocation,enabled,rfl⟩

theorem source_step_iff (instruction : Instruction) (values : Fin 12 → Word) (following : World) :
    (action instruction).Step (Cells.encode Finset.univ values) () following ↔
      following = Cells.encode Finset.univ (Function.update values instruction.core.destination (evaluate instruction values)) := by
  change (CellEffects.profile [P1Scalar.recipe (p1 instruction) instruction.core.destination]).theory.rewrites
    (Cells.encode Finset.univ values) following ↔ _
  rw [P1Scalar.rewrite_iff]
  simp only [X86P1Arithmetic.computes,Option.some.injEq,Finset.subset_univ,true_and]
  constructor
  · rintro ⟨result,same,endpoint⟩
    cases same
    exact endpoint
  · intro endpoint
    exact ⟨evaluate instruction values,rfl,endpoint⟩

noncomputable def spec : X86BlockCompiler.Spec Instruction World where
  action := action
  represents := X86WordLibrary.represents
  ready := X86WordLibrary.ready
  bytes := bytes
  count := count
  registerWrites := X86WordLibrary.registers
  byteWrites := ∅

theorem physical_copy (register : Fin 12) : physical register = X86CopyBlock.physical register :=
  X86P1ArithmeticCore.physical_copy register

theorem writes_included (instruction : Instruction) : writes instruction ⊆ X86WordLibrary.registers :=
  X86WordLibrary.binary_clobbers instruction.core.destination instruction.core.unlocked

theorem other_logical (instruction : Instruction) (register : Fin 12)
    (apart : register ≠ instruction.core.destination) : key (physical register) ∉ writes instruction :=
  X86WordPrimitive.other_logical
    (.binary 1 instruction.core.destination instruction.core.left instruction.core.right instruction.core.unlocked)
    register apart

theorem correct (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86P1Arithmetic.handlers other extra
    letI : VectorOpcodeHandlers := vector
    X86BlockCompiler.Correct spec := by
  let : OtherOpcodeHandlers := X86P1Arithmetic.handlers other extra
  let : VectorOpcodeHandlers := vector
  refine { dataOnly := X86WordLibrary.data_only, execute := ?_ }
  intro instruction source following native origin _ step represented prepared upper loaded _
  obtain ⟨values,sourceEq,registersKnown⟩ := represented
  subst source
  have followingEq := (source_step_iff instruction values following).mp step
  obtain ⟨flags,flagsKnown,quiet⟩ := prepared
  have known (register : Fin 12) : lookup native (physical register) = some (values register) := by
    rw [physical_copy]
    exact registersKnown register (Finset.mem_univ _)
  obtain ⟨after,nextFlags,run,frame,result,rip,nextKnown,nextQuiet,_,prefixes⟩ :=
    X86P1Arithmetic.executes other extra vector instruction values native origin
      (known instruction.core.left) (known instruction.core.right) flags flagsKnown quiet
      (by simpa [spec,Int.add_assoc] using upper) loaded
  refine ⟨after,run,(X86StateFrame.registerOnly frame).mono (writes_included instruction) (Finset.Subset.refl _),
    ⟨Function.update values instruction.core.destination (evaluate instruction values),followingEq,?_⟩,
    ⟨nextFlags,nextKnown,nextQuiet⟩,rip,?_⟩
  · intro register member
    change lookup after (X86CopyBlock.physical register) =
      some ((Function.update values instruction.core.destination (evaluate instruction values)) register)
    by_cases same : register = instruction.core.destination
    · subst register
      simpa only [Function.update_self,physical_copy] using result
    · rw [Function.update_of_ne same]
      have retained := frame.lookup (physical register) (other_logical instruction register same)
      rw [physical_copy] at retained
      exact retained.trans (registersKnown register member)
  · intro prefixCount within observed candidate
    exact (X86StateFrame.registerOnly (prefixes prefixCount within observed candidate)).mono
      (writes_included instruction) (Finset.Subset.refl _)

theorem source_wp_step (instruction : Instruction) (values : Fin 12 → Word)
    (post : Unit → World → Prop)
    (expected : post () (Cells.encode Finset.univ
      (Function.update values instruction.core.destination (evaluate instruction values)))) :
    (Prog.prim instruction).wp action post (Cells.encode Finset.univ values) := by
  apply (wp_prim action instruction post _).mpr
  let after := Function.update values instruction.core.destination (evaluate instruction values)
  have guarded : (effect instruction).guard ((effect instruction).inputs.map values)
      ((effect instruction).outputs.map after) = true := by
    apply (P1Scalar.guard_iff _ _ _ _).mpr
    simpa only [after,Function.update_self] using X86P1Arithmetic.computes instruction values
  obtain ⟨invocation,enabled,_⟩ := CellEffects.effect_realized (effect instruction) Finset.univ values after
    (Finset.subset_univ _) guarded
  refine ⟨⟨invocation,enabled⟩,?_⟩
  intro _ following step
  rw [(source_step_iff instruction values following).mp step]
  exact expected

theorem compile_wp (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (stop : Int) (program : X86BlockCompiler.Program Instruction) (source : World) (native : State)
    (input : X86BlockCompiler.At spec stop program source native) (post : Unit → World → Prop)
    (wp : program.wp action post source) :
    letI : OtherOpcodeHandlers := X86P1Arithmetic.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ following after, program.Runs action source () following ∧ post () following ∧
      (X86FuelPrefix.fetches (X86BlockCompiler.steps spec program)).run native = .ok () after ∧
      X86StateFrame.Frame spec.registerWrites spec.byteWrites native after ∧
      X86BlockCompiler.Observed spec stop () following after := by
  let : OtherOpcodeHandlers := X86P1Arithmetic.handlers other extra
  let : VectorOpcodeHandlers := vector
  exact X86BlockCompiler.compile_wp spec (correct other extra vector) progress stop program source native input post wp

#print axioms correct
#print axioms source_wp_step
#print axioms compile_wp
end Mettapedia.Machines.TIsa.X86P1ArithmeticLibrary
