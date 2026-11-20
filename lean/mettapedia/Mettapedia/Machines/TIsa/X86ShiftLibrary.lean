import Mettapedia.Machines.TIsa.X86TypedShiftBlock
import Mettapedia.Machines.TIsa.X86ShiftBlock
import Mettapedia.Machines.TIsa.X86LibrarySum

/-!
# U64, U32Z and I32S shifts in the common native block compiler

The source action is the existing p1 finite-resource recipe. Concrete template
proofs supply exact fetched counts, readiness, register results and prefix
frames. The common compiler then supplies code layout, sequencing and WP.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86ShiftLibrary
open _root_.X86Registers X86RegisterRefinement X86Execution
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev Instruction := Sum X86ShiftBlock.Instruction X86TypedShiftBlock.Instruction
abbrev World := X86WordLibrary.World
abbrev physical := X86WordPrimitive.physical

theorem physical_copy (register : Fin 12) : physical register = X86CopyBlock.physical register :=
  X86WordPrimitive.physical_copy register

def p1 : Instruction → P1Source.Instr
  | .inl instruction => X86ShiftBlock.p1 instruction
  | .inr instruction => X86TypedShiftBlock.p1 instruction

def lower? (source : P1Source.Instr) : Option Instruction :=
  match X86ShiftBlock.lower? source with
  | some instruction => some (.inl instruction)
  | none => (X86TypedShiftBlock.lower? source).map Sum.inr

theorem lower?_roundtrip (instruction : Instruction) : lower? (p1 instruction) = some instruction := by
  cases instruction with
  | inl instruction =>
    simp only [p1,lower?,X86ShiftBlock.lower?_roundtrip]
  | inr instruction =>
    have narrow : X86ShiftBlock.lower? (X86TypedShiftBlock.p1 instruction) = none := by
      cases selected : instruction.signed <;> simp [X86ShiftBlock.lower?,X86TypedShiftBlock.p1,selected]
    simp only [p1,lower?,narrow,X86TypedShiftBlock.lower?_roundtrip,Option.map_some]

theorem lower?_source {source : P1Source.Instr} {instruction : Instruction}
    (accepted : lower? source = some instruction) : p1 instruction = source := by
  cases wide : X86ShiftBlock.lower? source with
  | some actual =>
    simp only [lower?,wide,Option.some.injEq] at accepted
    subst instruction
    exact X86ShiftBlock.lower?_source wide
  | none =>
    cases narrow : X86TypedShiftBlock.lower? source with
    | none => simp [lower?,wide,narrow] at accepted
    | some actual =>
      simp only [lower?,wide,narrow,Option.map_some,Option.some.injEq] at accepted
      subst instruction
      exact X86TypedShiftBlock.lower?_source narrow

theorem count32_narrow_refused (operation : Shift) (signed : Bool) (destination source : Fin 12) :
    lower? (.shift operation (if signed then .i32s else .u32z) destination source 32) = none := by
  cases signed <;> simp [lower?,X86ShiftBlock.lower?,X86TypedShiftBlock.lower?]

theorem count64_wide_refused (operation : Shift) (destination source : Fin 12) :
    lower? (.shift operation .u64 destination source 64) = none := by
  simp [lower?,X86ShiftBlock.lower?,X86TypedShiftBlock.lower?]

def destination : Instruction → Fin 12
  | .inl instruction => instruction.destination
  | .inr instruction => instruction.destination

def sourceRegister : Instruction → Fin 12
  | .inl instruction => instruction.source
  | .inr instruction => instruction.source

def evaluate : Instruction → (Fin 12 → Word) → Word
  | .inl instruction => X86ShiftBlock.evaluate instruction
  | .inr instruction => X86TypedShiftBlock.evaluate instruction

def bytes : Instruction → List Nat
  | .inl instruction => X86ShiftBlock.bytes instruction
  | .inr instruction => X86TypedShiftBlock.bytes instruction

def count : Instruction → Nat
  | .inl instruction => X86ShiftBlock.count instruction
  | .inr instruction => X86TypedShiftBlock.count instruction

def writes : Instruction → Finset Register
  | .inl instruction => X86ShiftBlock.writes instruction
  | .inr instruction => X86TypedShiftBlock.writes instruction

def effect (instruction : Instruction) : CellEffects.Recipe (Fin 12) :=
  P1Scalar.recipe (p1 instruction) (destination instruction)

def action (instruction : Instruction) : Mettapedia.GSLT.Logic.AbstractSeparationLogic.Action World Unit where
  Safe world := ∃ invocation : CellEffects.Invocation (effect instruction),
    CellEffects.system.Enables world invocation
  Step world _ after := (CellEffects.profile [effect instruction]).theory.rewrites world after

theorem progress (instruction : Instruction) : (action instruction).Progress := by
  rintro world ⟨invocation,enabled⟩
  exact ⟨(),CellEffects.system.fire world invocation,ULift.up (0 : Fin 1),invocation,enabled,rfl⟩

theorem computes (instruction : Instruction) (values : Fin 12 → Word) :
    P1Scalar.evaluate (p1 instruction) ((p1 instruction).reads.map values) = some (evaluate instruction values) := by
  cases instruction with
  | inl instruction =>
    rw [p1,←X86ShiftBlock.source_evaluate_p1,evaluate]
    exact X86ShiftBlock.computes instruction values
  | inr instruction => exact X86TypedShiftBlock.computes instruction values

theorem source_step_iff (instruction : Instruction) (values : Fin 12 → Word) (following : World) :
    (action instruction).Step (Cells.encode Finset.univ values) () following ↔
      following = Cells.encode Finset.univ (Function.update values (destination instruction) (evaluate instruction values)) := by
  change (CellEffects.profile [P1Scalar.recipe (p1 instruction) (destination instruction)]).theory.rewrites
    (Cells.encode Finset.univ values) following ↔ _
  rw [P1Scalar.rewrite_iff]
  simp only [computes,Option.some.injEq,Finset.subset_univ,true_and]
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

theorem old_handlers_agree (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :
    X86ShiftBlock.handlers (X86Extend32.linkedHandlers other) extra = X86TypedShiftBlock.handlers other extra := rfl

theorem other_logical (instruction : Instruction) (register : Fin 12)
    (apart : register ≠ destination instruction) : key (physical register) ∉ writes instruction := by
  cases instruction with
  | inl instruction => exact X86ShiftBlock.other_logical instruction register apart
  | inr instruction => exact X86TypedShiftBlock.other_logical instruction register apart

theorem writes_included (instruction : Instruction) : writes instruction ⊆ X86WordLibrary.registers := by
  cases instruction with
  | inl instruction => exact X86WordLibrary.binary_clobbers _ instruction.unlocked
  | inr instruction => exact X86WordLibrary.binary_clobbers _ instruction.unlocked

theorem correct (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
    letI : VectorOpcodeHandlers := vector
    X86BlockCompiler.Correct spec := by
  let : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
  let : VectorOpcodeHandlers := vector
  refine { dataOnly := X86WordLibrary.data_only, execute := ?_ }
  intro instruction source following native origin _ step represented prepared upper loaded _
  obtain ⟨values,sourceEq,registersKnown⟩ := represented
  subst source
  have followingEq := (source_step_iff instruction values following).mp step
  obtain ⟨flags,flagsKnown,quiet⟩ := prepared
  have known : lookup native (physical (sourceRegister instruction)) = some (values (sourceRegister instruction)) := by
    rw [physical_copy]
    exact registersKnown _ (Finset.mem_univ _)
  have actualUpper : origin.address.toInt + (bytes instruction).length + 3 < (2 ^ 47 : Int) := by
    simpa [spec,Int.add_assoc] using upper
  have actual : ∃ after nextFlags,
      (X86FuelPrefix.fetches (count instruction)).run native = .ok () after ∧
      RegisterFrame (writes instruction) native after ∧
      lookup after (physical (destination instruction)) = some (evaluate instruction values) ∧
      after.regs.get? .rip = some ((address origin.address.toInt (bytes instruction).length).signExtend 64) ∧
      after.regs.get? .rflags = some nextFlags ∧ after.regs.get? .log_register_writes = some false ∧
      X86ControlFlags.Preserved native after ∧
      ∀ prefixCount ≤ count instruction, ∀ observed,
        (X86FuelPrefix.fetches prefixCount).run native = .ok () observed →
          RegisterFrame (writes instruction) native observed := by
    cases instruction with
    | inl instruction =>
      have run := X86ShiftBlock.executes_block (X86Extend32.linkedHandlers other) extra vector
        instruction values native origin known flags flagsKnown quiet actualUpper loaded
      rw [old_handlers_agree] at run
      exact run
    | inr instruction =>
      exact X86TypedShiftBlock.executes_block other extra vector instruction values native origin known
        flags flagsKnown quiet (by
          change origin.address.toInt + (X86TypedShiftBlock.bytes instruction).length + 3 < _ at actualUpper
          omega) loaded
  obtain ⟨after,nextFlags,run,frame,result,rip,nextKnown,nextQuiet,_,prefixes⟩ := actual
  refine ⟨after,run,(X86StateFrame.registerOnly frame).mono (writes_included instruction) (Finset.Subset.refl _),
    ⟨Function.update values (destination instruction) (evaluate instruction values),followingEq,?_⟩,
    ⟨nextFlags,nextKnown,nextQuiet⟩,rip,?_⟩
  · intro register member
    change lookup after (X86CopyBlock.physical register) =
      some ((Function.update values (destination instruction) (evaluate instruction values)) register)
    by_cases same : register = destination instruction
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
    (expected : post () (Cells.encode Finset.univ (Function.update values (destination instruction) (evaluate instruction values)))) :
    (Prog.prim instruction).wp action post (Cells.encode Finset.univ values) := by
  apply (wp_prim action instruction post _).mpr
  let after := Function.update values (destination instruction) (evaluate instruction values)
  have guarded : (effect instruction).guard ((effect instruction).inputs.map values)
      ((effect instruction).outputs.map after) = true := by
    apply (P1Scalar.guard_iff _ _ _ _).mpr
    simpa only [after,Function.update_self] using computes instruction values
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
    letI : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ following after, program.Runs action source () following ∧ post () following ∧
      (X86FuelPrefix.fetches (X86BlockCompiler.steps spec program)).run native = .ok () after ∧
      X86StateFrame.Frame spec.registerWrites spec.byteWrites native after ∧
      X86BlockCompiler.Observed spec stop () following after := by
  let : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
  let : VectorOpcodeHandlers := vector
  exact X86BlockCompiler.compile_wp spec (correct other extra vector) progress stop program source native input post wp

#print axioms lower?_roundtrip
#print axioms lower?_source
#print axioms count32_narrow_refused
#print axioms count64_wide_refused
#print axioms source_step_iff
#print axioms correct
#print axioms source_wp_step
#print axioms compile_wp
end Mettapedia.Machines.TIsa.X86ShiftLibrary
