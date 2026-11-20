import Mettapedia.Machines.TIsa.X86BranchCompiler
import Mettapedia.Machines.TIsa.X86BlockCompiler

/-!
# Adjacent guarded source branches in one generated region

The region owns each boundary marker once. Bare operation bodies share the
assembler's label environment. The first true continuation enters the second
source branch; native readiness is derived from the first execution's frame,
flags and retained image rather than supplied as a second execution premise.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86BranchRegion
open _root_.X86Registers X86RegisterRefinement X86Execution X86Assembler X86BranchCompiler
local instance : MemoryPrimitives := X86Memory.ordinary
universe u
variable {Key : Type u}

def secondFirst (first : List Chunk) (left : Control.Branch Key) (register : Fin 16) : List Chunk :=
  first ++ (.label left.point.toNat :: body left register)

def firstTail (right : Control.Branch Key) (register : Fin 16) (tail : List Chunk) : List Chunk :=
  body right register ++ (.label right.yes.toNat :: tail)

def program (first : List Chunk) (left right : Control.Branch Key) (leftReg rightReg : Fin 16)
    (tail : List Chunk) : List Chunk :=
  secondFirst first left leftReg ++ (lower right rightReg ++ tail)

theorem second_width (first : List Chunk) (left : Control.Branch Key) (register : Fin 16) :
    width (secondFirst first left register) = width first + 9 := by
  simp [secondFirst,width_append,width,Chunk.width,body_width]

theorem first_view (first : List Chunk) (left right : Control.Branch Key) (leftReg rightReg : Fin 16)
    (tail : List Chunk) (flow : left.yes = right.point) :
    program first left right leftReg rightReg tail =
      first ++ (lower left leftReg ++ firstTail right rightReg tail) := by
  simp [program,secondFirst,firstTail,lower,flow,List.append_assoc]

theorem system_step_in [DecidableEq Key] (recipes : List (CellEffects.Recipe (Control.Location Key)))
    (recipe : CellEffects.Recipe (Control.Location Key)) (member : recipe ∈ recipes)
    (invocation : CellEffects.Invocation recipe) (keys : Finset (Control.Location Key))
    (before : Control.Location Key → Word) (result : Multiset (Cells.Cell (Control.Location Key)))
    (enabled : CellEffects.system.Enables (Cells.encode keys before) invocation)
    (fired : CellEffects.system.fire (Cells.encode keys before) invocation = result) :
    (CellEffects.profile recipes).theory.rewrites (Cells.encode keys before) result := by
  obtain ⟨index,rfl⟩ := List.mem_iff_get.mp member
  exact ⟨ULift.up index,invocation,enabled,fired.symm⟩

theorem source_in [DecidableEq Key] [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    {branch : Control.Branch Key} {register : Fin 16} {first tail : List Chunk} {emission : Emission}
    {native after : State} {compiled : Compilation branch register first tail emission}
    {entry : Entry register (width first) emission native} {keys : Finset (Control.Location Key)}
    {before : Control.Location Key → Word} (correct : X86BranchCompiler.Result compiled entry keys before after)
    (recipes : List (CellEffects.Recipe (Control.Location Key))) (member : branch.recipe ∈ recipes) :
    (CellEffects.profile recipes).theory.rewrites (Cells.encode keys before)
      (Cells.encode keys (Function.update before (.inl branch.activation) (chosen branch entry.value))) := by
  obtain ⟨invocation,enabled,fired⟩ := correct.source
  exact system_step_in recipes branch.recipe member invocation keys before _ enabled fired

theorem fallthrough [DecidableEq Key] (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (first tail : List Chunk) (left right : Control.Branch Key) (leftReg rightReg : Fin 16)
    (emission : Emission) (assembled : assemble (program first left right leftReg rightReg tail) = some emission)
    (owner : left.activation = right.activation) (flow : left.yes = right.point)
    (native : State) (entry : Entry leftReg (width first) emission native)
    (keys : Finset (Control.Location Key)) (before : Control.Location Key → Word)
    (leftSupport : left.recipe.support ⊆ keys) (rightSupport : right.recipe.support ⊆ keys)
    (current : before (.inl left.activation) = left.point)
    (leftRead : before (.inr left.condition) = entry.value) (taken : entry.value = 1)
    (rightValue : Word) (rightRead : before (.inr right.condition) = rightValue)
    (rightKnown : X86RegisterRefinement.lookup native rightReg = some rightValue)
    (rightCanonical : rightValue = 0 ∨ rightValue = 1) :
    letI : OtherOpcodeHandlers := X86BranchGate.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ middle after labels target,
      (CellEffects.profile [left.recipe,right.recipe]).theory.rewrites (Cells.encode keys before)
        (Cells.encode keys (Function.update before (.inl left.activation) left.yes)) ∧
      (CellEffects.profile [left.recipe,right.recipe]).theory.rewrites
        (Cells.encode keys (Function.update before (.inl left.activation) left.yes))
        (Cells.encode keys (Function.update (Function.update before (.inl left.activation) left.yes)
          (.inl right.activation) (chosen right rightValue))) ∧
      (X86FuelPrefix.fetches 2).run native = .ok () middle ∧
      (X86FuelPrefix.fetches 2).run middle = .ok () after ∧
      (X86FuelPrefix.fetches 4).run native = .ok () after ∧
      RegisterFrame X86BranchGate.writes native after ∧
      X86CodePlacement.Placed after entry.base (X86Assembler.view emission.bytes) ∧
      X86ControlFlags.Preserved native after ∧
      labelsAt 0 (program first left right leftReg rightReg tail) = some labels ∧
      X86Assembler.lookup labels (chosen right rightValue).toNat = some target ∧
      after.regs.get? .rip = some ((address entry.base target).signExtend 64) ∧
      ∀ count ≤ 4, ∀ observed, (X86FuelPrefix.fetches count).run native = .ok () observed →
        RegisterFrame X86BranchGate.writes native observed := by
  let : OtherOpcodeHandlers := X86BranchGate.handlers other extra
  let : VectorOpcodeHandlers := vector
  have leftAssembly : assemble (first ++ (lower left leftReg ++ firstTail right rightReg tail)) = some emission := by
    rw [← first_view first left right leftReg rightReg tail flow]
    exact assembled
  obtain ⟨leftCompiled,middle,leftCorrect⟩ := X86BranchCompiler.realizes other extra vector left leftReg first
    (firstTail right rightReg tail) emission leftAssembly native entry keys before leftSupport current leftRead (Or.inr taken)
  have nonzero : entry.value ≠ (0#64) := by rw [taken]; decide
  have nextStart : chosenOffset leftCompiled entry.value = width (secondFirst first left leftReg) := by
    rw [chosenOffset,if_neg nonzero,second_width]
  obtain ⟨resumed,sameBase,sameValue⟩ := leftCorrect.next_entry rightReg rightValue rightKnown
  have ready : ∃ next : Entry rightReg (width (secondFirst first left leftReg)) emission middle,
      next.base = entry.base ∧ next.value = rightValue := by
    rw [← nextStart]
    exact ⟨resumed,sameBase,sameValue⟩
  obtain ⟨nextEntry,nextBase,nextValue⟩ := ready
  have nextCurrent : (Function.update before (.inl left.activation) left.yes) (.inl right.activation) = right.point := by
    rw [owner,Function.update_self,flow]
  have nextRead : (Function.update before (.inl left.activation) left.yes) (.inr right.condition) = nextEntry.value := by
    rw [Function.update_of_ne (by simp),rightRead,nextValue]
  obtain ⟨rightCompiled,after,rightCorrect⟩ := X86BranchCompiler.realizes other extra vector right rightReg
    (secondFirst first left leftReg) tail emission assembled middle nextEntry keys
    (Function.update before (.inl left.activation) left.yes) rightSupport nextCurrent nextRead
    (by rw [nextValue]; exact rightCanonical)
  have leftSource := source_in leftCorrect [left.recipe,right.recipe] (by simp)
  have rightSource := source_in rightCorrect [left.recipe,right.recipe] (by simp)
  rw [chosen,if_neg nonzero] at leftSource
  rw [nextValue] at rightSource
  have rightLabel := rightCorrect.outputLabel
  have rightPointer := rightCorrect.pointer
  rw [nextValue] at rightLabel
  rw [nextBase,nextValue] at rightPointer
  have full := X86FuelPrefix.fetches_then 2 2 native middle after leftCorrect.run rightCorrect.run
  refine ⟨middle,after,rightCompiled.labels,chosenOffset rightCompiled rightValue,
    leftSource,rightSource,leftCorrect.run,rightCorrect.run,full,
    (leftCorrect.frame.trans rightCorrect.frame).mono (by simp),?_,leftCorrect.control.trans rightCorrect.control,
    rightCompiled.resolved,rightLabel,rightPointer,?_⟩
  · rw [← nextBase]
    exact rightCorrect.image
  · intro count within observed candidate
    by_cases early : count ≤ 2
    · exact leftCorrect.prefixes count early observed candidate
    · have total : count = 2 + (count - 2) := by omega
      rw [total] at candidate
      obtain ⟨intermediate,firstRun,rest⟩ := X86BlockCompiler.fetches_split 2 (count - 2) native observed candidate
      have same := X86FuelPrefix.fetches_deterministic 2 native middle intermediate leftCorrect.run firstRun
      subst intermediate
      exact (leftCorrect.frame.trans (rightCorrect.prefixes (count - 2) (by omega) observed rest)).mono (by simp)

/-- An untaken continuation requires no resources or register value for the skipped branch. -/
theorem early_exit [DecidableEq Key] (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (first tail : List Chunk) (left right : Control.Branch Key) (leftReg rightReg : Fin 16)
    (emission : Emission) (assembled : assemble (program first left right leftReg rightReg tail) = some emission)
    (flow : left.yes = right.point) (native : State) (entry : Entry leftReg (width first) emission native)
    (keys : Finset (Control.Location Key)) (before : Control.Location Key → Word)
    (support : left.recipe.support ⊆ keys) (current : before (.inl left.activation) = left.point)
    (reads : before (.inr left.condition) = entry.value) (zero : entry.value = (0#64)) :
    letI : OtherOpcodeHandlers := X86BranchGate.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after labels target,
      (CellEffects.profile [left.recipe,right.recipe]).theory.rewrites (Cells.encode keys before)
        (Cells.encode keys (Function.update before (.inl left.activation) left.no)) ∧
      (X86FuelPrefix.fetches 2).run native = .ok () after ∧
      RegisterFrame X86BranchGate.writes native after ∧
      X86CodePlacement.Placed after entry.base (view emission.bytes) ∧
      X86ControlFlags.Preserved native after ∧
      labelsAt 0 (program first left right leftReg rightReg tail) = some labels ∧
      X86Assembler.lookup labels left.no.toNat = some target ∧
      after.regs.get? .rip = some ((address entry.base target).signExtend 64) ∧
      ∀ count ≤ 2, ∀ observed, (X86FuelPrefix.fetches count).run native = .ok () observed →
        RegisterFrame X86BranchGate.writes native observed := by
  let : OtherOpcodeHandlers := X86BranchGate.handlers other extra
  let : VectorOpcodeHandlers := vector
  have leftAssembly : assemble (first ++ (lower left leftReg ++ firstTail right rightReg tail)) = some emission := by
    rw [← first_view first left right leftReg rightReg tail flow]
    exact assembled
  obtain ⟨compiled,after,correct⟩ := X86BranchCompiler.realizes other extra vector left leftReg first
    (firstTail right rightReg tail) emission leftAssembly native entry keys before support current reads (Or.inl zero)
  have source := source_in correct [left.recipe,right.recipe] (by simp)
  have output := correct.outputLabel
  rw [chosen,if_pos zero] at source output
  refine ⟨after,compiled.labels,chosenOffset compiled entry.value,source,correct.run,correct.frame,
    correct.image,correct.control,?_,output,correct.pointer,correct.prefixes⟩
  rw [first_view first left right leftReg rightReg tail flow]
  exact compiled.resolved

end Mettapedia.Machines.TIsa.X86BranchRegion
