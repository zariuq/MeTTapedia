import Mettapedia.Machines.TIsa.X86ScalarLibrary
import Mettapedia.Machines.TIsa.LibraryLowering

/-!
# Three-register logical operations from certified native components

The source operation is the existing p1 U64 computation over initialized
register values. Its implementation uses the established cell-resource
actions and native copy/logical templates. When the right operand aliases
the destination, commutativity avoids overwriting that operand with a copy.

Library expansion preserves both outcomes and definedness. Native compilation
retains the existing code-placement, readiness, frame and exact-count
contracts. Admission and the public call boundary remain separate obligations.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86LogicalRecipes
open _root_.X86Registers X86RegisterRefinement X86Execution
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev Values := Fin 12 → Word
abbrev World := X86ScalarLibrary.World
abbrev Low := X86ScalarLibrary.Instruction

structure Instruction where
  operation : X86LogicalWord.Kind
  destination : Fin 12
  left : Fin 12
  right : Fin 12
  unlocked : destination ≠ 0

def p1 (instruction : Instruction) : P1Source.Instr :=
  .binary (X86LogicalLibrary.binary instruction.operation) .u64
    instruction.destination instruction.left instruction.right

def lower? : P1Source.Instr → Option Instruction
  | .binary .bor .u64 destination left right =>
      if unlocked : destination ≠ 0 then some ⟨.or,destination,left,right,unlocked⟩ else none
  | .binary .band .u64 destination left right =>
      if unlocked : destination ≠ 0 then some ⟨.and,destination,left,right,unlocked⟩ else none
  | .binary .bxor .u64 destination left right =>
      if unlocked : destination ≠ 0 then some ⟨.xor,destination,left,right,unlocked⟩ else none
  | _ => none

theorem lower?_roundtrip (instruction : Instruction) : lower? (p1 instruction) = some instruction := by
  rcases instruction with ⟨operation,destination,left,right,unlocked⟩
  cases operation <;> simp [p1,lower?,X86LogicalLibrary.binary,unlocked]

theorem lower?_source {source : P1Source.Instr} {instruction : Instruction}
    (accepted : lower? source = some instruction) : p1 instruction = source := by
  cases source <;> simp [lower?] at accepted
  case binary operation ty destination left right =>
    cases operation <;> cases ty <;> simp at accepted
    all_goals obtain ⟨_unlocked,rfl⟩ := accepted; rfl

def evaluate (instruction : Instruction) (values : Values) : Word :=
  X86LogicalWord.result instruction.operation (values instruction.left) (values instruction.right)

def updated (instruction : Instruction) (values : Values) : Values :=
  Function.update values instruction.destination (evaluate instruction values)

theorem computes (instruction : Instruction) (values : Values) :
    P1Scalar.evaluate (p1 instruction) ((p1 instruction).reads.map values) =
      some (evaluate instruction values) := by
  rcases instruction with ⟨operation,destination,left,right,unlocked⟩
  cases operation <;> rfl

def action (instruction : Instruction) : Action Values Unit where
  Safe values := P1Scalar.evaluate (p1 instruction) ((p1 instruction).reads.map values) =
    some (evaluate instruction values)
  Step values _ following := following = updated instruction values

theorem progress (instruction : Instruction) : (action instruction).Progress := by
  intro values _
  exact ⟨(),updated instruction values,rfl⟩

def related (values : Values) (world : World) : Prop := world = Cells.encode Finset.univ values

def copy (instruction : Instruction) : Low :=
  .inl (.copy ⟨instruction.left,instruction.destination,instruction.unlocked⟩)

def logical (instruction : Instruction) (source : Fin 12) : Low :=
  .inr ⟨instruction.operation,source,instruction.destination,instruction.unlocked⟩

def copyThenLogical (instruction : Instruction) : X86ScalarLibrary.Program :=
  (Prog.prim (copy instruction)).bind (fun _ => Prog.prim (logical instruction instruction.right))

def implementation (instruction : Instruction) : X86ScalarLibrary.Program :=
  if instruction.right = instruction.destination then Prog.prim (logical instruction instruction.left)
  else copyThenLogical instruction

theorem result_comm (operation : X86LogicalWord.Kind) (left right : Word) :
    X86LogicalWord.result operation left right = X86LogicalWord.result operation right left := by
  cases operation <;> simp only [X86LogicalWord.result,BitVec.or_comm,BitVec.and_comm,BitVec.xor_comm]

theorem logical_wp (instruction : Instruction) (source : Fin 12) (values : Values)
    (post : Unit → World → Prop)
    (expected : post () (Cells.encode Finset.univ (Function.update values instruction.destination
      (X86LogicalWord.result instruction.operation (values instruction.destination) (values source))))) :
    (Prog.prim (logical instruction source)).wp X86ScalarLibrary.spec.action post
      (Cells.encode Finset.univ values) := by
  exact X86ScalarLibrary.source_wp_step (logical instruction source) values _
    (X86LogicalLibrary.source_computes
      ⟨instruction.operation,source,instruction.destination,instruction.unlocked⟩ values) post expected

theorem copy_then_logical_wp (instruction : Instruction) (values : Values)
    (post : Unit → World → Prop)
    (expected : post () (Cells.encode Finset.univ (Function.update values instruction.destination
      (X86LogicalWord.result instruction.operation (values instruction.left)
        ((Function.update values instruction.destination (values instruction.left)) instruction.right))))) :
    (copyThenLogical instruction).wp X86ScalarLibrary.spec.action post (Cells.encode Finset.univ values) := by
  rw [copyThenLogical,wp_bind]
  apply X86ScalarLibrary.source_wp_step (copy instruction) values (values instruction.left) rfl
  apply logical_wp
  change post () (Cells.encode Finset.univ (Function.update
    (Function.update values instruction.destination (values instruction.left)) instruction.destination
    (X86LogicalWord.result instruction.operation
      ((Function.update values instruction.destination (values instruction.left)) instruction.destination)
      ((Function.update values instruction.destination (values instruction.left)) instruction.right))))
  simpa only [Function.update_self,Function.update_idem] using expected

theorem implementation_wp (instruction : Instruction) (values : Values) :
    (implementation instruction).wp X86ScalarLibrary.spec.action
      (fun _ world => related (updated instruction values) world) (Cells.encode Finset.univ values) := by
  unfold implementation
  split
  · rename_i aliases
    apply logical_wp
    change Cells.encode Finset.univ (Function.update values instruction.destination
      (X86LogicalWord.result instruction.operation (values instruction.destination) (values instruction.left))) = _
    rw [result_comm]
    simp only [updated,evaluate,aliases]
  · rename_i separate
    apply copy_then_logical_wp
    simp only [Function.update_of_ne separate]
    rfl

theorem correct : LibraryLowering.Correct action X86ScalarLibrary.spec.action related implementation where
  defined := by
    intro instruction source target represented
    change target = Cells.encode Finset.univ source at represented
    subst target
    exact ⟨fun _ => (implementation_wp instruction source).1,fun _ => computes instruction source⟩
  complete := by
    rintro instruction source target ⟨⟩ following represented step
    change target = Cells.encode Finset.univ source at represented
    subst target
    change following = updated instruction source at step
    subst following
    have verified := implementation_wp instruction source
    obtain ⟨⟨⟩,after,run⟩ := (implementation instruction).exists_runs
      X86ScalarLibrary.spec.action X86ScalarLibrary.progress _ verified.1
    exact ⟨after,run,verified.2 () after run⟩
  sound := by
    rintro instruction source target ⟨⟩ after represented run
    change target = Cells.encode Finset.univ source at represented
    subst target
    exact ⟨updated instruction source,rfl,(implementation_wp instruction source).2 () after run⟩

abbrev Program := Prog Instruction (fun _ => Unit) Unit

theorem compile_wp (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (stop : Int) (program : Program) (values : Values) (native : State)
    (input : X86BlockCompiler.At X86ScalarLibrary.spec stop
      (LibraryLowering.expand implementation program) (Cells.encode Finset.univ values) native)
    (post : Unit → Values → Prop) (wp : program.wp action post values) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ following after, program.Runs action values () following ∧ post () following ∧
      (X86FuelPrefix.fetches (X86BlockCompiler.steps X86ScalarLibrary.spec
        (LibraryLowering.expand implementation program))).run native = .ok () after ∧
      X86StateFrame.Frame X86ScalarLibrary.spec.registerWrites X86ScalarLibrary.spec.byteWrites native after ∧
      X86BlockCompiler.Observed X86ScalarLibrary.spec stop () (Cells.encode Finset.univ following) after := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have represented : related values (Cells.encode Finset.univ values) := rfl
  have lowWP : (LibraryLowering.expand implementation program).wp X86ScalarLibrary.spec.action
      (fun _ world => ∃ following, program.Runs action values () following ∧
        post () following ∧ related following world) (Cells.encode Finset.univ values) := by
    refine ⟨(correct.safe_iff program values _ represented).mp wp.1,?_⟩
    rintro ⟨⟩ world run
    obtain ⟨following,sourceRun,followingRelated⟩ := correct.reflects program values _ world () represented run
    exact ⟨following,sourceRun,wp.2 () following sourceRun,followingRelated⟩
  obtain ⟨world,after,_run,⟨following,sourceRun,postHolds,worldEq⟩,executed,frame,observed⟩ :=
    X86ScalarLibrary.compile_wp other vector stop _ _ native input _ lowWP
  change world = Cells.encode Finset.univ following at worldEq
  subst world
  exact ⟨following,after,sourceRun,postHolds,executed,frame,observed⟩

namespace Controls

def values (register : Fin 12) : Word :=
  if register = 1 then 1 else if register = 2 then 2 else 0

def rightAlias : Instruction := ⟨.xor,2,1,2,by decide⟩
def leftAlias : Instruction := ⟨.xor,1,1,2,by decide⟩
def separate : Instruction := ⟨.xor,3,1,2,by decide⟩

theorem right_alias : evaluate rightAlias values = 3 ∧
    implementation rightAlias = Prog.prim (logical rightAlias 1) := by
  exact ⟨by decide,rfl⟩

theorem alias_and_separate_counts :
    X86BlockCompiler.steps X86ScalarLibrary.spec (implementation rightAlias) = 1 ∧
    X86BlockCompiler.steps X86ScalarLibrary.spec (implementation leftAlias) = 1 ∧
    X86BlockCompiler.steps X86ScalarLibrary.spec (implementation separate) = 2 := by decide

theorem lowering_guards : lower? (p1 rightAlias) = some rightAlias ∧
    lower? (.binary .bxor .u64 0 1 2) = none ∧
    lower? (.binary .bxor .u32z 2 1 2) = none := by
  exact ⟨lower?_roundtrip rightAlias,by decide,by decide⟩

theorem overwritten_right_operand :
    ∃ after, (copyThenLogical rightAlias).Runs X86ScalarLibrary.spec.action
      (Cells.encode Finset.univ values) () after ∧
      after = Cells.encode Finset.univ (Function.update values 2 0) := by
  have verified : (copyThenLogical rightAlias).wp X86ScalarLibrary.spec.action
      (fun _ after => after = Cells.encode Finset.univ (Function.update values 2 0))
      (Cells.encode Finset.univ values) := by
    apply copy_then_logical_wp
    rfl
  obtain ⟨⟨⟩,after,run⟩ := (copyThenLogical rightAlias).exists_runs
    X86ScalarLibrary.spec.action X86ScalarLibrary.progress _ verified.1
  exact ⟨after,run,verified.2 () after run⟩

theorem copy_first_alias_is_incorrect :
    ¬ LibraryLowering.Correct action X86ScalarLibrary.spec.action related copyThenLogical := by
  intro claimed
  obtain ⟨after,run,bad⟩ := overwritten_right_operand
  obtain ⟨following,step,represented⟩ := claimed.sound rightAlias values
    (Cells.encode Finset.univ values) () after rfl run
  change following = updated rightAlias values at step
  subst following
  change after = Cells.encode Finset.univ (updated rightAlias values) at represented
  have different : Cells.encode Finset.univ (Function.update values 2 0) ≠
      Cells.encode Finset.univ (updated rightAlias values) := by decide
  exact different (bad.symm.trans represented)

end Controls

#print axioms lower?_roundtrip
#print axioms lower?_source
#print axioms computes
#print axioms result_comm
#print axioms progress
#print axioms logical_wp
#print axioms copy_then_logical_wp
#print axioms implementation_wp
#print axioms correct
#print axioms compile_wp
#print axioms Controls.right_alias
#print axioms Controls.alias_and_separate_counts
#print axioms Controls.lowering_guards
#print axioms Controls.overwritten_right_operand
#print axioms Controls.copy_first_alias_is_incorrect
end Mettapedia.Machines.TIsa.X86LogicalRecipes
