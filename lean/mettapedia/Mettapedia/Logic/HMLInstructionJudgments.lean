import Mettapedia.Logic.HMLStackProgram

/-!
# Independent stack judgments for modal instructions

The rules describe the complete consumed stack prefix and retained suffix
for each opcode. They are independently generated judgments, with soundness
and reconstruction against the actual instruction evaluator. Gather rules
retain every supplied prefix occurrence, including repeated Boolean values.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ModalMuCalculus.StackInspection

open Inspection

universe u

variable {State : Type u} {n : Nat}

inductive InstructionJudgment (environment : BooleanEnv State n) :
    Instruction State n → List Bool → List Bool → Type u where
  | literal (value : Bool) (stack : List Bool) :
      InstructionJudgment environment (.literal value) stack (value :: stack)
  | readVariable (index : Fin n) (state : State) (stack : List Bool) :
      InstructionJudgment environment (.variable index state) stack (environment index state :: stack)
  | negate (value : Bool) (stack : List Bool) :
      InstructionJudgment environment .negate (value :: stack) ((!value) :: stack)
  | conjoin (later earlier : Bool) (stack : List Bool) :
      InstructionJudgment environment .conjoin (later :: earlier :: stack) ((earlier && later) :: stack)
  | disjoin (later earlier : Bool) (stack : List Bool) :
      InstructionJudgment environment .disjoin (later :: earlier :: stack) ((earlier || later) :: stack)
  | gatherAny (values stack : List Bool) :
      InstructionJudgment environment (.gatherAny values.length) (values ++ stack)
        (values.any id :: stack)
  | gatherAll (values stack : List Bool) :
      InstructionJudgment environment (.gatherAll values.length) (values ++ stack)
        (values.all id :: stack)

namespace InstructionJudgment

theorem sound (environment : BooleanEnv State n)
    {instruction : Instruction State n} {stack output : List Bool}
    (judgment : InstructionJudgment environment instruction stack output) :
    instruction.execute environment stack = some output := by
  cases judgment with
  | literal => rfl
  | readVariable => rfl
  | negate => rfl
  | conjoin => rfl
  | disjoin => rfl
  | gatherAny values stack => simp [Instruction.execute]
  | gatherAll values stack => simp [Instruction.execute]

/-- Reconstruction uses the supplied stack's actual prefix; it does not
select an arbitrary successful operation or replace a gather by one value. -/
def reconstruct (environment : BooleanEnv State n) (instruction : Instruction State n)
    (stack output : List Bool) (checked : instruction.execute environment stack = some output) :
    InstructionJudgment environment instruction stack output := by
  cases instruction with
  | literal value =>
      have same := Option.some.inj checked
      cases same
      exact .literal value stack
  | «variable» index state =>
      have same := Option.some.inj checked
      cases same
      exact .readVariable index state stack
  | negate =>
      cases stack with
      | nil => cases checked
      | cons value stack =>
          have same := Option.some.inj checked
          cases same
          exact .negate value stack
  | conjoin =>
      cases stack with
      | nil => cases checked
      | cons later stack =>
          cases stack with
          | nil => cases checked
          | cons earlier stack =>
              have same := Option.some.inj checked
              cases same
              exact .conjoin later earlier stack
  | disjoin =>
      cases stack with
      | nil => cases checked
      | cons later stack =>
          cases stack with
          | nil => cases checked
          | cons earlier stack =>
              have same := Option.some.inj checked
              cases same
              exact .disjoin later earlier stack
  | gatherAny count =>
      by_cases enough : count ≤ stack.length
      · have readout : some ((stack.take count).any id :: stack.drop count) = some output := by
          simpa only [Instruction.execute, if_pos enough] using checked
        have same := Option.some.inj readout
        cases same
        have judgment := InstructionJudgment.gatherAny (environment := environment)
          (stack.take count) (stack.drop count)
        simpa only [List.length_take_of_le enough, List.take_append_drop] using judgment
      · simp only [Instruction.execute, if_neg enough] at checked
        cases checked
  | gatherAll count =>
      by_cases enough : count ≤ stack.length
      · have readout : some ((stack.take count).all id :: stack.drop count) = some output := by
          simpa only [Instruction.execute, if_pos enough] using checked
        have same := Option.some.inj readout
        cases same
        have judgment := InstructionJudgment.gatherAll (environment := environment)
          (stack.take count) (stack.drop count)
        simpa only [List.length_take_of_le enough, List.take_append_drop] using judgment
      · simp only [Instruction.execute, if_neg enough] at checked
        cases checked

theorem exists_iff (environment : BooleanEnv State n) (instruction : Instruction State n)
    (stack output : List Bool) :
    Nonempty (InstructionJudgment environment instruction stack output) ↔
      instruction.execute environment stack = some output :=
  ⟨fun ⟨judgment⟩ => judgment.sound environment,
    fun checked => ⟨reconstruct environment instruction stack output checked⟩⟩

theorem output_unique (environment : BooleanEnv State n) {instruction : Instruction State n}
    {stack first second : List Bool}
    (before : InstructionJudgment environment instruction stack first)
    (after : InstructionJudgment environment instruction stack second) : first = second :=
  Option.some.inj ((before.sound environment).symm.trans (after.sound environment))

end InstructionJudgment

end Mettapedia.Logic.ModalMuCalculus.StackInspection
