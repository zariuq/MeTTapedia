import Mettapedia.Languages.OCaml.CompiledDispatch

/-! Ordered constructor, environment, call/return, branch, fault and paging
controls for the prepared handler worker. These execute the worker itself.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml.CompiledDispatch.Controls

def integer (n : Int) : Value := .literal (.integer n)

def literalProgram : Program := {code := #[.literal (.integer 7)], entry := 0}

theorem zero_page_retains_entrance :
    run literalProgram (prepare literalProgram) 0 (begin literalProgram) = .pending (begin literalProgram) := rfl

theorem one_step_is_returned_not_halted :
    run literalProgram (prepare literalProgram) 1 (begin literalProgram) = .pending (.returned (integer 7) []) := by rfl

theorem second_step_completes :
    run literalProgram (prepare literalProgram) 2 (begin literalProgram) = .complete (.ok (integer 7)) := by rfl

theorem premature_completion_changes_the_page :
    run literalProgram (prepare literalProgram) 1 (begin literalProgram) ≠ .complete (.ok (integer 7)) := by
  rw [one_step_is_returned_not_halted]
  intro impossible
  cases impossible

def captureProgram : Program := {code := #[.lambda .bind 1, .variable 1], entry := 0}
def capturedCall : MachineState :=
  .returned (.closure (.lambda 0) [integer 7]) [.function (integer 99)]

theorem call_enters_captured_environment :
    step captureProgram (prepare captureProgram) capturedCall =
      .ok (some (.evaluate 1 [integer 99, integer 7] [])) := by rfl

theorem argument_does_not_replace_capture :
    run captureProgram (prepare captureProgram) 3 capturedCall = .complete (.ok (integer 7)) := by rfl

def priorityProgram : Program := {code := #[.literal (.integer 7), .literal (.integer 9)], entry := 0}
def clauses : List Clause := [⟨.wildcard, 0⟩, ⟨.literal (.integer 1), 1⟩]
def choice : MachineState := .returned (integer 1) [.matchValue clauses []]

theorem first_match_wins :
    run priorityProgram (prepare priorityProgram) 3 choice = .complete (.ok (integer 7)) := by rfl

theorem relation_style_reordering_is_not_admitted :
    run priorityProgram (prepare priorityProgram) 3 (.returned (integer 1) [.matchValue clauses.reverse []]) =
      .complete (.ok (integer 9)) := by rfl

def faultProgram : Program :=
  { code := #[.matchValue 1 [], .literal (.integer 0), .primitive .divide [3, 1],
      .literal (.integer 1), .tuple [0, 2]], entry := 4 }

theorem right_to_left_fault_order :
    run faultProgram (prepare faultProgram) 40 (begin faultProgram) = .complete (.error .divisionByZero) := by rfl

def branchProgram : Program :=
  {code := #[.literal (.boolean false), .literal (.integer 7), .literal (.integer 9), .branch 0 1 2], entry := 3}

theorem false_branch_keeps_its_choice :
    run branchProgram (prepare branchProgram) 10 (begin branchProgram) = .complete (.ok (integer 9)) := by rfl

theorem split_call_keeps_exact_pending_state :
    resume captureProgram (prepare captureProgram) 2 (run captureProgram (prepare captureProgram) 1 capturedCall) =
      .complete (.ok (integer 7)) := by rfl

theorem trace_retains_call_return_and_halt :
    trace captureProgram (prepare captureProgram) 3 capturedCall =
      [.evaluate 1 [integer 99, integer 7] [], .returned (integer 7) [], .halted (.ok (integer 7))] := by rfl

theorem missing_instruction_keeps_internal_error :
    run literalProgram (prepare literalProgram) 1 (.evaluate 99 [] []) = .invalid (.missingCode 99) := by rfl

def changedProgram : Program := {code := #[.literal (.integer 9)], entry := 0}

/-- A handler table belongs to its prepared source program, not just the
number of rows or the entry address. Live currentness must retain that stamp. -/
theorem stale_handlers_are_not_a_current_program :
    run changedProgram (prepare literalProgram) 2 (begin changedProgram) = .complete (.ok (integer 7)) ∧
    run changedProgram (prepare changedProgram) 2 (begin changedProgram) = .complete (.ok (integer 9)) := ⟨rfl, rfl⟩

end Mettapedia.Languages.OCaml.CompiledDispatch.Controls
