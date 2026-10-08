import Mettapedia.Logic.HMLResidualEvidence

/-!
# Instruction, prefix and residual-evidence controls

One independently compiled variable program reads different environments at
execution. Actual incomplete prefixes can contain intermediate answers
without reporting. Malformed stacks retain their purse, complete programs
retain a supplied stack, and repeated instructions retain both occurrences.

Residual calculation evidence follows an actual prefix. A predicate saying
that the pending program contains a variable does not follow that prefix.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ModalMuCalculus.StackInspection.Controls

open Inspection Funded

def quiescent : SuccessorPresentation Bool Unit where
  successors _ _ := []

def environment : BooleanEnv Bool 1 := fun _ state => state

def inverseEnvironment : BooleanEnv Bool 1 := fun _ state => !state

def variableFormula : Formula Unit 1 := .var 0

def negatedVariable : Formula Unit 1 := .neg variableFormula

def compound : Formula Unit 1 :=
  .conj negatedVariable (.disj variableFormula .tt)

theorem variable_instruction_reads_at_execution :
    compile quiescent variableFormula rfl true = [.variable 0 true] ∧
      execute environment (compile quiescent variableFormula rfl true) [] = some [true] ∧
      execute inverseEnvironment (compile quiescent variableFormula rfl true) [] = some [false] := by
  decide

theorem nonconstant_variable_readout :
    execute environment (compile quiescent variableFormula rfl true) [] ≠
      execute environment (compile quiescent variableFormula rfl false) [] := by
  decide

theorem compound_instruction_readout :
    compile quiescent compound rfl true =
        [.variable 0 true, .negate, .variable 0 true, .literal true, .disjoin, .conjoin] ∧
      execute environment (compile quiescent compound rfl true) [false] = some [false, false] ∧
      execute environment (compile quiescent compound rfl false) [false] = some [true, false] := by
  decide

theorem empty_modalities_execute :
    execute environment (compile quiescent (.diamond () variableFormula) rfl true) [] = some [false] ∧
      execute environment (compile quiescent (.box () variableFormula) rfl true) [] = some [true] := by
  decide

theorem malformed_stack_operations_reject :
    (Instruction.negate (State := Bool) (n := 1)).execute environment [] = none ∧
      (Instruction.conjoin (State := Bool) (n := 1)).execute environment [true] = none ∧
      (Instruction.disjoin (State := Bool) (n := 1)).execute environment [] = none ∧
      (Instruction.gatherAny (State := Bool) (n := 1) 2).execute environment [true] = none ∧
      (Instruction.gatherAll (State := Bool) (n := 1) 1).execute environment [] = none := by
  decide

theorem malformed_program_retains_purse :
    (run environment [.negate] [] 25 4).1 = ⟨[.negate], [], 25, 4⟩ ∧
      (run environment [.negate] [] 25 4).2.sites = [] ∧
      publicAnswer (run environment [.negate] [] 25 4).1 = none := by
  decide

theorem empty_stack_has_no_public_answer :
    publicAnswer (⟨[], [], 5, 0⟩ : Configuration Bool 1) = none := by
  decide

def unopened := attempt quiescent negatedVariable rfl environment true [] 0

def intermediate := attempt quiescent negatedVariable rfl environment true [] 1

def complete := attempt quiescent negatedVariable rfl environment true [] 2

theorem zero_budget_retains_whole_program :
    unopened.endpoint = ⟨[.variable 0 true, .negate], [], 0, 0⟩ ∧
      unopened.path.sites = [] ∧ publicAnswer unopened.endpoint = none := by
  decide

theorem intermediate_answer_is_not_a_verdict :
    intermediate.endpoint = ⟨[.negate], [true], 0, 1⟩ ∧
      intermediate.path.sites = [.variable 0 true] ∧
      intermediate.endpoint.stack.head? = some true ∧ publicAnswer intermediate.endpoint = none := by
  decide

theorem completed_execution_and_account :
    complete.endpoint = ⟨[], [false], 0, 2⟩ ∧
      complete.path.sites = [.variable 0 true, .negate] ∧
      publicAnswer complete.endpoint = some false ∧
      (instructionAccount environment).onPath complete.path = 2 := by
  decide

theorem supplied_stack_is_retained :
    (attempt quiescent negatedVariable rfl environment true [false, true] 3).endpoint =
      ⟨[], [false, false, true], 1, 2⟩ := by
  decide

theorem repeated_instructions_retain_occurrences :
    (run environment [.literal true, .literal true, .conjoin] [] 3 0).2.sites =
        [.literal true, .literal true, .conjoin] ∧
      (run environment [.literal true, .literal true, .conjoin] [] 3 0).1 =
        ⟨[], [true], 0, 3⟩ := by
  decide

theorem residual_evidence_at_incomplete_endpoint :
    execute environment intermediate.endpoint.pending intermediate.endpoint.stack = some [false] := by
  have readout : inspect quiescent negatedVariable rfl environment true = (false, 2) := by decide
  simpa only [readout] using
    compiled_current_evidence quiescent negatedVariable rfl environment true [] 1 0 intermediate.path

def initialEvidence : ResidualEvidence environment
    (⟨compile quiescent negatedVariable rfl true, [], 1, 0⟩ : Configuration Bool 1) :=
  compiledResidualEvidence quiescent negatedVariable rfl environment true [] 1 0

theorem actual_transport_retains_computed_output :
    (transportResidual environment intermediate.path initialEvidence).val = [false] := by
  decide

theorem initial_predicate_does_not_transport :
    Instruction.variable 0 true ∈ (compile quiescent negatedVariable rfl true) ∧
      Instruction.variable 0 true ∉ intermediate.endpoint.pending := by
  decide

theorem completed_falsehood_certificate :
    ¬ satisfies quiescent.toLTS environment.toEnv negatedVariable true :=
  (complete.answer_sound quiescent negatedVariable rfl environment true [] 2 false (by decide)).2.2

end Mettapedia.Logic.ModalMuCalculus.StackInspection.Controls
