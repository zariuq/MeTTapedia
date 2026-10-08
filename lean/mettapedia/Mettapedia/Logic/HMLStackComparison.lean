import Mettapedia.Logic.HMLStackProgram

/-!
# Complete stack-program answer and work comparisons

The independent postfix program runs above any supplied Boolean stack. Every
admitted formula produces one correct answer and retains the whole previous
stack. All modal successor occurrences execute, even when one earlier answer
already decides an existential or universal result.

The complete program length is exactly the previously computed inspection
work. These comparisons concern this eager instruction procedure; they do
not identify formula depth with work or machine instructions with host time.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ModalMuCalculus.StackInspection

open Inspection

universe u v

variable {State : Type u} {Action : Type v}

theorem execute_compiled {n : Nat} (presentation : SuccessorPresentation State Action)
    (formula : Formula Action n) (admitted : formula.isHML = true)
    (environment : BooleanEnv State n) (state : State) (stack : List Bool) :
    execute environment (compile presentation formula admitted state) stack =
      some ((inspect presentation formula admitted environment state).1 :: stack) := by
  induction formula generalizing state stack with
  | tt => rfl
  | ff => rfl
  | var index => rfl
  | neg body inductionHypothesis =>
      simp only [compile, execute_append, inductionHypothesis admitted environment state,
        Option.bind_some, execute, Instruction.execute, inspect]
  | conj first second firstHypothesis secondHypothesis =>
      have parts := Bool.and_eq_true_iff.mp admitted
      simp only [compile, execute_append, firstHypothesis parts.1 environment state,
        secondHypothesis parts.2 environment state, Option.bind_some, execute,
        Instruction.execute, inspect]
  | disj first second firstHypothesis secondHypothesis =>
      have parts := Bool.and_eq_true_iff.mp admitted
      simp only [compile, execute_append, firstHypothesis parts.1 environment state,
        secondHypothesis parts.2 environment state, Option.bind_some, execute,
        Instruction.execute, inspect]
  | diamond action body inductionHypothesis =>
      let children := presentation.successors state action
      let answer := fun successor => (inspect presentation body admitted environment successor).1
      have childRun := execute_children environment children
        (fun successor => compile presentation body admitted successor) answer
        (fun successor _ before => inductionHypothesis admitted environment successor before) stack
      rw [compile, execute_append, childRun]
      change execute environment [.gatherAny children.length]
        ((children.map answer).reverse ++ stack) = _
      have gathered := gather_any_answers environment (children.map answer) stack
      rw [List.length_map] at gathered
      rw [execute, gathered]
      simp only [Option.bind_some, execute, inspect, List.any_map]
      rfl
  | box action body inductionHypothesis =>
      let children := presentation.successors state action
      let answer := fun successor => (inspect presentation body admitted environment successor).1
      have childRun := execute_children environment children
        (fun successor => compile presentation body admitted successor) answer
        (fun successor _ before => inductionHypothesis admitted environment successor before) stack
      rw [compile, execute_append, childRun]
      change execute environment [.gatherAll children.length]
        ((children.map answer).reverse ++ stack) = _
      have gathered := gather_all_answers environment (children.map answer) stack
      rw [List.length_map] at gathered
      rw [execute, gathered]
      simp only [Option.bind_some, execute, inspect, List.all_map]
      rfl
  | mu body => exact False.elim (Bool.false_ne_true admitted)
  | nu body => exact False.elim (Bool.false_ne_true admitted)

theorem compiled_length {n : Nat} (presentation : SuccessorPresentation State Action)
    (formula : Formula Action n) (admitted : formula.isHML = true)
    (environment : BooleanEnv State n) (state : State) :
    (compile presentation formula admitted state).length =
      (inspect presentation formula admitted environment state).2 := by
  induction formula generalizing state with
  | tt => rfl
  | ff => rfl
  | var index => rfl
  | neg body inductionHypothesis =>
      simp only [compile, List.length_append, List.length_singleton, inspect,
        inductionHypothesis admitted environment state]
      omega
  | conj first second firstHypothesis secondHypothesis =>
      have parts := Bool.and_eq_true_iff.mp admitted
      simp only [compile, List.length_append, List.length_singleton, inspect,
        firstHypothesis parts.1 environment state, secondHypothesis parts.2 environment state]
      omega
  | disj first second firstHypothesis secondHypothesis =>
      have parts := Bool.and_eq_true_iff.mp admitted
      simp only [compile, List.length_append, List.length_singleton, inspect,
        firstHypothesis parts.1 environment state, secondHypothesis parts.2 environment state]
      omega
  | diamond action body inductionHypothesis =>
      simp only [compile, List.length_append, List.length_singleton, List.length_flatMap,
        List.map_map, inspect]
      simp only [Function.comp_def, inductionHypothesis admitted environment]
      omega
  | box action body inductionHypothesis =>
      simp only [compile, List.length_append, List.length_singleton, List.length_flatMap,
        List.map_map, inspect]
      simp only [Function.comp_def, inductionHypothesis admitted environment]
      omega
  | mu body => exact False.elim (Bool.false_ne_true admitted)
  | nu body => exact False.elim (Bool.false_ne_true admitted)

theorem compiled_satisfaction {n : Nat} (presentation : SuccessorPresentation State Action)
    (formula : Formula Action n) (admitted : formula.isHML = true)
    (environment : BooleanEnv State n) (state : State) (stack : List Bool) :
    execute environment (compile presentation formula admitted state) stack = some (true :: stack) ↔
      satisfies presentation.toLTS environment.toEnv formula state := by
  rw [execute_compiled, Option.some.injEq, List.cons.injEq]
  simp only [and_true]
  exact inspect_truth presentation formula admitted environment state

end Mettapedia.Logic.ModalMuCalculus.StackInspection
