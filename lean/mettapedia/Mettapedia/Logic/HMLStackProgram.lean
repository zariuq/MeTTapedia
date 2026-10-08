import Mettapedia.Logic.HMLInspection

/-!
# Independent stack programs for complete finite modal inspection

The compiler emits a genuine postfix instruction list. Variables are read
when their instruction executes. Modalities compile every supplied successor
occurrence before gathering its answers; neither an answer nor its work total
is embedded as the program's meaning.

Execution may reject malformed stacks. The separate comparison proves that
compiled admitted formulas execute with exactly one result above any supplied
stack, and counts the instructions actually performed.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ModalMuCalculus.StackInspection

open Inspection

universe u v

inductive Instruction (State : Type u) (n : Nat) where
  | literal (value : Bool)
  | variable (index : Fin n) (state : State)
  | negate
  | conjoin
  | disjoin
  | gatherAny (count : Nat)
  | gatherAll (count : Nat)
  deriving DecidableEq

variable {State : Type u} {Action : Type v} {n : Nat}

def Instruction.execute (environment : BooleanEnv State n) :
    Instruction State n → List Bool → Option (List Bool)
  | .literal value, stack => some (value :: stack)
  | .variable index state, stack => some (environment index state :: stack)
  | .negate, value :: stack => some ((!value) :: stack)
  | .conjoin, later :: earlier :: stack => some ((earlier && later) :: stack)
  | .disjoin, later :: earlier :: stack => some ((earlier || later) :: stack)
  | .gatherAny count, stack =>
      if count ≤ stack.length then some ((stack.take count).any id :: stack.drop count) else none
  | .gatherAll count, stack =>
      if count ≤ stack.length then some ((stack.take count).all id :: stack.drop count) else none
  | _, _ => none

def execute (environment : BooleanEnv State n) :
    List (Instruction State n) → List Bool → Option (List Bool)
  | [], stack => some stack
  | instruction :: rest, stack =>
      (instruction.execute environment stack).bind (execute environment rest)

theorem execute_append (environment : BooleanEnv State n)
    (before after : List (Instruction State n)) (stack : List Bool) :
    execute environment (before ++ after) stack =
      (execute environment before stack).bind (execute environment after) := by
  induction before generalizing stack with
  | nil => rfl
  | cons instruction rest inductionHypothesis =>
      simp only [List.cons_append, execute]
      cases checked : instruction.execute environment stack with
      | none => rfl
      | some next => exact inductionHypothesis next

def compile (presentation : SuccessorPresentation State Action) :
    (formula : Formula Action n) → formula.isHML = true → State → List (Instruction State n)
  | .tt, _, _ => [.literal true]
  | .ff, _, _ => [.literal false]
  | .var index, _, state => [.variable index state]
  | .neg body, admitted, state => compile presentation body admitted state ++ [.negate]
  | .conj first second, admitted, state =>
      compile presentation first (Bool.and_eq_true_iff.mp admitted).1 state ++
        compile presentation second (Bool.and_eq_true_iff.mp admitted).2 state ++ [.conjoin]
  | .disj first second, admitted, state =>
      compile presentation first (Bool.and_eq_true_iff.mp admitted).1 state ++
        compile presentation second (Bool.and_eq_true_iff.mp admitted).2 state ++ [.disjoin]
  | .diamond action body, admitted, state =>
      (presentation.successors state action).flatMap
        (fun successor => compile presentation body admitted successor) ++
          [.gatherAny (presentation.successors state action).length]
  | .box action body, admitted, state =>
      (presentation.successors state action).flatMap
        (fun successor => compile presentation body admitted successor) ++
          [.gatherAll (presentation.successors state action).length]
  | .mu _, admitted, _ => False.elim (Bool.false_ne_true admitted)
  | .nu _, admitted, _ => False.elim (Bool.false_ne_true admitted)

/-- Running independently successful child programs retains every result in
its actual stack order, including equal answers at distinct occurrences. -/
theorem execute_children {Child : Type v} (environment : BooleanEnv State n)
    (children : List Child) (program : Child → List (Instruction State n))
    (answer : Child → Bool)
    (successful : ∀ child ∈ children, ∀ stack,
      execute environment (program child) stack = some (answer child :: stack))
    (stack : List Bool) :
    execute environment (children.flatMap program) stack =
      some ((children.map answer).reverse ++ stack) := by
  induction children generalizing stack with
  | nil => rfl
  | cons child rest inductionHypothesis =>
      rw [List.flatMap_cons, execute_append, successful child List.mem_cons_self stack]
      change execute environment (rest.flatMap program) (answer child :: stack) = _
      rw [inductionHypothesis (fun next member => successful next (List.mem_cons_of_mem _ member))]
      simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem gather_any_answers (environment : BooleanEnv State n)
    (answers stack : List Bool) :
    (Instruction.gatherAny answers.length).execute environment (answers.reverse ++ stack) =
      some (answers.any id :: stack) := by
  simp [Instruction.execute]

theorem gather_all_answers (environment : BooleanEnv State n)
    (answers stack : List Bool) :
    (Instruction.gatherAll answers.length).execute environment (answers.reverse ++ stack) =
      some (answers.all id :: stack) := by
  simp [Instruction.execute]

end Mettapedia.Logic.ModalMuCalculus.StackInspection
