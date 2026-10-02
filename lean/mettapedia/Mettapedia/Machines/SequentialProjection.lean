import Mettapedia.Machines.SingletonSequence
import Mettapedia.Machines.ScopedCommit

/-!
# Sequential control without intermediate value lists

The source gathers every child value before selecting the first or last.
The target executes the same ordered goals, retaining only the selected value.
The projection law quantifies over the child service, state, faults and value
selector. It preserves repeated replies and never re-executes a selected value.

The separate continuation law composes arbitrary finite scoped controls in
their existing delimiter. Its world is threaded through backtracking; adding
a sequence does not install a new cut scope. These are component laws, not
native ownership or whole-runtime refinement theorems.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SequentialProjection

open SingletonSequence

variable {Op Value State Fault : Type}

def project (select : Value → Value → Value) (saved : Value) :
    Reply (List Value) State Fault → List (Reply Value State Fault)
  | .fault error state => [.fault error state]
  | .value values state => [.value (values.foldl select saved) state]

/-- No intermediate value list is built by the target. -/
def executeRest (execute : Op → State → List (Reply Value State Fault))
    (select : Value → Value → Value) :
    List Op → Value → State → List (Reply Value State Fault)
  | [], saved, state => [.value saved state]
  | op :: rest, saved, state =>
      (execute op state).flatMap fun
        | .fault error next => [.fault error next]
        | .value value next => executeRest execute select rest (select saved value) next

theorem projection_correct (execute : Op → State → List (Reply Value State Fault))
    (select : Value → Value → Value) (ops : List Op) (saved : Value) (state : State) :
    (collect execute ops state).flatMap (project select saved) =
      executeRest execute select ops saved state := by
  induction ops generalizing saved state with
  | nil => rfl
  | cons op rest ih =>
      simp only [collect, executeRest, List.flatMap_assoc]
      apply List.flatMap_congr
      intro reply _
      cases reply with
      | fault error next => rfl
      | value value next =>
          rw [List.flatMap_map]
          trans (collect execute rest next).flatMap (project select (select saved value))
          · apply List.flatMap_congr
            intro answer _
            cases answer <;> rfl
          · exact ih _ _

def executeSequence (execute : Op → State → List (Reply Value State Fault))
    (select : Value → Value → Value) : List Op → State → List (Reply Value State Fault)
  | [], _ => []
  | op :: rest, state =>
      (execute op state).flatMap fun
        | .fault error next => [.fault error next]
        | .value value next => executeRest execute select rest value next

private theorem fold_first (values : List Value) (value : Value) :
    values.foldl (fun saved _ => saved) value = value := by
  induction values with
  | nil => rfl
  | cons _ _ ih => exact ih

private theorem fold_last (values : List Value) (value : Value) :
    some (values.foldl (fun _ next => next) value) = (value :: values).getLast? := by
  induction values generalizing value with
  | nil => rfl
  | cons head rest ih =>
      simpa only [List.foldl_cons, List.getLast?_cons_cons] using ih head

theorem first_correct (execute : Op → State → List (Reply Value State Fault))
    (ops : List Op) (state : State) :
    (collect execute ops state).flatMap observeFirst =
      executeSequence execute (fun saved _ => saved) ops state := by
  cases ops with
  | nil => rfl
  | cons op rest =>
      simp only [collect, executeSequence, List.flatMap_assoc]
      apply List.flatMap_congr
      intro reply _
      cases reply with
      | fault error next => rfl
      | value value next =>
          rw [List.flatMap_map]
          dsimp only
          rw [← projection_correct]
          apply List.flatMap_congr
          intro answer _
          cases answer <;> simp [observeFirst, project]

theorem last_correct (execute : Op → State → List (Reply Value State Fault))
    (ops : List Op) (state : State) :
    (collect execute ops state).flatMap observeLast =
      executeSequence execute (fun _ next => next) ops state := by
  cases ops with
  | nil => rfl
  | cons op rest =>
      simp only [collect, executeSequence, List.flatMap_assoc]
      apply List.flatMap_congr
      intro reply _
      cases reply with
      | fault error next => rfl
      | value value next =>
          rw [List.flatMap_map]
          dsimp only
          rw [← projection_correct]
          apply List.flatMap_congr
          intro answer _
          cases answer <;> simp [observeLast, project, ← fold_last]

open ScopedCommit

variable {Local World Result : Type}

def lower (bodies : List (Body Local World)) : Body Local World :=
  bodies.foldr andThen .done

/-- Direct continuation execution, independently of the lowered syntax. -/
def executeControls : List (Body Local World) → Local →
    Success Local World Result → Failure World Result →
    Failure World Result → World → Result
  | [], state, success, failure, _, world => success state failure world
  | body :: rest, state, success, failure, saved, world =>
      eval body state (fun next alternatives nextWorld =>
        executeControls rest next success alternatives saved nextWorld) failure saved world

theorem controls_correct (bodies : List (Body Local World)) (state : Local)
    (success : Success Local World Result) (failure saved : Failure World Result)
    (world : World) :
    eval (lower bodies) state success failure saved world =
      executeControls bodies state success failure saved world := by
  induction bodies generalizing state failure world with
  | nil => rfl
  | cons body rest ih =>
      simp only [lower, List.foldr_cons, eval_andThen, executeControls]
      congr 1
      funext next alternatives nextWorld
      exact ih _ _ _

private def choices (op : Nat) (state : Nat) : List (Reply Nat Nat String) :=
  [.value op (state + 1), .value op (state + 1)]

example : executeSequence choices (fun _ next => next) [1, 2, 3] 0 =
    List.replicate 8 (.value 3 3) := by decide

example : executeSequence choices (fun saved _ => saved) [1, 2, 3] 0 =
    List.replicate 8 (.value 1 3) := by decide

example : executeSequence choices (fun saved _ => saved) [1, 2] 0 ≠ choices 1 0 := by
  decide

example : executeSequence (fun op state => if op = 2 then [.fault "raised" state]
    else choices op state) (fun saved _ => saved) [1, 2, 3] 0 =
    [.fault "raised" 1, .fault "raised" 1] := by decide

#print axioms projection_correct
#print axioms first_correct
#print axioms last_correct
#print axioms controls_correct

end Mettapedia.Machines.SequentialProjection
