import Mettapedia.GSLT.LanguageDef.NativeOpsCLocalBlock

/-!
# Retained counted loops over scoped local blocks

The loop tests its supplied condition before executing its supplied body.
Normal body completion executes the supplied increment; break exits without
that increment, and return propagates its actual value. Counted declarations
restore the previous counter binding. Iteration and body proof fuel are
separate from undefined reads and completed C control flow.

Nested read-only loops use the existing local block service. This is a typed
fragment, not an interpreter for arbitrary C or a physical-memory model.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.NativeC.LocalLoop

open ScalarRead LocalBlock

variable {Ptr : Type} [DecidableEq Ptr]

def run (fields : FieldReader Ptr) (condition step : CExpr) (body : List CStatement)
    (bodyFuel fuel : Nat) (environment : Environment Ptr) : LocalBlock.Result Ptr :=
  match (expression environment fields condition).bind truth? with
  | none => .finished none
  | some false => .finished (some (.next environment))
  | some true => match fuel with
    | 0 => .exhausted
    | fuel + 1 => match LocalBlock.execute fields bodyFuel environment body with
      | .finished none => .finished none
      | .finished (some (.next updated)) => match increment updated step with
          | none => .finished none
          | some advanced => run fields condition step body bodyFuel fuel advanced
      | .finished (some (.broken updated)) => .finished (some (.next updated))
      | .finished (some (.returned updated value)) => .finished (some (.returned updated value))
      | .exhausted => .exhausted

def counted (fields : FieldReader Ptr) (bodyFuel fuel : Nat)
    (environment : Environment Ptr) : CStatement → Option (LocalBlock.Result Ptr)
  | .forLoop type counter initial condition step body =>
      if type = ⟨"uint32_t".toList, 0⟩ then do
        let .unsigned first ← expression environment fields initial | none
        some (LocalBlock.restore counter (environment counter)
          (run fields condition step body bodyFuel fuel
            (Function.update environment counter (some (.unsigned first)))))
      else none
  | _ => none

/-- A while loop has no implicit increment. Its actual body must make progress;
break becomes normal loop completion, while return retains its value. -/
def whileRun (fields : FieldReader Ptr) (condition : CExpr) (body : List CStatement)
    (bodyFuel fuel : Nat) (environment : Environment Ptr) : LocalBlock.Result Ptr :=
  match (expression environment fields condition).bind truth? with
  | none => .finished none
  | some false => .finished (some (.next environment))
  | some true => match fuel with
    | 0 => .exhausted
    | fuel + 1 => match LocalBlock.execute fields bodyFuel environment body with
      | .finished (some (.next updated)) => whileRun fields condition body bodyFuel fuel updated
      | .finished (some (.broken updated)) => .finished (some (.next updated))
      | result => result

def whileStatement (fields : FieldReader Ptr) (bodyFuel fuel : Nat)
    (environment : Environment Ptr) : CStatement → Option (LocalBlock.Result Ptr)
  | .whileLoop condition body => some (whileRun fields condition body bodyFuel fuel environment)
  | _ => none

theorem while_false_condition_skips_body (fields : FieldReader Ptr) (condition : CExpr)
    (body : List CStatement) (bodyFuel fuel : Nat) (environment : Environment Ptr)
    (test : (expression environment fields condition).bind truth? = some false) :
    whileRun fields condition body bodyFuel fuel environment =
      .finished (some (.next environment)) := by
  rw [whileRun.eq_def, test]

theorem while_true_condition_executes_body (fields : FieldReader Ptr) (condition : CExpr)
    (body : List CStatement) (bodyFuel fuel : Nat) (environment updated : Environment Ptr)
    (test : (expression environment fields condition).bind truth? = some true)
    (completed : LocalBlock.execute fields bodyFuel environment body = .finished (some (.next updated))) :
    whileRun fields condition body bodyFuel (fuel + 1) environment =
      whileRun fields condition body bodyFuel fuel updated := by
  rw [whileRun.eq_def, test]
  dsimp only
  rw [completed]

theorem while_break_completes (fields : FieldReader Ptr) (condition : CExpr)
    (body : List CStatement) (bodyFuel fuel : Nat) (environment updated : Environment Ptr)
    (test : (expression environment fields condition).bind truth? = some true)
    (completed : LocalBlock.execute fields bodyFuel environment body = .finished (some (.broken updated))) :
    whileRun fields condition body bodyFuel (fuel + 1) environment =
      .finished (some (.next updated)) := by
  rw [whileRun.eq_def, test]
  dsimp only
  rw [completed]

theorem false_condition_skips_body (fields : FieldReader Ptr) (condition step : CExpr)
    (body : List CStatement) (bodyFuel fuel : Nat) (environment : Environment Ptr)
    (test : (expression environment fields condition).bind truth? = some false) :
    run fields condition step body bodyFuel fuel environment =
      .finished (some (.next environment)) := by
  rw [run.eq_def, test]

theorem true_condition_continues_actual_body (fields : FieldReader Ptr) (condition step : CExpr)
    (body : List CStatement) (bodyFuel fuel : Nat) (environment updated advanced : Environment Ptr)
    (test : (expression environment fields condition).bind truth? = some true)
    (completed : LocalBlock.execute fields bodyFuel environment body = .finished (some (.next updated)))
    (incremented : increment updated step = some advanced) :
    run fields condition step body bodyFuel (fuel + 1) environment =
      run fields condition step body bodyFuel fuel advanced := by
  rw [run.eq_def, test]
  dsimp only
  rw [completed]
  dsimp only
  rw [incremented]

theorem break_exits_without_increment (fields : FieldReader Ptr) (condition step : CExpr)
    (body : List CStatement) (bodyFuel fuel : Nat) (environment updated : Environment Ptr)
    (test : (expression environment fields condition).bind truth? = some true)
    (completed : LocalBlock.execute fields bodyFuel environment body = .finished (some (.broken updated))) :
    run fields condition step body bodyFuel (fuel + 1) environment =
      .finished (some (.next updated)) := by
  rw [run.eq_def, test]
  dsimp only
  rw [completed]

theorem zero_initialization_keeps_counter_scope (fields : FieldReader Ptr) (bodyFuel fuel : Nat)
    (environment : Environment Ptr) (counter : Name) (condition step : CExpr) (body : List CStatement) :
    counted fields bodyFuel fuel environment
      (.forLoop ⟨"uint32_t".toList, 0⟩ counter (.unsignedInteger 0) condition step body) =
      some (LocalBlock.restore counter (environment counter)
        (run fields condition step body bodyFuel fuel
          (Function.update environment counter (some (.unsigned 0))))) := by
  simp [counted, expression]

namespace Controls

def fields : FieldReader Nat := fun _ _ => none
def environment : Environment Nat := fun name =>
  if name = ['i'] then some (.unsigned 7)
  else if name = ['o', 'k'] then some (.boolean true) else none

def observeCounter : LocalBlock.Result Nat → Option UInt32
  | .finished (some (.next environment)) | .finished (some (.returned environment _)) => do
      let .unsigned counter ← environment ['i'] | none
      some counter
  | _ => none

theorem false_condition_does_not_touch_invalid_body :
    run fields (.bool false) (.identifier ['m'])
      [.declare ⟨"Space".toList, 1⟩ ['d'] (.identifier ['m'])] 0 0 environment =
      .finished (some (.next environment)) := rfl

theorem break_does_not_increment_counter :
    observeCounter (run fields (.bool true) (.postIncrement (.identifier ['i']))
      [.break] 1 1 environment) = some 7 := rfl

theorem return_is_not_loop_break :
    run fields (.bool true) (.postIncrement (.identifier ['i']))
      [.return (some (.bool false))] 1 1 environment =
      .finished (some (.returned environment (some (.boolean false)))) := rfl

theorem missing_increment_is_not_synthesized :
    run fields (.bool true) (.identifier ['m']) [] 0 1 environment = .finished none := rfl

theorem missing_condition_is_not_false_completion :
    run fields (.identifier ['m']) (.postIncrement (.identifier ['i'])) [] 0 0 environment =
      .finished none := rfl

theorem live_condition_with_no_iterations_is_exhausted :
    run fields (.bool true) (.postIncrement (.identifier ['i'])) [] 0 0 environment = .exhausted := rfl

theorem counter_scope_restores_outer_value :
    (counted fields 1 1 environment (.forLoop ⟨"uint32_t".toList, 0⟩ ['i'] (.unsignedInteger 0)
      (.bool true) (.postIncrement (.identifier ['i'])) [.break])).bind observeCounter = some 7 := rfl

theorem while_without_progress_is_exhausted :
    whileRun fields (.bool true) [] 0 3 environment = .exhausted := rfl

theorem while_break_does_not_increment :
    observeCounter (whileRun fields (.bool true) [.break] 1 1 environment) = some 7 := rfl

theorem while_return_is_not_normal_completion :
    whileRun fields (.bool true) [.return (some (.bool false))] 1 1 environment =
      .finished (some (.returned environment (some (.boolean false)))) := rfl

theorem while_unknown_condition_is_not_false :
    whileRun fields (.identifier ['m']) [] 0 0 environment = .finished none := rfl

end Controls

#print axioms false_condition_skips_body
#print axioms true_condition_continues_actual_body
#print axioms break_exits_without_increment
#print axioms zero_initialization_keeps_counter_scope
#print axioms Controls.false_condition_does_not_touch_invalid_body
#print axioms Controls.break_does_not_increment_counter
#print axioms Controls.return_is_not_loop_break
#print axioms Controls.missing_increment_is_not_synthesized
#print axioms Controls.missing_condition_is_not_false_completion
#print axioms Controls.live_condition_with_no_iterations_is_exhausted
#print axioms Controls.counter_scope_restores_outer_value
#print axioms while_false_condition_skips_body
#print axioms while_true_condition_executes_body
#print axioms while_break_completes
#print axioms Controls.while_without_progress_is_exhausted
#print axioms Controls.while_break_does_not_increment
#print axioms Controls.while_return_is_not_normal_completion
#print axioms Controls.while_unknown_condition_is_not_false

end Mettapedia.GSLT.LanguageDef.NativeOps.NativeC.LocalLoop
