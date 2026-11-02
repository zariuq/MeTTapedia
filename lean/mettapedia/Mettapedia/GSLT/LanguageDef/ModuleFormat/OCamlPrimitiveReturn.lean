import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlReturnBoolean

/-! Primitive answer dispatch preserves values and faults. This proves
the answer-consumption boundary; correctness of the installed primitive
provider and its MeTTa implementation is a separate obligation.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding

def primitiveResult (result : OCaml.Result) : Pattern := match result with
  | .ok actual => node "MlPrimitiveValue" [value actual]
  | .error error => node "MlPrimitiveFault" [fault error]

theorem primitive_value_instance (actual rest : Pattern) :
    BaseRuleInstance 20 (node "MlPrimitiveReturned" [node "MlPrimitiveValue" [actual], rest])
      (node "MlReturn" [actual, rest]) := by
  have fields : (baseLanguage.rewrites[20]?).map (fun row => (row.left, row.right, row.premises)) = some
      (node "MlPrimitiveReturned" [node "MlPrimitiveValue" [.fvar "value"], .fvar "rest"],
       node "MlReturn" [.fvar "value", .fvar "rest"], []) := by decide +kernel
  let assignment : Bindings := [("value", actual), ("rest", rest)]
  simpa [assignment, apply_node, applyBindings] using base_instance_of_fields fields assignment

theorem primitive_fault_instance (error rest : Pattern) :
    BaseRuleInstance 21 (node "MlPrimitiveReturned" [node "MlPrimitiveFault" [error], rest])
      (node "MlFault" [error]) := by
  have fields : (baseLanguage.rewrites[21]?).map (fun row => (row.left, row.right, row.premises)) = some
      (node "MlPrimitiveReturned" [node "MlPrimitiveFault" [.fvar "fault"], .fvar "rest"],
       node "MlFault" [.fvar "fault"], []) := by decide +kernel
  let assignment : Bindings := [("fault", error), ("rest", rest)]
  simpa [assignment, apply_node, applyBindings] using base_instance_of_fields fields assignment

def finishPrimitive (result : OCaml.Result) (rest : OCaml.Continuation) : OCaml.MachineState := match result with
  | .ok actual => .returned actual rest
  | .error error => .halted (.error error)

theorem finish_primitive_source (program : OCaml.Program) (operator : OCaml.Primitive) (arguments : List OCaml.Value)
    (result : OCaml.Result) (rest : OCaml.Continuation)
    (evaluated : operator.eval arguments = .ok result) :
    OCaml.finishBuild program (.primitive operator) arguments rest = .ok (finishPrimitive result rest) := by
  simp only [OCaml.finishBuild, evaluated]
  cases result <;> rfl

theorem primitive_return_firing_source {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} {program : OCaml.Program}
    {pool : List OCaml.MatchPattern} {operator : OCaml.Primitive} {arguments : List OCaml.Value}
    {result : OCaml.Result} {rest : OCaml.Continuation} {encodedRest target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (authored : baseLanguage.rewrites[match result with | .ok _ => 20 | .error _ => 21]? = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (resolved : continuation? pool rest = some encodedRest)
    (evaluated : operator.eval arguments = .ok result)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlPrimitiveReturned" [primitiveResult result, encodedRest]) ordinal trace captured completed history target) :
    completed = captured ∧ history = [] ∧ ∃ next,
      OCaml.finishBuild program (.primitive operator) arguments rest = .ok next ∧ state? pool next = some target := by
  have source := finish_primitive_source program operator arguments result rest evaluated
  cases result with
  | ok actual =>
      obtain ⟨sameCaptures, emptyHistory, output⟩ := base_instance_firing position authored zero
        (primitive_value_instance (value actual) encodedRest) firing
      refine ⟨sameCaptures, emptyHistory, .returned actual rest, source, ?_⟩
      rw [output]
      simp only [state?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  | error error =>
      obtain ⟨sameCaptures, emptyHistory, output⟩ := base_instance_firing position authored zero
        (primitive_fault_instance (fault error) encodedRest) firing
      exact ⟨sameCaptures, emptyHistory, .halted (.error error), source, by rw [output]; rfl⟩

#print axioms finish_primitive_source
#print axioms primitive_return_firing_source

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
