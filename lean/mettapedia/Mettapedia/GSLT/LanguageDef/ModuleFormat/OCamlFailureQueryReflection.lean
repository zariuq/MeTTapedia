import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedInputQueries
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceProviderInvariant
import Mettapedia.OSLF.MeTTaIL.GeneralVectorInputQueryReadout

/-! Both actual failed-pattern query rows reflect to a failed source
pattern. Their target is exactly the next clause cursor or Match_failure;
the provider row cannot authorize a different argument or continuation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding GeneralFirstOrderProjection

theorem failure_query_firing_source {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} {pool : List OCaml.MatchPattern}
    (isClause : Bool) (index : Nat) (parameter : OCaml.MatchPattern) (argument : OCaml.Value)
    (body : OCaml.Code) (later : Pattern) (captured : OCaml.Environment) (rest target : Pattern)
    {trace : List GeneralScopedMatchMachine.BagChoice} {matched completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (authored : baseLanguage.rewrites[if isClause then 26 else 25]? = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (invariant : SourceProviderInvariant pool plan.snapshot.provider) (indexed : pool[index]? = some parameter)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node (if isClause then "MlTryClause" else "MlMatchOne")
        ([patternId index, value argument, code body] ++ (if isClause then [later] else []) ++ [environment captured, rest]))
      ordinal trace matched completed history target) :
    OCaml.matchPattern parameter argument = none ∧
      target = if isClause then node "MlSelect" [later, value argument, environment captured, rest]
        else node "MlFault" [fault .matchFailure] := by
  have fields : (baseLanguage.rewrites[if isClause then 26 else 25]?).map (fun row => (row.left, row.right, row.premises)) =
      some (node (if isClause then "MlTryClause" else "MlMatchOne")
          ([.fvar "pattern", .fvar "value", .fvar "body"] ++ (if isClause then [.fvar "later"] else []) ++
            [.fvar "environment", .fvar "rest"]),
        (if isClause then node "MlSelect" [.fvar "later", .fvar "value", .fvar "environment", .fvar "rest"]
          else node "MlFault" [fault .matchFailure]),
        [.relationQuery "ml-pattern-failure" [.fvar "pattern", .fvar "value"]]) := by
    cases isClause <;> decide +kernel
  rw [authored] at fields
  have actual := Option.some.inj fields
  have left := congrArg (fun fields => fields.1) actual
  have right := congrArg (fun fields => fields.2.1) actual
  have premise := congrArg (fun fields => fields.2.2) actual
  dsimp only at left right premise
  obtain ⟨leftShape, rightShape⟩ := base_vector_shapes row.authored (List.mem_of_getElem? authored)
  have signature : GeneralPremise.signature? plan.snapshot.provider "ml-pattern-failure" 2 =
      some ⟨"ml-pattern-failure", [.base "MlPattern", .base "MlValue"], [.input, .input]⟩ := by
    unfold GeneralPremise.signature?
    rw [invariant.signatures]
    decide +kernel
  obtain ⟨bindings, rowIndex, sourceRead, targetRead, rowAt⟩ := vector_two_input_root_readout
    (GeneralPlanEnvironment.selected_rule plan position) (GeneralPlanEnvironment.selected_specification plan position)
    zero leftShape (GeneralRuleBindingInference.vector_binderFree rightShape) premise rfl signature firing
  change applyBindings bindings row.authored.left = _ at sourceRead
  change applyBindings bindings row.authored.right = _ at targetRead
  let assignment : Bindings := [("pattern", patternId index), ("value", value argument), ("body", code body),
    ("later", later), ("environment", environment captured), ("rest", rest)]
  have input : applyBindings assignment row.authored.left =
      node (if isClause then "MlTryClause" else "MlMatchOne")
        ([patternId index, value argument, code body] ++ (if isClause then [later] else []) ++ [environment captured, rest]) := by
    rw [left]
    cases isClause <;> simp [assignment, apply_node, applyBindings]
  have output : applyBindings assignment row.authored.right =
      if isClause then node "MlSelect" [later, value argument, environment captured, rest]
        else node "MlFault" [fault .matchFailure] := by
    rw [right]
    cases isClause <;> simp [assignment, fault, apply_node, applyBindings]
  have patternBound : "pattern" ∈ row.authored.left.freeFvarNames := by
    rw [left]
    cases isClause <;> simp [node, Pattern.freeFvarNames]
  have valueBound : "value" ∈ row.authored.left.freeFvarNames := by
    rw [left]
    cases isClause <;> simp [node, Pattern.freeFvarNames]
  have patternRead : applyBindings bindings (.fvar "pattern") = patternId index := by
    simpa [assignment, apply_variable, Bindings.lookup] using
      vector_input_agreement leftShape bindings assignment (sourceRead.trans input.symm) "pattern" patternBound
  have valueRead : applyBindings bindings (.fvar "value") = value argument := by
    simpa [assignment, apply_variable, Bindings.lookup] using
      vector_input_agreement leftShape bindings assignment (sourceRead.trans input.symm) "value" valueBound
  have cached : failureRow index argument ∈ plan.snapshot.provider.rows := by
    simpa only [patternRead, valueRead, failureRow, GeneralPlanEnvironment.environment] using List.mem_of_getElem? rowAt
  refine ⟨invariant.meaningful.2 index parameter argument indexed cached, ?_⟩
  have rightBound : ∀ name ∈ row.authored.right.freeFvarNames, name ∈ row.authored.left.freeFvarNames := by
    rw [right, left]
    cases isClause <;> simp [node, fault, Pattern.freeFvarNames]
  exact targetRead.symm.trans ((vector_rule_output_unique leftShape rightShape rightBound bindings assignment
    (sourceRead.trans input.symm)).trans output)

#print axioms failure_query_firing_source

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
