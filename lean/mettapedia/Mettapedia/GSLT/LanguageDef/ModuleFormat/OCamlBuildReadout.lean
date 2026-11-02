import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlReturnGather

/-! Build requests retain all collected values. Source formation checks
remain explicit for tuples and constructors; primitive evaluation remains
an observable service request until its answer is returned.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding

theorem build_tuple_instance (items rest : Pattern) :
    BaseRuleInstance 16 (node "MlBuildConfig" [node "MlBuildTuple", items, rest])
      (node "MlReturn" [node "MlTuple" [items], rest]) := by
  have fields : (baseLanguage.rewrites[16]?).map (fun row => (row.left, row.right, row.premises)) = some
      (node "MlBuildConfig" [node "MlBuildTuple", .fvar "values", .fvar "rest"],
       node "MlReturn" [node "MlTuple" [.fvar "values"], .fvar "rest"], []) := by decide +kernel
  let assignment : Bindings := [("values", items), ("rest", rest)]
  simpa [assignment, apply_node, applyBindings] using base_instance_of_fields fields assignment

theorem build_variant_instance (constructor items rest : Pattern) :
    BaseRuleInstance 17 (node "MlBuildConfig" [node "MlBuildVariant" [constructor], items, rest])
      (node "MlReturn" [node "MlVariant" [constructor, items], rest]) := by
  have fields : (baseLanguage.rewrites[17]?).map (fun row => (row.left, row.right, row.premises)) = some
      (node "MlBuildConfig" [node "MlBuildVariant" [.fvar "tag"], .fvar "values", .fvar "rest"],
       node "MlReturn" [node "MlVariant" [.fvar "tag", .fvar "values"], .fvar "rest"], []) := by decide +kernel
  let assignment : Bindings := [("tag", constructor), ("values", items), ("rest", rest)]
  simpa [assignment, apply_node, applyBindings] using base_instance_of_fields fields assignment

theorem build_primitive_instance (operator arguments rest : Pattern) :
    BaseRuleInstance 18 (node "MlBuildConfig" [node "MlBuildPrimitive" [operator], arguments, rest])
      (node "MlPrimitiveRequest" [operator, arguments, rest]) := by
  have fields : (baseLanguage.rewrites[18]?).map (fun row => (row.left, row.right, row.premises)) = some
      (node "MlBuildConfig" [node "MlBuildPrimitive" [.fvar "operator"], .fvar "values", .fvar "rest"],
       node "MlPrimitiveRequest" [.fvar "operator", .fvar "values", .fvar "rest"], []) := by decide +kernel
  let assignment : Bindings := [("operator", operator), ("values", arguments), ("rest", rest)]
  simpa [assignment, apply_node, applyBindings] using base_instance_of_fields fields assignment

theorem build_tuple_source {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} {program : OCaml.Program}
    {pool : List OCaml.MatchPattern} {items : List OCaml.Value} {rest : OCaml.Continuation} {encodedRest target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (authored : baseLanguage.rewrites[16]? = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (formed : 2 ≤ items.length)
    (resolved : continuation? pool rest = some encodedRest)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlBuildConfig" [node "MlBuildTuple", valueList items, encodedRest]) ordinal trace captured completed history target) :
    completed = captured ∧ history = [] ∧ ∃ next,
      OCaml.finishBuild program .tuple items rest = .ok next ∧ state? pool next = some target := by
  obtain ⟨sameCaptures, emptyHistory, output⟩ := base_instance_firing position authored zero
    (build_tuple_instance (valueList items) encodedRest) firing
  refine ⟨sameCaptures, emptyHistory, .returned (.tuple items) rest, ?_, ?_⟩
  · simp only [OCaml.finishBuild, if_neg (Nat.not_lt.mpr formed)]
    rfl
  · rw [output]
    simp only [state?, resolved, value, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

theorem build_variant_source {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} {program : OCaml.Program}
    {pool : List OCaml.MatchPattern} {typeId constructor : Nat} {items : List OCaml.Value}
    {rest : OCaml.Continuation} {encodedRest target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (authored : baseLanguage.rewrites[17]? = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (formed : program.constructorDeclared typeId constructor items.length = true)
    (resolved : continuation? pool rest = some encodedRest)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlBuildConfig" [node "MlBuildVariant" [tag typeId constructor], valueList items, encodedRest])
      ordinal trace captured completed history target) :
    completed = captured ∧ history = [] ∧ ∃ next,
      OCaml.finishBuild program (.variant typeId constructor) items rest = .ok next ∧ state? pool next = some target := by
  obtain ⟨sameCaptures, emptyHistory, output⟩ := base_instance_firing position authored zero
    (build_variant_instance (tag typeId constructor) (valueList items) encodedRest) firing
  refine ⟨sameCaptures, emptyHistory, .returned (.variant typeId constructor items) rest, ?_, ?_⟩
  · simp only [OCaml.Program.constructorDeclared] at formed
    simp only [OCaml.finishBuild, formed, if_true]
    rfl
  · rw [output]
    simp only [state?, resolved, value, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

#print axioms build_tuple_source
#print axioms build_variant_source

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
