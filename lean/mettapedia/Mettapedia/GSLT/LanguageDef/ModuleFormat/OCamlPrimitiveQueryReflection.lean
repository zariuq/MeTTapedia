import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedInputQueries
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlProviderEncoding
import Mettapedia.OSLF.MeTTaIL.GeneralQueryRowReadout

/-! Every actual selected primitive-query firing reads a source-encoded
cache row for the same operator and arguments. Its result and retained
continuation therefore have the independent source meaning.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding GeneralFirstOrderProjection

theorem primitive_query_firing_source {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} {pool : List OCaml.MatchPattern}
    {operator : OCaml.Primitive} {arguments : List OCaml.Value} {rest target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (authored : baseLanguage.rewrites[19]? = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (signatures : plan.snapshot.provider.signatures = provider.signatures)
    (encoded : EncodedProviderRows plan.snapshot.provider) (meaning : ProviderMeaning pool plan.snapshot.provider)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlPrimitiveRequest" [primitive operator, valueList arguments, rest]) ordinal trace captured completed history target) :
    ∃ result, operator.eval arguments = .ok result ∧
      primitiveRow operator arguments result ∈ plan.snapshot.provider.rows ∧
      target = node "MlPrimitiveReturned" [primitiveResult result, rest] := by
  have fields : (baseLanguage.rewrites[19]?).map (fun row => (row.left, row.right, row.premises)) =
      some (node "MlPrimitiveRequest" [.fvar "operator", .fvar "arguments", .fvar "rest"],
        node "MlPrimitiveReturned" [.fvar "result", .fvar "rest"],
        [.relationQuery "ml-primitive" [.fvar "operator", .fvar "arguments", .fvar "result"]]) := by decide +kernel
  rw [authored] at fields
  have actual := Option.some.inj fields
  have left := congrArg (fun fields => fields.1) actual
  have right := congrArg (fun fields => fields.2.1) actual
  have premise := congrArg (fun fields => fields.2.2) actual
  dsimp only at left right premise
  have actualPremise : row.rule.premises = [.relationQuery "ml-primitive" [.fvar "operator", .fvar "arguments", .fvar "result"]] := premise
  obtain ⟨leftShape, rightShape⟩ := base_vector_shapes row.authored (List.mem_of_getElem? authored)
  have signature : GeneralPremise.signature? plan.snapshot.provider "ml-primitive" 3 =
      some ⟨"ml-primitive", [.base "MlPrimitive", .base "MlValues", .base "MlPrimitiveResult"], [.input, .input, .output]⟩ := by
    unfold GeneralPremise.signature?
    rw [signatures]
    decide +kernel
  cases firing with
  | fire actualDeclared actualSpecified admitted sourceTyped matching typed premises reduct targetTyped =>
    have sameRule := Option.some.inj (actualDeclared.symm.trans (GeneralPlanEnvironment.selected_rule plan position))
    subst sameRule
    have sameSpec := Option.some.inj (actualSpecified.symm.trans (GeneralPlanEnvironment.selected_specification plan position))
    subst sameSpec
    have roots := typed.rootValues zero
    have sourceRead := vector_matching_readout leftShape matching.matching (fun _ _ found => found) roots
    change applyBindings (ordinary captured) row.authored.left = _ at sourceRead
    rw [left] at sourceRead
    simp only [apply_node, List.map_cons, List.map_nil] at sourceRead
    have sourceFields := List.cons.inj (Pattern.apply.inj sourceRead).2
    have operatorRead := sourceFields.1
    have argumentsRead := (List.cons.inj sourceFields.2).1
    rw [actualPremise] at premises
    cases premises with
    | cons head tail =>
      cases tail
      cases head with
      | query queried =>
        obtain ⟨first, second, answer, present, firstInput, secondInput, outputMatch⟩ :=
          GeneralPremise.two_input_output_row_readout rfl signature queried
        have firstRead := binderFree_instantiation_readout (by rfl) roots firstInput
        have secondRead := binderFree_instantiation_readout (by rfl) roots secondInput
        have firstSame : first = primitive operator := firstRead.symm.trans operatorRead
        have secondSame : second = valueList arguments := secondRead.symm.trans argumentsRead
        subst first second
        have presentSource : (⟨"ml-primitive", [primitive operator, valueList arguments, answer]⟩ : GeneralPremise.ProviderRow) ∈
            plan.snapshot.provider.rows := by
          simpa only [operatorRead, argumentsRead, GeneralPlanEnvironment.environment] using List.mem_of_getElem? present
        obtain ⟨result, answerSame, cached⟩ := primitive_query_row_source plan.snapshot.provider operator arguments answer
          encoded presentSource
        have completedTyped : GeneralPremise.TypedAssignment (GeneralPlanEnvironment.environment plan)
            ⟨ordinal, row.rule, row.binding.spec, [], 0, 0⟩ completed := by
          cases queried with
          | row _ _ _ _ finalTyped => exact finalTyped
          | dynamicRow _ _ _ source _ _ _ _ => cases source
        have finalRoots := completedTyped.rootValues zero
        have finalSourceRead := vector_matching_readout leftShape matching.matching queried.extension finalRoots
        change applyBindings (ordinary completed) row.authored.left = _ at finalSourceRead
        rw [left] at finalSourceRead
        simp only [apply_node, List.map_cons, List.map_nil] at finalSourceRead
        have restRead := (List.cons.inj (List.cons.inj (List.cons.inj (Pattern.apply.inj finalSourceRead).2).2).2).1
        have resultRead := vector_matching_readout (.metavariable "result") outputMatch (fun _ _ found => found) finalRoots
        have targetRead := binderFree_instantiation_readout (GeneralRuleBindingInference.vector_binderFree rightShape) finalRoots reduct
        change applyBindings (ordinary completed) row.authored.right = _ at targetRead
        rw [right] at targetRead
        simp only [apply_node, List.map_cons, List.map_nil, resultRead, restRead, answerSame] at targetRead
        exact ⟨result, meaning.1 operator arguments result cached, cached, targetRead.symm⟩

#print axioms primitive_query_firing_source

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
