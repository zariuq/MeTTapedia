import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedInputQueries
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedPrimitiveAnswers
import Mettapedia.OSLF.MeTTaIL.GeneralVectorOutputQuery

/-! The actual ComputePrimitive row reads its two inputs and matches the
cached answer into its output capture. Source result consumption composes
with this query, preserving values, faults and the continuation.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem prepared_primitive_query_step (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (operator : OCaml.Primitive) (arguments : List OCaml.Value)
    (result : OCaml.Result) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (cached : primitiveRow operator arguments result ∈ table.rows) :
    (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlPrimitiveRequest" [primitive operator, valueList arguments, encodedRest])
      (node "MlPrimitiveReturned" [primitiveResult result, encodedRest]) := by
  let authored := baseLanguage.rewrites[19]'(by decide +kernel)
  have atBase : baseLanguage.rewrites[19]? = some authored := List.getElem?_eq_getElem (by decide +kernel)
  have computed : (baseLanguage.rewrites[19]?).map (fun row => (row.left, row.right, row.premises)) =
      some (node "MlPrimitiveRequest" [.fvar "operator", .fvar "arguments", .fvar "rest"],
        node "MlPrimitiveReturned" [.fvar "result", .fvar "rest"],
        [.relationQuery "ml-primitive" [.fvar "operator", .fvar "arguments", .fvar "result"]]) := by decide +kernel
  rw [atBase] at computed
  have fields := Option.some.inj computed
  have left := congrArg (fun fields => fields.1) fields
  have right := congrArg (fun fields => fields.2.1) fields
  have premise := congrArg (fun fields => fields.2.2) fields
  dsimp only at left right premise
  obtain ⟨_, _, terms, types, dispatch, functions, _, _, allRows⟩ := prepare_readback program prepared built
  have inProgram : authored ∈ prepared.compiled.rewrites := by
    rw [allRows]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_of_getElem? atBase)))
  obtain ⟨ordinal, row, selected, same, _⟩ := whole_plan_row prepared authored inProgram (prepared_plan_complete program prepared built)
  have position : (epochPlan prepared table).rules[ordinal]? = some row := by
    rw [epoch_rules prepared table signatures]
    exact selected
  have declared : baseLanguage.rewrites[19]? = some row.authored := by rw [same]; exact atBase
  let runtime := GeneralPlanEnvironment.environment (epochPlan prepared table)
  have grammar : runtime.language.terms = baseLanguage.terms := terms
  have binding := selected_base_binding position terms types
  obtain ⟨leftShape, rightShape⟩ := base_vector_shapes row.authored (List.mem_of_getElem? declared)
  have admitted := (GeneralRuleBindingInference.compile_admitted binding).1
  have sourceTyped := primitive_request_open runtime.language grammar (epochPlan prepared table).snapshot.free operator arguments
    (patterns program) rest encodedRest resolved
  have targetTyped := primitive_returned_open runtime.language grammar (epochPlan prepared table).snapshot.free result
    (patterns program) rest encodedRest resolved
  have actualLeft : row.rule.left = node "MlPrimitiveRequest" [.fvar "operator", .fvar "arguments", .fvar "rest"] := by
    simpa only [GeneralExecutionAdmission.RulePlan.rule, GeneralRuleBindingInference.BindingPlan.elaborate, same] using left
  have actualRight : row.rule.right = node "MlPrimitiveReturned" [.fvar "result", .fvar "rest"] := by
    simpa only [GeneralExecutionAdmission.RulePlan.rule, GeneralRuleBindingInference.BindingPlan.elaborate, same] using right
  have actualPremise : row.rule.premises = [.relationQuery "ml-primitive" [.fvar "operator", .fvar "arguments", .fvar "result"]] := by
    simpa only [GeneralExecutionAdmission.RulePlan.rule, GeneralRuleBindingInference.BindingPlan.elaborate, same] using premise
  have context : row.rule.typeContext = [("operator", .base "MlPrimitive"), ("arguments", .base "MlValues"),
      ("result", .base "MlPrimitiveResult"), ("rest", .base "MlContinuation")] := by
    have checked : (GeneralRuleBindingInference.compile? baseLanguage authored).map
        (fun binding => (binding.elaborate authored).typeContext) = some [("operator", .base "MlPrimitive"),
          ("arguments", .base "MlValues"), ("result", .base "MlPrimitiveResult"), ("rest", .base "MlContinuation")] := by cbv
    rw [← same, binding] at checked
    exact Option.some.inj checked
  let assignment : Bindings := [("operator", primitive operator), ("arguments", valueList arguments),
    ("result", primitiveResult result), ("rest", encodedRest)]
  have typed : CapturesTyped runtime.language runtime.free [] row.rule.typeContext assignment := by
    intro entry member
    simp only [assignment, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact ⟨.base "MlPrimitive", by rw [context]; rfl,
        typed_node_open (primitive_vector operator) (primitive_typed runtime.language grammar runtime.free [] operator)⟩
    · exact ⟨.base "MlValues", by rw [context]; rfl,
        typed_node_open (valueList_vector arguments) (valueList_typed runtime.language grammar runtime.free [] arguments)⟩
    · exact ⟨.base "MlPrimitiveResult", by rw [context]; rfl,
        typed_node_open (primitiveResult_vector result) (primitiveResult_typed runtime.language grammar runtime.free [] result)⟩
    · exact ⟨.base "MlContinuation", by rw [context]; rfl,
        typed_node_open (continuation?_vector (patterns program) rest encodedRest resolved)
          (continuation?_typed runtime.language grammar runtime.free [] (patterns program) rest encodedRest resolved)⟩
  have input : applyBindings assignment row.rule.left = node "MlPrimitiveRequest" [primitive operator, valueList arguments, encodedRest] := by
    rw [actualLeft]
    simp [assignment, apply_node, applyBindings]
  have output : applyBindings assignment row.rule.right = node "MlPrimitiveReturned" [primitiveResult result, encodedRest] := by
    rw [actualRight]
    simp [assignment, apply_node, applyBindings]
  obtain ⟨rowIndex, rowAt⟩ := List.mem_iff_getElem?.mp cached
  have signature : GeneralPremise.signature? table "ml-primitive" 3 =
      some ⟨"ml-primitive", [.base "MlPrimitive", .base "MlValues", .base "MlPrimitiveResult"], [.input, .input, .output]⟩ := by
    unfold GeneralPremise.signature?
    rw [signatures]
    decide +kernel
  have closed := (epoch_primitive_request_checked program prepared table operator arguments rest encodedRest built resolved).1
  obtain ⟨trace, captured, completed, outputTrace, firing⟩ := vector_two_input_output_root_construct
    (GeneralPlanEnvironment.selected_rule (epochPlan prepared table) position)
    (GeneralPlanEnvironment.selected_specification (epochPlan prepared table) position) admitted
    (selected_base_zero position terms types declared) leftShape rightShape typed actualPremise
    (by rw [actualLeft]; simp [node, Pattern.freeFvarNames])
    (by rw [actualLeft]; simp [node, Pattern.freeFvarNames])
    (by rw [actualRight, actualLeft]; simp [node, Pattern.freeFvarNames])
    (vector_defined_of_closed_input leftShape assignment input closed)
    (by intro name member; have same : name = "result" := by simpa only [Pattern.freeFvarNames, List.mem_singleton] using member
        subst name; exact ⟨primitiveResult result, by simp [assignment, Bindings.lookup]⟩)
    sourceTyped targetTyped
    (typed_node_open (primitiveResult_vector result) (primitiveResult_typed runtime.language grammar runtime.free [] result))
    input output (by simp [assignment, applyBindings]) (by simp [assignment, applyBindings]) (by simp [assignment, applyBindings])
    rowAt signature rfl (GeneralPremise.checkRow_sound (primitive_row_checked runtime.language grammar runtime.free operator arguments result))
  exact GeneralOccurrenceSemantics.root_firing_step position rfl sourceTyped firing

theorem prepared_cached_primitive_path (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (operator : OCaml.Primitive) (arguments : List OCaml.Value)
    (result : OCaml.Result) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (meaning : ProviderMeaning (patterns program) table) (cached : primitiveRow operator arguments result ∈ table.rows)
    (resolved : continuation? (patterns program) rest = some encodedRest) :
    OCaml.finishBuild program (.primitive operator) arguments rest = .ok (finishPrimitive result rest) ∧
    ∃ target, state? (patterns program) (finishPrimitive result rest) = some target ∧
      Relation.ReflTransGen (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
        (node "MlPrimitiveRequest" [primitive operator, valueList arguments, encodedRest]) target := by
  obtain ⟨target, encoded, finish⟩ := prepared_primitive_answer_step program prepared table result rest encodedRest built signatures resolved
  exact ⟨cached_primitive_authorized table program operator arguments result rest meaning.1 cached, target, encoded,
    (Relation.ReflTransGen.single (prepared_primitive_query_step program prepared table operator arguments result rest encodedRest
      built signatures resolved cached)).trans (Relation.ReflTransGen.single finish)⟩

#print axioms prepared_primitive_query_step
#print axioms prepared_cached_primitive_path

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
