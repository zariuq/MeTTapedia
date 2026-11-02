import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedBaseSteps
import Mettapedia.OSLF.MeTTaIL.GeneralVectorInputQuery

/-! Read-only kernel queries use the actual selected row, provider row
and inferred binding specification of a successfully prepared program.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

set_option cbv.maxSteps 2000000 in
theorem base_dependencies_checked : baseLanguage.rewrites.all (fun authored =>
    match GeneralRuleBindingInference.compile? baseLanguage authored with
    | none => false
    | some binding => GeneralPremise.checkZeroDependencies binding.spec) = true := by cbv

theorem selected_base_zero {snapshot : GeneralExecutionAdmission.Snapshot}
    {permissions : GeneralExecutionAdmission.Permissions} {row : GeneralExecutionAdmission.RulePlan} {ordinal index : Nat}
    (position : (GeneralExecutionAdmission.compile snapshot permissions).rules[ordinal]? = some row)
    (terms : snapshot.language.terms = baseLanguage.terms) (types : snapshot.language.typeNames = baseLanguage.typeNames)
    (authored : baseLanguage.rewrites[index]? = some row.authored) :
    GeneralPremise.checkZeroDependencies row.binding.spec = true := by
  have checked := List.all_eq_true.mp base_dependencies_checked row.authored (List.mem_of_getElem? authored)
  rw [selected_base_binding position terms types] at checked
  exact checked

theorem prepared_input_query_base_step (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (built : prepare program = .ok prepared)
    (signatures : table.signatures = provider.signatures) (index : Nat) (authored : RewriteRule)
    (atBase : baseLanguage.rewrites[index]? = some authored) (source target : Pattern) (assignment : Bindings)
    (relation : String) (arguments : List Pattern) (rowIndex : Nat) (signature : GeneralPremise.Signature)
    (premise : authored.premises = [.relationQuery relation arguments])
    (rightBound : ∀ name ∈ authored.right.freeFvarNames, name ∈ authored.left.freeFvarNames)
    (queryShapes : ∀ argument ∈ arguments, VectorFirstOrder argument)
    (queryBound : ∀ argument ∈ arguments, ∀ name ∈ argument.freeFvarNames, name ∈ authored.left.freeFvarNames)
    (closed : source.freeFvarNames = [])
    (sourceTyped : OpenPatternWellSorted (GeneralPlanEnvironment.environment (epochPlan prepared table)).language
      (epochPlan prepared table).snapshot.free [] (.base "MlConfig") source)
    (targetTyped : OpenPatternWellSorted (GeneralPlanEnvironment.environment (epochPlan prepared table)).language
      (epochPlan prepared table).snapshot.free [] (.base "MlConfig") target)
    (input : applyBindings assignment authored.left = source) (output : applyBindings assignment authored.right = target)
    (rowAt : table.rows[rowIndex]? = some ⟨relation, arguments.map (applyBindings assignment)⟩)
    (signatureAt : GeneralPremise.signature? table relation arguments.length = some signature)
    (modes : signature.modes = arguments.map (fun _ => RelationArgMode.input))
    (rowTyped : GeneralPremise.RowTyped (GeneralPlanEnvironment.environment (epochPlan prepared table)).language
      (epochPlan prepared table).snapshot.free [] signature ⟨relation, arguments.map (applyBindings assignment)⟩) :
    (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step source target := by
  obtain ⟨_, _, terms, types, dispatch, functions, _, _, allRows⟩ := prepare_readback program prepared built
  have inProgram : authored ∈ prepared.compiled.rewrites := by
    rw [allRows]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_of_getElem? atBase)))
  obtain ⟨ordinal, row, selected, same, _⟩ := whole_plan_row prepared authored inProgram (prepared_plan_complete program prepared built)
  have position : (epochPlan prepared table).rules[ordinal]? = some row := by
    rw [epoch_rules prepared table signatures]
    exact selected
  have declared : baseLanguage.rewrites[index]? = some row.authored := by rw [same]; exact atBase
  let runtime := GeneralPlanEnvironment.environment (epochPlan prepared table)
  have grammar : runtime.language.terms = baseLanguage.terms := terms
  have binding := selected_base_binding position terms types
  obtain ⟨leftShape, rightShape⟩ := base_vector_shapes row.authored (List.mem_of_getElem? declared)
  have admitted := (GeneralRuleBindingInference.compile_admitted binding).1
  have schema := base_binding_schema_transport runtime.language grammar row.authored row.binding (List.mem_of_getElem? declared) binding
  have actualInput : applyBindings assignment row.rule.left = source := by simpa only [GeneralExecutionAdmission.RulePlan.rule,
    GeneralRuleBindingInference.BindingPlan.elaborate, same] using input
  have actualOutput : applyBindings assignment row.rule.right = target := by simpa only [GeneralExecutionAdmission.RulePlan.rule,
    GeneralRuleBindingInference.BindingPlan.elaborate, same] using output
  have actualPremise : row.rule.premises = [.relationQuery relation arguments] := by simpa only [GeneralExecutionAdmission.RulePlan.rule,
    GeneralRuleBindingInference.BindingPlan.elaborate, same] using premise
  have coherent : ∀ queryIndex argument, arguments[queryIndex]? = some argument →
      NameCoherent row.rule (.premise 0 0 queryIndex) [] argument := by
    intro queryIndex argument queried suffix
    simp only [sitePattern?, actualPremise, List.getElem?_cons_zero, quantifiedBody?, Option.bind_eq_bind,
      Option.bind_some, queried, List.nil_append]
  obtain ⟨trace, captured, firing⟩ := vector_input_query_root_construct
    (GeneralPlanEnvironment.selected_rule (epochPlan prepared table) position)
    (GeneralPlanEnvironment.selected_specification (epochPlan prepared table) position) admitted
    (selected_base_zero position terms types declared)
    (base_label_deterministic runtime.language grammar) (base_collection_deterministic runtime.language grammar)
    leftShape rightShape schema actualPremise
    (by simpa only [GeneralExecutionAdmission.RulePlan.rule, GeneralRuleBindingInference.BindingPlan.elaborate, same] using rightBound)
    queryShapes
    (by simpa only [GeneralExecutionAdmission.RulePlan.rule, GeneralRuleBindingInference.BindingPlan.elaborate, same] using queryBound)
    coherent (vector_defined_of_closed_input leftShape assignment actualInput closed) sourceTyped targetTyped actualInput actualOutput
    rowAt signatureAt modes rowTyped
  exact GeneralOccurrenceSemantics.root_firing_step position rfl sourceTyped firing

#print axioms base_dependencies_checked
#print axioms selected_base_zero
#print axioms prepared_input_query_base_step

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
