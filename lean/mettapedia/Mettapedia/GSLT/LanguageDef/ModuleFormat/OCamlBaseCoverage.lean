import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlBaseSchemaTyping
import Mettapedia.OSLF.MeTTaIL.GeneralVectorCaptureTyping
import Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammarFirstOrder
import Mettapedia.OSLF.MeTTaIL.Complete.DeepRoot
import Mettapedia.OSLF.MeTTaIL.GeneralVectorDefinedInput
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlStateClosed

/-! Actual selected base rows cover their encoded source instances. Capture
typing is derived from the source and authored schema; it is not supplied as
a target-correctness premise. Execution/source declaration indices remain
separate.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding
open Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem base_vector_shapes (row : RewriteRule) (member : row ∈ baseLanguage.rewrites) :
    VectorFirstOrder row.left ∧ VectorFirstOrder row.right := by
  have checked : baseLanguage.rewrites.all (fun row => checkFirstOrder row.left && checkFirstOrder row.right) = true := by
    decide +kernel
  have both := Bool.and_eq_true_iff.mp (List.all_eq_true.mp checked row member)
  have lift : ∀ pattern : Pattern, FirstOrder pattern → VectorFirstOrder pattern := by
    intro pattern shape
    induction shape with
    | metavariable name => exact .metavariable name
    | constructor label arguments _ children => exact .constructor label arguments children
  exact ⟨lift _ (checkFirstOrder_sound both.1), lift _ (checkFirstOrder_sound both.2)⟩

theorem base_right_bound (row : RewriteRule) (member : row ∈ baseLanguage.rewrites) (premiseFree : row.premises = []) :
    ∀ name ∈ row.right.freeFvarNames, name ∈ row.left.freeFvarNames := by
  have checked : baseLanguage.rewrites.all (fun row =>
      !row.premises.isEmpty || row.right.freeFvarNames.all row.left.freeFvarNames.contains) = true := by cbv
  have bound := List.all_eq_true.mp checked row member
  simp only [premiseFree, List.isEmpty_nil, Bool.not_true, Bool.false_or] at bound
  intro name present
  exact List.contains_iff_mem.mp (List.all_eq_true.mp bound name present)

theorem base_source_firing_construct {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal index : Nat} {pool : List OCaml.MatchPattern}
    {sourceState targetState : OCaml.MachineState} {source target : Pattern} {assignment : Bindings}
    (position : plan.rules[ordinal]? = some row)
    (terms : plan.snapshot.language.terms = baseLanguage.terms)
    (authored : baseLanguage.rewrites[index]? = some row.authored)
    (compiled : GeneralRuleBindingInference.compile? baseLanguage row.authored = some row.binding)
    (premiseFree : row.authored.premises = [])
    (sourceEncoded : state? pool sourceState = some source)
    (targetEncoded : state? pool targetState = some target)
    (defined : Defined assignment row.authored.left.freeFvarNames)
    (input : applyBindings assignment row.authored.left = source)
    (output : applyBindings assignment row.authored.right = target) :
    ∃ trace captured, GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      source ordinal trace captured captured [] target := by
  let runtime := GeneralPlanEnvironment.environment plan
  have grammar : runtime.language.terms = baseLanguage.terms := terms
  have member := List.mem_of_getElem? authored
  obtain ⟨leftShape, rightShape⟩ := base_vector_shapes row.authored member
  have admitted := (GeneralRuleBindingInference.compile_admitted compiled).1
  have zero := GeneralRuleBindingInference.compile_binderFree_zero baseLanguage row.authored row.binding
    (by
      have checked : baseLanguage.rewrites.all (fun row => row.bindings.isNone) = true := by decide +kernel
      exact Option.isNone_iff_eq_none.mp (List.all_eq_true.mp checked row.authored member))
    (GeneralRuleBindingInference.vector_binderFree leftShape) (GeneralRuleBindingInference.vector_binderFree rightShape)
    premiseFree compiled
  have schema := base_binding_schema_transport runtime.language grammar row.authored row.binding member compiled
  exact vector_source_root_construct (GeneralPlanEnvironment.selected_rule plan position)
    (GeneralPlanEnvironment.selected_specification plan position) admitted zero
    (base_label_deterministic runtime.language grammar) (base_collection_deterministic runtime.language grammar)
    leftShape rightShape schema premiseFree (base_right_bound row.authored member premiseFree)
    defined (state?_open runtime.language grammar runtime.free [] pool sourceState source sourceEncoded)
    (state?_open runtime.language grammar runtime.free [] pool targetState target targetEncoded) input output

theorem base_source_eventually_published {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal index : Nat} {pool : List OCaml.MatchPattern}
    {sourceState targetState : OCaml.MachineState} {source target : Pattern} {assignment : Bindings}
    (position : plan.rules[ordinal]? = some row)
    (terms : plan.snapshot.language.terms = baseLanguage.terms)
    (authored : baseLanguage.rewrites[index]? = some row.authored)
    (compiled : GeneralRuleBindingInference.compile? baseLanguage row.authored = some row.binding)
    (premiseFree : row.authored.premises = [])
    (sourceEncoded : state? pool sourceState = some source)
    (targetEncoded : state? pool targetState = some target)
    (defined : Defined assignment row.authored.left.freeFvarNames)
    (input : applyBindings assignment row.authored.left = source)
    (output : applyBindings assignment row.authored.right = target) :
    ∃ work firing, firing ∈ (Complete.DeepRoot.run ⟨GeneralPlanEnvironment.environment plan, [], .base "MlConfig", source, ordinal⟩ work
      (Complete.DeepRoot.start ⟨GeneralPlanEnvironment.environment plan, [], .base "MlConfig", source, ordinal⟩)).publication ∧
      firing.target = target := by
  obtain ⟨trace, captured, valid⟩ := base_source_firing_construct position terms authored compiled premiseFree
    sourceEncoded targetEncoded defined input output
  let firing : Complete.DeepRoot.Firing := ⟨trace, captured, captured, [], target⟩
  obtain ⟨work, present⟩ := Complete.DeepRoot.complete_in_limit
    (request := ⟨GeneralPlanEnvironment.environment plan, [], .base "MlConfig", source, ordinal⟩)
    (firing := firing) valid
  exact ⟨work, firing, present, rfl⟩

#print axioms base_source_firing_construct
#print axioms base_source_eventually_published

theorem base_encoded_firing_construct {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal index : Nat} {pool : List OCaml.MatchPattern}
    {sourceState targetState : OCaml.MachineState} {source target : Pattern} {assignment : Bindings}
    (position : plan.rules[ordinal]? = some row)
    (terms : plan.snapshot.language.terms = baseLanguage.terms)
    (authored : baseLanguage.rewrites[index]? = some row.authored)
    (compiled : GeneralRuleBindingInference.compile? baseLanguage row.authored = some row.binding)
    (premiseFree : row.authored.premises = [])
    (sourceEncoded : state? pool sourceState = some source)
    (targetEncoded : state? pool targetState = some target)
    (input : applyBindings assignment row.authored.left = source)
    (output : applyBindings assignment row.authored.right = target) :
    ∃ trace captured, GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      source ordinal trace captured captured [] target := by
  have shape := (base_vector_shapes row.authored (List.mem_of_getElem? authored)).1
  have defined := vector_defined_of_closed_input shape assignment input (state?_closed pool sourceState source sourceEncoded)
  exact base_source_firing_construct position terms authored compiled premiseFree sourceEncoded targetEncoded defined input output

theorem base_encoded_settled_publication {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal index work : Nat} {pool : List OCaml.MatchPattern}
    {sourceState targetState : OCaml.MachineState} {source target : Pattern} {assignment : Bindings}
    (position : plan.rules[ordinal]? = some row)
    (terms : plan.snapshot.language.terms = baseLanguage.terms)
    (authored : baseLanguage.rewrites[index]? = some row.authored)
    (compiled : GeneralRuleBindingInference.compile? baseLanguage row.authored = some row.binding)
    (premiseFree : row.authored.premises = [])
    (sourceEncoded : state? pool sourceState = some source)
    (targetEncoded : state? pool targetState = some target)
    (input : applyBindings assignment row.authored.left = source)
    (output : applyBindings assignment row.authored.right = target)
    (done : (Complete.DeepRoot.run ⟨GeneralPlanEnvironment.environment plan, [], .base "MlConfig", source, ordinal⟩ work
      (Complete.DeepRoot.start ⟨GeneralPlanEnvironment.environment plan, [], .base "MlConfig", source, ordinal⟩)).complete = true) :
    ∃ firing, firing ∈ (Complete.DeepRoot.run ⟨GeneralPlanEnvironment.environment plan, [], .base "MlConfig", source, ordinal⟩ work
      (Complete.DeepRoot.start ⟨GeneralPlanEnvironment.environment plan, [], .base "MlConfig", source, ordinal⟩)).publication ∧
      firing.target = target := by
  obtain ⟨trace, captured, valid⟩ := base_encoded_firing_construct position terms authored compiled premiseFree
    sourceEncoded targetEncoded input output
  let firing : Complete.DeepRoot.Firing := ⟨trace, captured, captured, [], target⟩
  exact ⟨firing, Complete.DeepRoot.exact_of_complete _ work done valid, rfl⟩

#print axioms base_encoded_firing_construct
#print axioms base_encoded_settled_publication

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
