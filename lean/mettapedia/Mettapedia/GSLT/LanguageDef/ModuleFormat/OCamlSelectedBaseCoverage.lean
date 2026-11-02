import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceTransitionCoverage
import Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammarTransport

/-! Actual selected admission rows retain the binding inference used by
the source vocabulary. Base-row coverage derives that evidence from the
compiled plan's origin instead of asking a caller to reconstruct it.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding
open Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

theorem selected_base_binding {snapshot : GeneralExecutionAdmission.Snapshot}
    {permissions : GeneralExecutionAdmission.Permissions} {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat}
    (position : (GeneralExecutionAdmission.compile snapshot permissions).rules[ordinal]? = some row)
    (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames) :
    GeneralRuleBindingInference.compile? baseLanguage row.authored = some row.binding := by
  obtain ⟨actual, index, _, _, selected⟩ :=
    GeneralExecutionAdmission.compiled_rule_origin (List.mem_of_getElem? position)
  obtain ⟨_, authored, compiled, _, _, _⟩ := GeneralExecutionAdmission.rulePlan_readout selected
  rw [← authored] at compiled
  rw [GeneralRuleBindingInference.compile?_transport terms types] at compiled
  exact compiled

theorem selected_base_firing_construct {snapshot : GeneralExecutionAdmission.Snapshot}
    {permissions : GeneralExecutionAdmission.Permissions} {row : GeneralExecutionAdmission.RulePlan} {ordinal index : Nat}
    {pool : List OCaml.MatchPattern} {sourceState targetState : OCaml.MachineState} {source target : Pattern}
    {assignment : Bindings}
    (position : (GeneralExecutionAdmission.compile snapshot permissions).rules[ordinal]? = some row)
    (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames)
    (authored : baseLanguage.rewrites[index]? = some row.authored)
    (premiseFree : row.authored.premises = [])
    (sourceEncoded : state? pool sourceState = some source)
    (targetEncoded : state? pool targetState = some target)
    (input : applyBindings assignment row.authored.left = source)
    (output : applyBindings assignment row.authored.right = target) :
    ∃ trace captured, GeneralPremise.RootFiring
      (GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions)) [] (.base "MlConfig")
      source ordinal trace captured captured [] target :=
  base_encoded_firing_construct position terms authored (selected_base_binding position terms types)
    premiseFree sourceEncoded targetEncoded input output

theorem selected_base_instance_coverage {snapshot : GeneralExecutionAdmission.Snapshot}
    {permissions : GeneralExecutionAdmission.Permissions} {row : GeneralExecutionAdmission.RulePlan} {ordinal index : Nat}
    {pool : List OCaml.MatchPattern} {sourceState targetState : OCaml.MachineState} {source target : Pattern}
    (position : (GeneralExecutionAdmission.compile snapshot permissions).rules[ordinal]? = some row)
    (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames)
    (authored : baseLanguage.rewrites[index]? = some row.authored)
    (sourceEncoded : state? pool sourceState = some source)
    (targetEncoded : state? pool targetState = some target)
    (realization : BaseRuleInstance index source target) :
    ∃ trace captured, GeneralPremise.RootFiring
      (GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions)) [] (.base "MlConfig")
      source ordinal trace captured captured [] target :=
  base_instance_encoded_coverage position terms authored (selected_base_binding position terms types)
    sourceEncoded targetEncoded realization

#print axioms selected_base_binding
#print axioms selected_base_instance_coverage

theorem selected_pure_base_zero {snapshot : GeneralExecutionAdmission.Snapshot}
    {permissions : GeneralExecutionAdmission.Permissions} {row : GeneralExecutionAdmission.RulePlan} {ordinal index : Nat}
    (position : (GeneralExecutionAdmission.compile snapshot permissions).rules[ordinal]? = some row)
    (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames)
    (authored : baseLanguage.rewrites[index]? = some row.authored) (premiseFree : row.authored.premises = []) :
    GeneralPremise.checkZeroDependencies row.binding.spec = true := by
  have member := List.mem_of_getElem? authored
  obtain ⟨leftShape, rightShape⟩ := base_vector_shapes row.authored member
  apply GeneralRuleBindingInference.compile_binderFree_zero baseLanguage row.authored row.binding
  · have checked : baseLanguage.rewrites.all (fun row => row.bindings.isNone) = true := by decide +kernel
    exact Option.isNone_iff_eq_none.mp (List.all_eq_true.mp checked row.authored member)
  · exact GeneralRuleBindingInference.vector_binderFree leftShape
  · exact GeneralRuleBindingInference.vector_binderFree rightShape
  · exact premiseFree
  · exact selected_base_binding position terms types

theorem selected_cons_head_root_iff {snapshot : GeneralExecutionAdmission.Snapshot}
    {permissions : GeneralExecutionAdmission.Permissions} {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat}
    {pool : List OCaml.MatchPattern} {head tail : OCaml.Value} {rest : OCaml.Continuation} {encodedRest target : Pattern}
    (position : (GeneralExecutionAdmission.compile snapshot permissions).rules[ordinal]? = some row)
    (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames)
    (authored : baseLanguage.rewrites[13]? = some row.authored)
    (resolved : continuation? pool rest = some encodedRest) :
    (∃ trace captured completed history,
      GeneralPremise.RootFiring
        (GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions)) [] (.base "MlConfig")
        (node "MlReturn" [value head, node "MlKConsHead" [value tail, encodedRest]]) ordinal trace captured completed history target) ↔
      target = node "MlReturn" [value (.cons head tail), encodedRest] := by
  have premiseFree : row.authored.premises = [] := by
    have fields : (baseLanguage.rewrites[13]?).map RewriteRule.premises = some [] := by decide +kernel
    rw [authored] at fields
    exact Option.some.inj fields
  exact cons_head_root_iff position terms authored (selected_base_binding position terms types)
    (selected_pure_base_zero position terms types authored premiseFree) resolved

#print axioms selected_cons_head_root_iff

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
