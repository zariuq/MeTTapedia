import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEncodedShapes
import Mettapedia.OSLF.MeTTaIL.GeneralVectorTypedMatch
import Mettapedia.OSLF.MeTTaIL.GeneralLanguageTyping
import Mettapedia.GSLT.LanguageDef.RestAwareLanguageTransport

/-! The actual inferred binding contexts of the authored O0 base rows type
their left schemas. Certificates are computed over the declarations and
then transported only along equality of the grammar vocabulary.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding
open Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

def baseBindingSchemasChecked : Bool := baseLanguage.rewrites.all fun row =>
  match GeneralRuleBindingInference.compile? baseLanguage row with
  | none => false
  | some binding =>
      let elaborated := binding.elaborate row
      Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkSchemaHasType baseLanguage
        (FreeTypeContext.ofList elaborated.typeContext) [] elaborated.left (.base "MlConfig")

set_option cbv.maxSteps 2000000 in
theorem baseBindingSchemas_checked : baseBindingSchemasChecked = true := by cbv

theorem base_binding_schema_typed (row : RewriteRule) (binding : GeneralRuleBindingInference.BindingPlan)
    (member : row ∈ baseLanguage.rewrites)
    (compiled : GeneralRuleBindingInference.compile? baseLanguage row = some binding) :
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType baseLanguage
      (FreeTypeContext.ofList (binding.elaborate row).typeContext) [] row.left (.base "MlConfig") := by
  have checked := List.all_eq_true.mp baseBindingSchemas_checked row member
  rw [compiled] at checked
  exact Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkSchemaHasType_sound checked

theorem base_binding_schema_transport (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (row : RewriteRule) (binding : GeneralRuleBindingInference.BindingPlan)
    (member : row ∈ baseLanguage.rewrites)
    (compiled : GeneralRuleBindingInference.compile? baseLanguage row = some binding) :
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType language
      (FreeTypeContext.ofList (binding.elaborate row).typeContext) [] row.left (.base "MlConfig") :=
  Mettapedia.GSLT.LanguageDef.RestAwareTyping.type_transport terms.symm (base_binding_schema_typed row binding member compiled)

theorem base_label_deterministic (language : LanguageDef) (terms : language.terms = baseLanguage.terms) :
    LabelDeterministic language := by
  have labels : (baseLanguage.terms.map GrammarRule.label).Nodup := by decide +kernel
  intro first second firstMember secondMember same
  rw [terms] at firstMember secondMember
  exact List.inj_on_of_nodup_map labels firstMember secondMember same

theorem base_collection_deterministic (language : LanguageDef) (terms : language.terms = baseLanguage.terms) :
    CollectionChoiceDeterministic language := by
  apply collectionChoiceDeterministic_of_check
  rw [terms]
  decide +kernel

#print axioms base_binding_schema_typed

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
