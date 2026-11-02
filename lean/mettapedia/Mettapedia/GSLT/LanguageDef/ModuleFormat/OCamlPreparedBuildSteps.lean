import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedBaseSteps
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlAdministrativeRequestTyping
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlBuildReadout

/-! Final gather and constructor-building steps of the actual prepared
occurrence GSLT. The administrative build configuration keeps every ordered
argument and the source continuation before construction or service entry.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem prepared_last_gather_step (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (kind : OCaml.Build) (actual : OCaml.Value)
    (capturedEnvironment : OCaml.Environment) (suffix : List OCaml.Value) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (resolved : continuation? (patterns program) rest = some encodedRest) :
    (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlReturn" [value actual, node "MlKBuild" [build kind, codes [], environment capturedEnvironment, valueList suffix, encodedRest]])
      (node "MlBuildConfig" [build kind, valueList (actual :: suffix), encodedRest]) := by
  have grammar : (GeneralPlanEnvironment.environment (epochPlan prepared table)).language.terms = baseLanguage.terms :=
    (prepare_readback program prepared built).2.2.1
  have encoded : state? (patterns program) (.returned actual (.gather kind [] capturedEnvironment suffix :: rest)) =
      some (node "MlReturn" [value actual, node "MlKBuild" [build kind, codes [], environment capturedEnvironment, valueList suffix, encodedRest]]) := by
    simp only [state?, continuation?, frame?, resolved, List.map_nil, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  apply prepared_pure_base_step program prepared table built signatures 15
    (baseLanguage.rewrites[15]'(by decide +kernel)) (by exact List.getElem?_eq_getElem (by decide +kernel))
  · exact state?_closed _ _ _ encoded
  · exact state?_open _ grammar _ [] _ _ _ encoded
  · exact build_request_open _ grammar _ kind (actual :: suffix) (patterns program) rest encodedRest resolved
  · exact return_build_last_instance (value actual) (build kind) (environment capturedEnvironment) (valueList suffix) encodedRest

theorem prepared_tuple_build_step (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (items : List OCaml.Value) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (resolved : continuation? (patterns program) rest = some encodedRest) :
    (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlBuildConfig" [build .tuple, valueList items, encodedRest])
      (node "MlReturn" [value (.tuple items), encodedRest]) := by
  have grammar : (GeneralPlanEnvironment.environment (epochPlan prepared table)).language.terms = baseLanguage.terms :=
    (prepare_readback program prepared built).2.2.1
  have encoded : state? (patterns program) (.returned (.tuple items) rest) =
      some (node "MlReturn" [value (.tuple items), encodedRest]) := by
    simp only [state?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  apply prepared_pure_base_step program prepared table built signatures 16
    (baseLanguage.rewrites[16]'(by decide +kernel)) (by exact List.getElem?_eq_getElem (by decide +kernel))
  · exact build_request_closed .tuple items (patterns program) rest encodedRest resolved
  · exact build_request_open _ grammar _ .tuple items (patterns program) rest encodedRest resolved
  · exact state?_open _ grammar _ [] _ _ _ encoded
  · exact build_tuple_instance (valueList items) encodedRest

theorem prepared_variant_build_step (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (typeId constructor : Nat) (items : List OCaml.Value)
    (rest : OCaml.Continuation) (encodedRest : Pattern) (built : prepare program = .ok prepared)
    (signatures : table.signatures = provider.signatures) (resolved : continuation? (patterns program) rest = some encodedRest) :
    (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlBuildConfig" [build (.variant typeId constructor), valueList items, encodedRest])
      (node "MlReturn" [value (.variant typeId constructor items), encodedRest]) := by
  have grammar : (GeneralPlanEnvironment.environment (epochPlan prepared table)).language.terms = baseLanguage.terms :=
    (prepare_readback program prepared built).2.2.1
  have encoded : state? (patterns program) (.returned (.variant typeId constructor items) rest) =
      some (node "MlReturn" [value (.variant typeId constructor items), encodedRest]) := by
    simp only [state?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  apply prepared_pure_base_step program prepared table built signatures 17
    (baseLanguage.rewrites[17]'(by decide +kernel)) (by exact List.getElem?_eq_getElem (by decide +kernel))
  · exact build_request_closed (.variant typeId constructor) items (patterns program) rest encodedRest resolved
  · exact build_request_open _ grammar _ (.variant typeId constructor) items (patterns program) rest encodedRest resolved
  · exact state?_open _ grammar _ [] _ _ _ encoded
  · exact build_variant_instance (tag typeId constructor) (valueList items) encodedRest

theorem prepared_primitive_build_step (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (operator : OCaml.Primitive) (arguments : List OCaml.Value)
    (rest : OCaml.Continuation) (encodedRest : Pattern) (built : prepare program = .ok prepared)
    (signatures : table.signatures = provider.signatures) (resolved : continuation? (patterns program) rest = some encodedRest) :
    (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlBuildConfig" [build (.primitive operator), valueList arguments, encodedRest])
      (node "MlPrimitiveRequest" [primitive operator, valueList arguments, encodedRest]) := by
  have grammar : (GeneralPlanEnvironment.environment (epochPlan prepared table)).language.terms = baseLanguage.terms :=
    (prepare_readback program prepared built).2.2.1
  apply prepared_pure_base_step program prepared table built signatures 18
    (baseLanguage.rewrites[18]'(by decide +kernel)) (by exact List.getElem?_eq_getElem (by decide +kernel))
  · exact build_request_closed (.primitive operator) arguments (patterns program) rest encodedRest resolved
  · exact build_request_open _ grammar _ (.primitive operator) arguments (patterns program) rest encodedRest resolved
  · exact primitive_request_open _ grammar _ operator arguments (patterns program) rest encodedRest resolved
  · exact build_primitive_instance (primitive operator) (valueList arguments) encodedRest

#print axioms prepared_last_gather_step
#print axioms prepared_tuple_build_step
#print axioms prepared_variant_build_step
#print axioms prepared_primitive_build_step

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
