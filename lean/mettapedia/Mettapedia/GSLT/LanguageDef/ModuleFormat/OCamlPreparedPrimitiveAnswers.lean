import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedBaseSteps
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlAdministrativeRequestTyping
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlProviderMeaning

/-! Consumption of a source-authorized primitive result is an actual
prepared GSLT step. Values retain the continuation and faults halt at the
source fault; the provider's independent semantic meaning authorizes cache
answers rather than their typing alone.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem prepared_primitive_answer_step (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (result : OCaml.Result) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (resolved : continuation? (patterns program) rest = some encodedRest) :
    ∃ target, state? (patterns program) (finishPrimitive result rest) = some target ∧
      (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
        (node "MlPrimitiveReturned" [primitiveResult result, encodedRest]) target := by
  have grammar : (GeneralPlanEnvironment.environment (epochPlan prepared table)).language.terms = baseLanguage.terms :=
    (prepare_readback program prepared built).2.2.1
  have sourceClosed : (node "MlPrimitiveReturned" [primitiveResult result, encodedRest]).freeFvarNames = [] := by
    have typed := primitive_returned_open baseLanguage rfl Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty
      result (patterns program) rest encodedRest resolved
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro name present
    obtain ⟨_, impossible⟩ := typed.1.freeType_of_mem_freeFvarNames_of_isObjectPattern typed.2.2.1 present
    cases impossible
  cases result with
  | ok actual =>
    have encoded : state? (patterns program) (.returned actual rest) = some (node "MlReturn" [value actual, encodedRest]) := by
      simp only [state?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    refine ⟨_, encoded, ?_⟩
    apply prepared_pure_base_step program prepared table built signatures 20
      (baseLanguage.rewrites[20]'(by decide +kernel)) (by exact List.getElem?_eq_getElem (by decide +kernel))
    · exact sourceClosed
    · exact primitive_returned_open _ grammar _ (.ok actual) (patterns program) rest encodedRest resolved
    · exact state?_open _ grammar _ [] _ _ _ encoded
    · exact primitive_value_instance (value actual) encodedRest
  | error error =>
    have encoded : state? (patterns program) (.halted (.error error)) = some (node "MlFault" [fault error]) := rfl
    refine ⟨_, encoded, ?_⟩
    apply prepared_pure_base_step program prepared table built signatures 21
      (baseLanguage.rewrites[21]'(by decide +kernel)) (by exact List.getElem?_eq_getElem (by decide +kernel))
    · exact sourceClosed
    · exact primitive_returned_open _ grammar _ (.error error) (patterns program) rest encodedRest resolved
    · exact state?_open _ grammar _ [] _ _ _ encoded
    · exact primitive_fault_instance (fault error) encodedRest

theorem prepared_cached_primitive_consumption (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (operator : OCaml.Primitive) (arguments : List OCaml.Value)
    (result : OCaml.Result) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (meaning : ProviderMeaning (patterns program) table) (present : primitiveRow operator arguments result ∈ table.rows)
    (resolved : continuation? (patterns program) rest = some encodedRest) :
    OCaml.finishBuild program (.primitive operator) arguments rest = .ok (finishPrimitive result rest) ∧
      ∃ target, state? (patterns program) (finishPrimitive result rest) = some target ∧
        (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
          (node "MlPrimitiveReturned" [primitiveResult result, encodedRest]) target :=
  ⟨cached_primitive_authorized table program operator arguments result rest meaning.1 present,
    prepared_primitive_answer_step program prepared table result rest encodedRest built signatures resolved⟩

#print axioms prepared_primitive_answer_step
#print axioms prepared_cached_primitive_consumption

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
