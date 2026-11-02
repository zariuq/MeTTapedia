import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlControlPointCanonical
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlAdministrativeRequestTyping
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSelectionRequestTyping
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlFreeNames

/-! All source control points are closed, well-sorted inputs to the actual
prepared runner, including configurations between ordinary source states.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem ControlPoint.open {program : OCaml.Program} {source : OCaml.MachineState} {config : Pattern} {rank : Nat}
    (point : ControlPoint program source config rank) (language : LanguageDef)
    (terms : language.terms = baseLanguage.terms) (free : FreeTypeContext) :
    OpenPatternWellSorted language free [] (.base "MlConfig") config := by
  have shape := point.vector
  cases point with
  | state encoded => exact state?_open language terms free [] _ _ _ encoded
  | application resolved _ => exact apply_request_open language terms free _ _ _ _ _ resolved
  | @matchOne index parameter argument body captured rest encodedRest indexed resolved =>
    apply typed_node_open shape
    exact nonbare_constructor_typed terms
      [("pattern", .base "MlPattern"), ("value", .base "MlValue"), ("body", .base "MlCode"),
        ("environment", .base "MlEnvironment"), ("continuation", .base "MlContinuation")] _ (by decide +kernel)
      (.cons (patternId_typed language terms free [] index) (.cons (value_typed language terms free [] argument)
        (.cons (code_typed language terms free [] body) (.cons (environment_typed language terms free [] captured)
          (.cons (continuation?_typed language terms free [] _ rest encodedRest resolved) .nil)))))
  | select listed resolved _ => exact select_request_open language terms free _ _ _ _ _ _ _ listed resolved
  | @clause index clause clauses later argument captured rest encodedRest next indexed listed resolved selected =>
    apply typed_node_open shape
    exact nonbare_constructor_typed terms
      [("pattern", .base "MlPattern"), ("value", .base "MlValue"), ("body", .base "MlCode"), ("later", .base "MlClauses"),
        ("environment", .base "MlEnvironment"), ("continuation", .base "MlContinuation")] _ (by decide +kernel)
      (.cons (patternId_typed language terms free [] index) (.cons (value_typed language terms free [] argument)
        (.cons (code_typed language terms free [] clause.body) (.cons (clauseList?_typed language terms free [] _ clauses later listed)
          (.cons (environment_typed language terms free [] captured)
            (.cons (continuation?_typed language terms free [] _ rest encodedRest resolved) .nil))))))
  | build resolved _ => exact build_request_open language terms free _ _ _ _ _ resolved
  | primitive resolved _ => exact primitive_request_open language terms free _ _ _ _ _ resolved
  | answer resolved => exact primitive_returned_open language terms free _ _ _ _ resolved

theorem control_point_epoch_checked (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    {source : OCaml.MachineState} {config : Pattern} {rank : Nat}
    (built : prepare program = .ok prepared) (point : ControlPoint program source config rank) :
    config.freeFvarNames = [] ∧ Complete.Classes.Checked (epochPlan prepared table) [] (.base "MlConfig") config := by
  have grammar : (GeneralPlanEnvironment.environment (epochPlan prepared table)).language.terms = baseLanguage.terms :=
    (prepare_readback program prepared built).2.2.1
  exact ⟨vector_typed_closed point.vector (point.open baseLanguage rfl FreeTypeContext.empty).1,
    checkOpenPatternWellSorted_complete (point.open _ grammar _)⟩

#print axioms ControlPoint.open
#print axioms control_point_epoch_checked

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
