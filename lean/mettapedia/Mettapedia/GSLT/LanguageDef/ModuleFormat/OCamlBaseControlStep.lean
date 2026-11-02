import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedBaseSteps
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlControlPointTyping

/-! An authored base instance between source control points constructs an
actual prepared step. Preparation supplies admission and source control
points supply closed typing at both endpoints.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem prepared_base_control_step (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    {source next : OCaml.MachineState} {config target : Pattern} {rank nextRank : Nat} (index : Nat)
    (inside : index < baseLanguage.rewrites.length) (built : prepare program = .ok prepared)
    (signatures : table.signatures = provider.signatures)
    (point : ControlPoint program source config rank) (nextPoint : ControlPoint program next target nextRank)
    (instanceAt : BaseRuleInstance index config target) :
    (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step config target := by
  have grammar : (GeneralPlanEnvironment.environment (epochPlan prepared table)).language.terms = baseLanguage.terms :=
    (prepare_readback program prepared built).2.2.1
  exact prepared_pure_base_step program prepared table built signatures index (baseLanguage.rewrites[index]'inside)
    (List.getElem?_eq_getElem inside) config target
    (control_point_epoch_checked program prepared table built point).1 (point.open _ grammar _)
    (nextPoint.open _ grammar _) instanceAt

#print axioms prepared_base_control_step

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
