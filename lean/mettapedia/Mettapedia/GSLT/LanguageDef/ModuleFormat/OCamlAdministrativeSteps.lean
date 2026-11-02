import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlAdministrativePreservation
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCanonicalState
import Mettapedia.OSLF.MeTTaIL.GeneralRootReceiptReadout
import Mettapedia.OSLF.MeTTaIL.Complete.Run

/-! Equation-saturated prepared steps preserve administrative source control.
The actual receipt supplies its selected root row; O0's empty authored
equation table removes representative changes without assuming them away.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem epoch_compiled_equations_empty (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (built : prepare program = .ok prepared) :
    (epochPlan prepared table).equations = [] := by
  change (GeneralExecutionAdmission.selectedEquations (epochSnapshot prepared table) permissions).filterMap _ = []
  have selected : GeneralExecutionAdmission.selectedEquations (epochSnapshot prepared table) permissions = [] := by
    exact prepared_no_equations program prepared built
  rw [selected]
  rfl

theorem administrative_step_preserves_source (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) {source : OCaml.MachineState} {config target : Pattern} {rank : Nat}
    (built : prepare program = .ok prepared) (invariant : SourceProviderInvariant (patterns program) table)
    (point : ControlPoint program source config rank) (positive : 0 < rank)
    (step : (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step config target) :
    ∃ nextRank, ControlPoint program source target nextRank ∧ nextRank < rank := by
  obtain ⟨receipt, valid, same⟩ := Complete.Run.valid_of_step (epochPlan prepared table) [] (.base "MlConfig")
    (epoch_compiled_equations_empty program prepared table built) step
  obtain ⟨position, firing⟩ := GeneralRuleJobs.rootOnly_receipt (plan := epochPlan prepared table) rfl valid
  rw [same] at firing
  exact administrative_firing_preserves_source program prepared table built invariant point positive position firing

#print axioms epoch_compiled_equations_empty
#print axioms administrative_step_preserves_source

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
