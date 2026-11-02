import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadCompatibleResourceLifting

/-! # Actual ordinary firings project to source-compatible resource instances -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadCompatibleResourcePlanning

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open PositiveResourceProjection (realized)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  {A : SubstitutionAction T S} {assignment : S} {label : O → T}

def planOfSelection (structural : A.E = Eq) {selection : Selection O} {rule : RuleInstance T}
    {before : Configuration T O} (valid : selection.Valid A label rule before)
    (solved : A.Models assignment (selection.result label rule before).equations) :
    ReadPlan A assignment label rule where
  prototype := selection.read
  compatible := by
    have matching := (Selection.models_problem A valid solved).2.2.1
    simpa only [structural, realized] using matching

theorem resource_firing [DecidableEq T] (structural : A.E = Eq)
    (source : AdmittedRule A assignment) {selection : Selection O} {before : Configuration T O}
    (valid : selection.Valid A label source.rule before)
    (solved : A.Models assignment (selection.result label source.rule before).equations) :
    (resources A assignment label).Enables (labels (realized A assignment label) before.present)
        (site := ⟨source⟩) ⟨planOfSelection structural valid solved⟩ ∧
      labels (realized A assignment label) (selection.result label source.rule before).present =
        (resources A assignment label).fire (labels (realized A assignment label) before.present)
          (site := ⟨source⟩) ⟨planOfSelection structural valid solved⟩ := by
  exact PositiveResourceProjection.resource_firing A structural valid solved

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadCompatibleResourcePlanning
