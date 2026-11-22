import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CheckStability
import Mettapedia.Logic.WitnessObservations
import Mettapedia.Logic.ProjectedObservations

/-! Converses for the actual constraint-rewriting observation interfaces.
Exact counts characterize occurrence coverage model by model; preservation
of protected solution projections characterizes all observable queries. -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

open Mettapedia.Logic

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO}

namespace Check

theorem coversMatches_iff_all_model_counts [DecidableEq O] (A : SubstitutionAction T S)
    (equations : EquationStore T) (label : O → T) (visible world : Finset O) (pattern : T)
    (included : visible ⊆ world) :
    CoversMatches A equations label visible world pattern ↔
      ∀ σ, A.Models σ equations →
        («matches» A σ label visible pattern).card = («matches» A σ label world pattern).card := by
  classical
  constructor
  · intro covers σ model
    exact congrArg Finset.card (region_eq_of_covered A included covers σ model)
  · intro counts σ model
    have covered := (WitnessObservations.covers_iff_count_eq visible world
      (fun occurrence => A.E (A.apply σ pattern) (A.apply σ (label occurrence))) included).mpr (counts σ model)
    exact covered

theorem coversMatches_iff_all_filtered_absence [DecidableEq O] (A : SubstitutionAction T S)
    (equations : EquationStore T) (label : O → T) (visible world : Finset O) (pattern : T)
    (included : visible ⊆ world) :
    CoversMatches A equations label visible world pattern ↔
      ∀ σ, A.Models σ equations → ∀ test : O → Prop,
        (¬ ∃ occurrence ∈ visible, A.E (A.apply σ pattern) (A.apply σ (label occurrence)) ∧ test occurrence) ↔
        (¬ ∃ occurrence ∈ world, A.E (A.apply σ pattern) (A.apply σ (label occurrence)) ∧ test occurrence) := by
  constructor
  · intro covered σ model
    exact (WitnessObservations.covers_iff_all_filtered_absence visible world _ included).mp (covered σ model)
  · intro preserved σ model
    exact (WitnessObservations.covers_iff_all_filtered_absence visible world _ included).mpr (preserved σ model)

end Check

theorem protected_projection_iff_possible (A : SubstitutionAction T S) {Observation : Type*}
    (protectedView : S → Observation) (before after : EquationStore T) :
    protectedView '' {σ | A.Models σ before} = protectedView '' {σ | A.Models σ after} ↔
      ∀ query : Observation → Prop, (∃ σ, A.Models σ before ∧ query (protectedView σ)) ↔
        (∃ σ, A.Models σ after ∧ query (protectedView σ)) :=
  ProjectedObservations.image_eq_iff_possible _ _ _ _

theorem protected_projection_iff_necessary (A : SubstitutionAction T S) {Observation : Type*}
    (protectedView : S → Observation) (before after : EquationStore T) :
    protectedView '' {σ | A.Models σ before} = protectedView '' {σ | A.Models σ after} ↔
      ∀ query : Observation → Prop, A.Entails before (fun σ => query (protectedView σ)) ↔
        A.Entails after (fun σ => query (protectedView σ)) :=
  ProjectedObservations.image_eq_iff_necessary _ _ _ _

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
