import Mettapedia.GSLT.Dynamics.StepSpendObservation
import Mettapedia.GSLT.LanguageDef.GradedLanguageDef

/-!
# Graded LanguageDef semantics through observation disciplines

The free and inert graded-language policies already define `GSLT.StepSpend`
objects over the denoted five-field language.  This module exposes those
objects through the generic occurrence observation discipline.  It introduces
no second graded semantics: `toFreeGSLT` and `toInertGSLT` remain the existing
generic spend lifts.
-/

namespace Mettapedia.GSLT.LanguageDef.GradedObservationDiscipline

open Mettapedia.GSLT
open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.Dynamics.StepSpendObservation
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.GradedLanguageDef
open Mettapedia.GSLT.LanguageDef.TotalGSLT
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Syntax

variable {Grade : Type} (graded : GradedLanguageDef Grade)
variable (laws : GradedReductionRespectsEquations graded.toLanguageDef)

/-- The free policy observed through its exact graded occurrences. -/
def free [Monoid Grade] :
    ObservationDiscipline
      (Occurrence (graded.freeSpend laws)) :=
  StepSpendObservation.discipline (graded.freeSpend laws)

/-- The inert policy observed through only explicitly graded occurrences. -/
def inert [Monoid Grade] :
    ObservationDiscipline
      (Occurrence (graded.inertSpend laws)) :=
  StepSpendObservation.discipline (graded.inertSpend laws)

/-- Every authored base step has a free-policy occurrence. -/
theorem free_observes_every_base_step [One Grade]
    {source target : Pattern}
    (step : (graded.baseGSLT laws).Step source target) :
    Nonempty (OccurrenceAt (graded.freeSpend laws) source target) :=
  occurrence_nonempty_of_total (graded.freeSpend laws)
    (graded.freeGrading_total laws) step

/-- Coverage is exactly what grants the inert policy the same observation
totality. -/
theorem inert_observes_every_base_step_of_covers
    (covers : graded.Covers) {source target : Pattern}
    (step : (graded.baseGSLT laws).Step source target) :
    Nonempty (OccurrenceAt (graded.inertSpend laws) source target) :=
  occurrence_nonempty_of_total (graded.inertSpend laws)
    (graded.inertGrading_total_of_covers laws covers) step

/-- Negative control: an ungraded firing has no inert observation occurrence.
The observation layer does not manufacture authority absent from the table. -/
theorem inert_has_no_occurrence_of_ungraded
    {source target : Pattern}
    (ungraded : forall rule,
      RootRuleStep (engineBasePremises RelationEnv.empty)
        graded.toLanguageDef rule source target ->
      graded.ruleGrade? rule = none) :
    ¬ Nonempty (OccurrenceAt (graded.inertSpend laws) source target) := by
  rintro ⟨occurrence⟩
  obtain ⟨rule, root, gradeEquation⟩ := occurrence.graded
  rw [ungraded rule root] at gradeEquation
  cases gradeEquation

/-- The existing free graded step is precisely an observed occurrence plus
the monoidal accumulator update. -/
theorem free_step_iff_observed_occurrence [Monoid Grade]
    {source target : Pattern × Grade} :
    (graded.toFreeGSLT laws).Step source target ↔
      ∃ occurrence : OccurrenceAt
          (graded.freeSpend laws) source.1 target.1,
        target.2 = source.2 * occurrence.grade :=
  spendLift_step_iff_occurrence (graded.freeSpend laws)

/-- The same characterization holds for the partial inert policy; it simply
has fewer occurrences when the authored table is incomplete. -/
theorem inert_step_iff_observed_occurrence [Monoid Grade]
    {source target : Pattern × Grade} :
    (graded.toInertGSLT laws).Step source target ↔
      ∃ occurrence : OccurrenceAt
          (graded.inertSpend laws) source.1 target.1,
        target.2 = source.2 * occurrence.grade :=
  spendLift_step_iff_occurrence (graded.inertSpend laws)

end Mettapedia.GSLT.LanguageDef.GradedObservationDiscipline
