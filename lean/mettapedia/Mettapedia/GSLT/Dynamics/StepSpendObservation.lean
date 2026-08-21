import Mettapedia.GSLT.Core.GSLTConstructions
import Mettapedia.GSLT.Dynamics.ObservationDiscipline

/-!
# Step spending as an observation discipline

`GSLT.StepSpend` is the proof-relevant bridge between authored execution and
an accumulated grade.  This module exposes its exact graded occurrences as an
observation discipline.  The generic `spendLift` is then characterized by one
base occurrence together with the monoidal update of its accumulator.

This places graded `LanguageDef` semantics inside the general observation
architecture: the base GSLT determines execution, `StepSpend` supplies
occurrences, and a monoidal readout internalizes those occurrences in the
state.  A partial grading remains partial; reflection is obtained only from
the existing explicit `StepSpend.Total` obligation.
-/

namespace Mettapedia.GSLT.Dynamics.StepSpendObservation

open Mettapedia.GSLT
open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.Dynamics.IndexedEventValuation

universe uTerm uGrade

variable {system : GSLT} {Grade : Type uGrade}

/-- One exact occurrence of a graded base step. -/
structure Occurrence (spend : GSLT.StepSpend system Grade) where
  source : system.Term
  target : system.Term
  grade : Grade
  graded : spend.graded source target grade

/-- An occurrence indexed by its exact endpoints.  This form avoids
recovering dependent endpoint equalities after packaging an occurrence. -/
structure OccurrenceAt (spend : GSLT.StepSpend system Grade)
    (source target : system.Term) where
  grade : Grade
  graded : spend.graded source target grade

namespace Occurrence

/-- Forget the grade witness while retaining the authored base step. -/
def erase {spend : GSLT.StepSpend system Grade}
    (occurrence : Occurrence spend) : system.LabeledStep where
  source := occurrence.source
  target := occurrence.target
  step := spend.sound occurrence.graded

end Occurrence

namespace OccurrenceAt

/-- Forget endpoint indices into the history event type. -/
def toOccurrence {spend : GSLT.StepSpend system Grade}
    {source target : system.Term}
    (occurrence : OccurrenceAt spend source target) : Occurrence spend where
  source := source
  target := target
  grade := occurrence.grade
  graded := occurrence.graded

end OccurrenceAt

/-- Multiplicative accumulation as a total partial monoid. -/
def multiplicativePartialMonoid (Grade : Type uGrade) [Monoid Grade] :
    PartialMonoid Grade where
  unit := 1
  op := fun first second => some (first * second)
  unit_op := by simp
  op_unit := by simp
  op_assoc := by simp [mul_assoc]

/-- Collect exact graded occurrences by multiplying their grades in
chronological order. -/
def occurrenceValuation [Monoid Grade]
    (spend : GSLT.StepSpend system Grade) : Valuation (Occurrence spend) where
  Grade := Grade
  algebra := multiplicativePartialMonoid Grade
  grade := fun occurrence => some occurrence.grade

/-- The identity-valued observation discipline of exact graded occurrences. -/
def discipline [Monoid Grade]
    (spend : GSLT.StepSpend system Grade) :
    ObservationDiscipline (Occurrence spend) :=
  ObservationDiscipline.ofValuation (occurrenceValuation spend)

/-- Package exact graded occurrences as a rich event presentation over the
unchanged base GSLT. -/
def presented [Monoid Grade]
    (spend : GSLT.StepSpend system Grade) : PresentedObservation system where
  Event := Occurrence spend
  erase := Occurrence.erase
  discipline := discipline spend

@[simp] theorem singleton_observe [Monoid Grade]
    (spend : GSLT.StepSpend system Grade)
    (occurrence : Occurrence spend) :
    (discipline spend).observe [occurrence] = some occurrence.grade := by
  change
    ((multiplicativePartialMonoid Grade).op occurrence.grade
      (multiplicativePartialMonoid Grade).unit).bind some =
        some occurrence.grade
  rw [(multiplicativePartialMonoid Grade).op_unit]
  rfl

/-- Every observed occurrence is an authored base step. -/
theorem occurrence_sound (spend : GSLT.StepSpend system Grade)
    (occurrence : Occurrence spend) :
    system.Step occurrence.source occurrence.target :=
  spend.sound occurrence.graded

/-- A total grading provides at least one observed occurrence for every base
step. -/
theorem occurrence_nonempty_of_total
    (spend : GSLT.StepSpend system Grade) (total : spend.Total)
    {source target : system.Term} (step : system.Step source target) :
    Nonempty (OccurrenceAt spend source target) := by
  obtain ⟨grade, graded⟩ := total step
  exact ⟨⟨grade, graded⟩⟩

/-- Totality is exactly completeness of the rich graded-event presentation. -/
theorem presented_complete_of_total [Monoid Grade]
    (spend : GSLT.StepSpend system Grade) (total : spend.Total) :
    (presented spend).Complete := by
  intro step
  obtain ⟨grade, graded⟩ := total step.step
  refine ⟨⟨step.source, step.target, grade, graded⟩, ?_⟩
  cases step
  rfl

/-- A lifted step is exactly an observed graded occurrence plus the monoidal
accumulator update. -/
theorem spendLift_step_iff_occurrence [Monoid Grade]
    (spend : GSLT.StepSpend system Grade)
    {source target : system.Term × Grade} :
    (system.spendLift spend).Step source target ↔
      ∃ occurrence : OccurrenceAt spend source.1 target.1,
        target.2 = source.2 * occurrence.grade := by
  constructor
  · rintro ⟨grade, graded, accumulated⟩
    exact ⟨⟨grade, graded⟩, accumulated⟩
  · rintro ⟨occurrence, accumulated⟩
    exact ⟨occurrence.grade, occurrence.graded, accumulated⟩

/-- Erasing the occurrence from the preceding characterization recovers the
usual preservation theorem. -/
theorem spendLift_step_erases [Monoid Grade]
    (spend : GSLT.StepSpend system Grade)
    {source target : system.Term × Grade}
    (step : (system.spendLift spend).Step source target) :
    system.Step source.1 target.1 := by
  obtain ⟨occurrence, _⟩ :=
    (spendLift_step_iff_occurrence spend).mp step
  exact spend.sound occurrence.graded

/-! ## Negative control: a partial grading need not observe every step -/

/-- The empty grading of the always-stepping tick system. -/
def emptyTickSpend : GSLT.StepSpend GSLT.tickSystem Nat where
  graded := fun _ _ _ => False
  sound := False.elim
  resp_left := by
    intro source source' target grade equivalent impossible
    exact False.elim impossible
  resp_right := by
    intro source target target' grade impossible equivalent
    exact False.elim impossible

theorem tick_has_base_step : GSLT.tickSystem.Step () () :=
  trivial

/-- Base execution does not manufacture a grade: without totality there is no
observed occurrence and therefore no lifted step. -/
theorem empty_grading_does_not_reflect_tick :
    (¬ Nonempty (Occurrence emptyTickSpend)) ∧
      ¬ (GSLT.tickSystem.spendLift emptyTickSpend).Step ((), 1) ((), 1) := by
  constructor
  · rintro ⟨occurrence⟩
    exact occurrence.graded
  · rintro ⟨grade, graded, accumulated⟩
    exact graded

/-- The empty grading's presented observation is correspondingly incomplete. -/
theorem empty_grading_presentation_not_complete :
    ¬ (presented emptyTickSpend).Complete := by
  intro complete
  obtain ⟨⟨occurrence, erased⟩⟩ := complete
    ({ source := (), target := (), step := trivial } :
      GSLT.tickSystem.LabeledStep)
  exact occurrence.graded

end Mettapedia.GSLT.Dynamics.StepSpendObservation
